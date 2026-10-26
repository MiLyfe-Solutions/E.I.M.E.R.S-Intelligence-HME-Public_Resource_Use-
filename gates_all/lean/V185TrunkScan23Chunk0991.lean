import V185TrunkScan23Chunk0990

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5867172 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_5867172 : Nat := 118140960795 + 5867172 * 2 ^ 59
def prefixEnd_5867172 : Nat := 4983230072969 + 3 ^ 40 * 5867172 * 2
def baseEnd_5867172 : Nat := 1004226439533741298755791

theorem tailTrace_5867172 : CollatzResearch.WordTrace tailWord_5867172 prefixEnd_5867172 1004226439533741298755791 := by
  unfold tailWord_5867172
  simp only [CollatzResearch.WordTrace]
  refine ⟨106996671550122676023385885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142662228733496901364514513 106996671550122676023385885)
  ·
    refine ⟨40123751831296003508769707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106996671550122676023385885 40123751831296003508769707)
    ·
      refine ⟨60185627746944005263154561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40123751831296003508769707 60185627746944005263154561)
      ·
        refine ⟨45139220810208003947365921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60185627746944005263154561 45139220810208003947365921)
        ·
          refine ⟨33854415607656002960524441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45139220810208003947365921 33854415607656002960524441)
          ·
            refine ⟨25390811705742002220393331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33854415607656002960524441 25390811705742002220393331)
            ·
              refine ⟨38086217558613003330589997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25390811705742002220393331 38086217558613003330589997)
              ·
                refine ⟨14282331584479876248971249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38086217558613003330589997 14282331584479876248971249)
                ·
                  refine ⟨10711748688359907186728437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14282331584479876248971249 10711748688359907186728437)
                  ·
                    refine ⟨1004226439533741298755791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10711748688359907186728437 1004226439533741298755791)
                    ·
                      rfl

theorem cell23_5867172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_5867172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867172 prefixEnd_5867172 := by exact prefixLift 5867172
  have htrace : WordTrace (prefixWord ++ tailWord_5867172) baseStart_5867172 baseEnd_5867172 := by
    simpa [prefixWord, tailWord_5867172, baseEnd_5867172] using wordTrace_append hprefix tailTrace_5867172
  have hstable : (prefixWord ++ tailWord_5867172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867172).length < 2 ^ (prefixWord ++ tailWord_5867172).sum := by decide
  have hdescent : baseEnd_5867172 < baseStart_5867172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867192 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 6, 2]
def baseStart_5867192 : Nat := 118140960795 + 5867192 * 2 ^ 59
def prefixEnd_5867192 : Nat := 4983230072969 + 3 ^ 40 * 5867192 * 2
def baseEnd_5867192 : Nat := 3012689588214313818017281

theorem tailTrace_5867192 : CollatzResearch.WordTrace tailWord_5867192 prefixEnd_5867192 3012689588214313818017281 := by
  unfold tailWord_5867192
  simp only [CollatzResearch.WordTrace]
  refine ⟨106997036280086447731249915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142662715040115263641666553 106997036280086447731249915)
  ·
    refine ⟨160495554420129671596874873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106997036280086447731249915 160495554420129671596874873)
    ·
      refine ⟨120371665815097253697656155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160495554420129671596874873 120371665815097253697656155)
      ·
        refine ⟨180557498722645880546484233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120371665815097253697656155 180557498722645880546484233)
        ·
          refine ⟨135418124041984410409863175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180557498722645880546484233 135418124041984410409863175)
          ·
            refine ⟨203127186062976615614794763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135418124041984410409863175 203127186062976615614794763)
            ·
              refine ⟨304690779094464923422192145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203127186062976615614794763 304690779094464923422192145)
              ·
                refine ⟨228518084320848692566644109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304690779094464923422192145 228518084320848692566644109)
                ·
                  refine ⟨85694281620318259712491541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228518084320848692566644109 85694281620318259712491541)
                  ·
                    refine ⟨4016919450952418424023041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85694281620318259712491541 4016919450952418424023041)
                    ·
                      refine ⟨3012689588214313818017281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016919450952418424023041 3012689588214313818017281)
                      ·
                        rfl

theorem cell23_5867192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_5867192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867192 prefixEnd_5867192 := by exact prefixLift 5867192
  have htrace : WordTrace (prefixWord ++ tailWord_5867192) baseStart_5867192 baseEnd_5867192 := by
    simpa [prefixWord, tailWord_5867192, baseEnd_5867192] using wordTrace_append hprefix tailTrace_5867192
  have hstable : (prefixWord ++ tailWord_5867192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867192).length < 2 ^ (prefixWord ++ tailWord_5867192).sum := by decide
  have hdescent : baseEnd_5867192 < baseStart_5867192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867205 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_5867205 : Nat := 118140960795 + 5867205 * 2 ^ 59
def prefixEnd_5867205 : Nat := 4983230072969 + 3 ^ 40 * 5867205 * 2
def baseEnd_5867205 : Nat := 3012696263462822267154721

theorem tailTrace_5867205 : CollatzResearch.WordTrace tailWord_5867205 prefixEnd_5867205 3012696263462822267154721 := by
  unfold tailWord_5867205
  simp only [CollatzResearch.WordTrace]
  refine ⟨213994546709125798682723069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142663031139417199121815379 213994546709125798682723069)
  ·
    refine ⟨80247955015922174506021151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213994546709125798682723069 80247955015922174506021151)
    ·
      refine ⟨120371932523883261759031727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80247955015922174506021151 120371932523883261759031727)
      ·
        refine ⟨180557898785824892638547591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120371932523883261759031727 180557898785824892638547591)
        ·
          refine ⟨270836848178737338957821387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180557898785824892638547591 270836848178737338957821387)
          ·
            refine ⟨406255272268106008436732081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270836848178737338957821387 406255272268106008436732081)
            ·
              refine ⟨304691454201079506327549061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406255272268106008436732081 304691454201079506327549061)
              ·
                refine ⟨57129647662702407436415449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304691454201079506327549061 57129647662702407436415449)
                ·
                  refine ⟨42847235747026805577311587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57129647662702407436415449 42847235747026805577311587)
                  ·
                    refine ⟨64270853620540208365967381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42847235747026805577311587 64270853620540208365967381)
                    ·
                      refine ⟨3012696263462822267154721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64270853620540208365967381 3012696263462822267154721)
                      ·
                        rfl

theorem cell23_5867205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_5867205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867205 prefixEnd_5867205 := by exact prefixLift 5867205
  have htrace : WordTrace (prefixWord ++ tailWord_5867205) baseStart_5867205 baseEnd_5867205 := by
    simpa [prefixWord, tailWord_5867205, baseEnd_5867205] using wordTrace_append hprefix tailTrace_5867205
  have hstable : (prefixWord ++ tailWord_5867205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867205).length < 2 ^ (prefixWord ++ tailWord_5867205).sum := by decide
  have hdescent : baseEnd_5867205 < baseStart_5867205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867236 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_5867236 : Nat := 118140960795 + 5867236 * 2 ^ 59
def prefixEnd_5867236 : Nat := 4983230072969 + 3 ^ 40 * 5867236 * 2
def baseEnd_5867236 : Nat := 1004237393787703881955693

theorem tailTrace_5867236 : CollatzResearch.WordTrace tailWord_5867236 prefixEnd_5867236 1004237393787703881955693 := by
  unfold tailWord_5867236
  simp only [CollatzResearch.WordTrace]
  refine ⟨106997838686006745488550781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142663784914675660651401041 106997838686006745488550781)
  ·
    refine ⟨40124189507252529558206543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106997838686006745488550781 40124189507252529558206543)
    ·
      refine ⟨60186284260878794337309815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40124189507252529558206543 60186284260878794337309815)
      ·
        refine ⟨90279426391318191505964723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60186284260878794337309815 90279426391318191505964723)
        ·
          refine ⟨135419139586977287258947085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90279426391318191505964723 135419139586977287258947085)
          ·
            refine ⟨50782177345116482722105157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135419139586977287258947085 50782177345116482722105157)
            ·
              refine ⟨9521658252209340510394717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50782177345116482722105157 9521658252209340510394717)
              ·
                refine ⟨3570621844578502691398019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9521658252209340510394717 3570621844578502691398019)
                ·
                  refine ⟨5355932766867754037097029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570621844578502691398019 5355932766867754037097029)
                  ·
                    refine ⟨1004237393787703881955693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355932766867754037097029 1004237393787703881955693)
                    ·
                      rfl

theorem cell23_5867236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_5867236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867236 prefixEnd_5867236 := by exact prefixLift 5867236
  have htrace : WordTrace (prefixWord ++ tailWord_5867236) baseStart_5867236 baseEnd_5867236 := by
    simpa [prefixWord, tailWord_5867236, baseEnd_5867236] using wordTrace_append hprefix tailTrace_5867236
  have hstable : (prefixWord ++ tailWord_5867236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867236).length < 2 ^ (prefixWord ++ tailWord_5867236).sum := by decide
  have hdescent : baseEnd_5867236 < baseStart_5867236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867249 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 6]
def baseStart_5867249 : Nat := 118140960795 + 5867249 * 2 ^ 59
def prefixEnd_5867249 : Nat := 4983230072969 + 3 ^ 40 * 5867249 * 2
def baseEnd_5867249 : Nat := 334746539623513343889391

theorem tailTrace_5867249 : CollatzResearch.WordTrace tailWord_5867249 prefixEnd_5867249 334746539623513343889391 := by
  unfold tailWord_5867249
  simp only [CollatzResearch.WordTrace]
  refine ⟨213996151520966394197324801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142664101013977596131549867 213996151520966394197324801)
  ·
    refine ⟨160497113640724795647993601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213996151520966394197324801 160497113640724795647993601)
    ·
      refine ⟨120372835230543596735995201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160497113640724795647993601 120372835230543596735995201)
      ·
        refine ⟨90279626422907697551996401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120372835230543596735995201 90279626422907697551996401)
        ·
          refine ⟨67709719817180773163997301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90279626422907697551996401 67709719817180773163997301)
          ·
            refine ⟨6347786232860697484124747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67709719817180773163997301 6347786232860697484124747)
            ·
              refine ⟨9521679349291046226187121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347786232860697484124747 9521679349291046226187121)
              ·
                refine ⟨7141259511968284669640341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521679349291046226187121 7141259511968284669640341)
                ·
                  refine ⟨334746539623513343889391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7141259511968284669640341 334746539623513343889391)
                  ·
                    rfl

theorem cell23_5867249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 6].length) (baseStart_5867249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867249 prefixEnd_5867249 := by exact prefixLift 5867249
  have htrace : WordTrace (prefixWord ++ tailWord_5867249) baseStart_5867249 baseEnd_5867249 := by
    simpa [prefixWord, tailWord_5867249, baseEnd_5867249] using wordTrace_append hprefix tailTrace_5867249
  have hstable : (prefixWord ++ tailWord_5867249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867249).length < 2 ^ (prefixWord ++ tailWord_5867249).sum := by decide
  have hdescent : baseEnd_5867249 < baseStart_5867249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867266 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_5867266 : Nat := 118140960795 + 5867266 * 2 ^ 59
def prefixEnd_5867266 : Nat := 4983230072969 + 3 ^ 40 * 5867266 * 2
def baseEnd_5867266 : Nat := 334747509531416280943549

theorem tailTrace_5867266 : CollatzResearch.WordTrace tailWord_5867266 prefixEnd_5867266 334747509531416280943549 := by
  unfold tailWord_5867266
  simp only [CollatzResearch.WordTrace]
  refine ⟨53499192890476201525173413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142664514374603204067129101 53499192890476201525173413)
  ·
    refine ⟨10031098666964287785970015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53499192890476201525173413 10031098666964287785970015)
    ·
      refine ⟨15046648000446431678955023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10031098666964287785970015 15046648000446431678955023)
      ·
        refine ⟨22569972000669647518432535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15046648000446431678955023 22569972000669647518432535)
        ·
          refine ⟨33854958001004471277648803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22569972000669647518432535 33854958001004471277648803)
          ·
            refine ⟨50782437001506706916473205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33854958001004471277648803 50782437001506706916473205)
            ·
              refine ⟨4760853468891253773419363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50782437001506706916473205 4760853468891253773419363)
              ·
                refine ⟨7141280203336880660129045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760853468891253773419363 7141280203336880660129045)
                ·
                  refine ⟨334747509531416280943549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7141280203336880660129045 334747509531416280943549)
                  ·
                    rfl

theorem cell23_5867266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_5867266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867266 prefixEnd_5867266 := by exact prefixLift 5867266
  have htrace : WordTrace (prefixWord ++ tailWord_5867266) baseStart_5867266 baseEnd_5867266 := by
    simpa [prefixWord, tailWord_5867266, baseEnd_5867266] using wordTrace_append hprefix tailTrace_5867266
  have hstable : (prefixWord ++ tailWord_5867266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867266).length < 2 ^ (prefixWord ++ tailWord_5867266).sum := by decide
  have hdescent : baseEnd_5867266 < baseStart_5867266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867292 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5867292 : Nat := 118140960795 + 5867292 * 2 ^ 59
def prefixEnd_5867292 : Nat := 4983230072969 + 3 ^ 40 * 5867292 * 2
def baseEnd_5867292 : Nat := 1004246978759921142255607

theorem tailTrace_5867292 : CollatzResearch.WordTrace tailWord_5867292 prefixEnd_5867292 1004246978759921142255607 := by
  unfold tailWord_5867292
  simp only [CollatzResearch.WordTrace]
  refine ⟨106998859929905306270570065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142665146573207075027426753 106998859929905306270570065)
  ·
    refine ⟨80249144947428979702927549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106998859929905306270570065 80249144947428979702927549)
    ·
      refine ⟨30093429355285867388597831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80249144947428979702927549 30093429355285867388597831)
      ·
        refine ⟨45140144032928801082896747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30093429355285867388597831 45140144032928801082896747)
        ·
          refine ⟨67710216049393201624345121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45140144032928801082896747 67710216049393201624345121)
          ·
            refine ⟨50782662037044901218258841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67710216049393201624345121 50782662037044901218258841)
            ·
              refine ⟨38086996527783675913694131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50782662037044901218258841 38086996527783675913694131)
              ·
                refine ⟨57130494791675513870541197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38086996527783675913694131 57130494791675513870541197)
                ·
                  refine ⟨21423935546878317701452949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57130494791675513870541197 21423935546878317701452949)
                  ·
                    refine ⟨1004246978759921142255607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21423935546878317701452949 1004246978759921142255607)
                    ·
                      rfl

theorem cell23_5867292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5867292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867292 prefixEnd_5867292 := by exact prefixLift 5867292
  have htrace : WordTrace (prefixWord ++ tailWord_5867292) baseStart_5867292 baseEnd_5867292 := by
    simpa [prefixWord, tailWord_5867292, baseEnd_5867292] using wordTrace_append hprefix tailTrace_5867292
  have hstable : (prefixWord ++ tailWord_5867292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867292).length < 2 ^ (prefixWord ++ tailWord_5867292).sum := by decide
  have hdescent : baseEnd_5867292 < baseStart_5867292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867299 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 4]
def baseStart_5867299 : Nat := 118140960795 + 5867299 * 2 ^ 59
def prefixEnd_5867299 : Nat := 4983230072969 + 3 ^ 40 * 5867299 * 2
def baseEnd_5867299 : Nat := 3012744530644344899379289

theorem tailTrace_5867299 : CollatzResearch.WordTrace tailWord_5867299 prefixEnd_5867299 3012744530644344899379289 := by
  unfold tailWord_5867299
  simp only [CollatzResearch.WordTrace]
  refine ⟨213997975170785252736644951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142665316780523501824429967 213997975170785252736644951)
  ·
    refine ⟨320996962756177879104967427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213997975170785252736644951 320996962756177879104967427)
    ·
      refine ⟨481495444134266818657451141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320996962756177879104967427 481495444134266818657451141)
      ·
        refine ⟨90280395775175028498272089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 481495444134266818657451141 90280395775175028498272089)
        ·
          refine ⟨67710296831381271373704067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90280395775175028498272089 67710296831381271373704067)
          ·
            refine ⟨101565445247071907060556101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67710296831381271373704067 101565445247071907060556101)
            ·
              refine ⟨19043520983825982573854269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101565445247071907060556101 19043520983825982573854269)
              ·
                refine ⟨7141320368934743465195351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19043520983825982573854269 7141320368934743465195351)
                ·
                  refine ⟨10711980553402115197793027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141320368934743465195351 10711980553402115197793027)
                  ·
                    refine ⟨16067970830103172796689541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10711980553402115197793027 16067970830103172796689541)
                    ·
                      refine ⟨3012744530644344899379289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16067970830103172796689541 3012744530644344899379289)
                      ·
                        rfl

theorem cell23_5867299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_5867299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867299 prefixEnd_5867299 := by exact prefixLift 5867299
  have htrace : WordTrace (prefixWord ++ tailWord_5867299) baseStart_5867299 baseEnd_5867299 := by
    simpa [prefixWord, tailWord_5867299, baseEnd_5867299] using wordTrace_append hprefix tailTrace_5867299
  have hstable : (prefixWord ++ tailWord_5867299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867299).length < 2 ^ (prefixWord ++ tailWord_5867299).sum := by decide
  have hdescent : baseEnd_5867299 < baseStart_5867299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867310 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5867310 : Nat := 118140960795 + 5867310 * 2 ^ 59
def prefixEnd_5867310 : Nat := 4983230072969 + 3 ^ 40 * 5867310 * 2
def baseEnd_5867310 : Nat := 3012750178931544356341739

theorem tailTrace_5867310 : CollatzResearch.WordTrace tailWord_5867310 prefixEnd_5867310 3012750178931544356341739 := by
  unfold tailWord_5867310
  simp only [CollatzResearch.WordTrace]
  refine ⟨26749797046718175201911923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142665584249163601076863589 26749797046718175201911923)
  ·
    refine ⟨40124695570077262802867885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26749797046718175201911923 40124695570077262802867885)
    ·
      refine ⟨15046760838778973551075457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40124695570077262802867885 15046760838778973551075457)
      ·
        refine ⟨11285070629084230163306593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15046760838778973551075457 11285070629084230163306593)
        ·
          refine ⟨8463802971813172622479945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11285070629084230163306593 8463802971813172622479945)
          ·
            refine ⟨6347852228859879466859959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8463802971813172622479945 6347852228859879466859959)
            ·
              refine ⟨9521778343289819200289939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347852228859879466859959 9521778343289819200289939)
              ·
                refine ⟨14282667514934728800434909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9521778343289819200289939 14282667514934728800434909)
                ·
                  refine ⟨5356000318100523300163091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14282667514934728800434909 5356000318100523300163091)
                  ·
                    refine ⟨8034000477150784950244637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5356000318100523300163091 8034000477150784950244637)
                    ·
                      refine ⟨3012750178931544356341739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034000477150784950244637 3012750178931544356341739)
                      ·
                        rfl

theorem cell23_5867310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5867310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867310 prefixEnd_5867310 := by exact prefixLift 5867310
  have htrace : WordTrace (prefixWord ++ tailWord_5867310) baseStart_5867310 baseEnd_5867310 := by
    simpa [prefixWord, tailWord_5867310, baseEnd_5867310] using wordTrace_append hprefix tailTrace_5867310
  have hstable : (prefixWord ++ tailWord_5867310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867310).length < 2 ^ (prefixWord ++ tailWord_5867310).sum := by decide
  have hdescent : baseEnd_5867310 < baseStart_5867310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867322 : List Nat := [3, 1, 1, 1, 5, 1, 1, 10]
def baseStart_5867322 : Nat := 118140960795 + 5867322 * 2 ^ 59
def prefixEnd_5867322 : Nat := 4983230072969 + 3 ^ 40 * 5867322 * 2
def baseEnd_5867322 : Nat := 111583568174051789236729

theorem tailTrace_5867322 : CollatzResearch.WordTrace tailWord_5867322 prefixEnd_5867322 111583568174051789236729 := by
  unfold tailWord_5867322
  simp only [CollatzResearch.WordTrace]
  refine ⟨53499703512425481916183055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142665876033134618443154813 53499703512425481916183055)
  ·
    refine ⟨80249555268638222874274583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53499703512425481916183055 80249555268638222874274583)
    ·
      refine ⟨120374332902957334311411875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80249555268638222874274583 120374332902957334311411875)
      ·
        refine ⟨180561499354436001467117813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120374332902957334311411875 180561499354436001467117813)
        ·
          refine ⟨16927640564478375137542295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180561499354436001467117813 16927640564478375137542295)
          ·
            refine ⟨25391460846717562706313443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16927640564478375137542295 25391460846717562706313443)
            ·
              refine ⟨38087191270076344059470165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25391460846717562706313443 38087191270076344059470165)
              ·
                refine ⟨111583568174051789236729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38087191270076344059470165 111583568174051789236729)
                ·
                  rfl

theorem cell23_5867322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_5867322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867322 prefixEnd_5867322 := by exact prefixLift 5867322
  have htrace : WordTrace (prefixWord ++ tailWord_5867322) baseStart_5867322 baseEnd_5867322 := by
    simpa [prefixWord, tailWord_5867322, baseEnd_5867322] using wordTrace_append hprefix tailTrace_5867322
  have hstable : (prefixWord ++ tailWord_5867322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867322).length < 2 ^ (prefixWord ++ tailWord_5867322).sum := by decide
  have hdescent : baseEnd_5867322 < baseStart_5867322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867336 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_5867336 : Nat := 118140960795 + 5867336 * 2 ^ 59
def prefixEnd_5867336 : Nat := 4983230072969 + 3 ^ 40 * 5867336 * 2
def baseEnd_5867336 : Nat := 3012763529428561254616619

theorem tailTrace_5867336 : CollatzResearch.WordTrace tailWord_5867336 prefixEnd_5867336 3012763529428561254616619 := by
  unfold tailWord_5867336
  simp only [CollatzResearch.WordTrace]
  refine ⟨106999662335825604027870931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142666216447767472037161241 106999662335825604027870931)
  ·
    refine ⟨160499493503738406041806397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106999662335825604027870931 160499493503738406041806397)
    ·
      refine ⟨60187310063901902265677399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160499493503738406041806397 60187310063901902265677399)
      ·
        refine ⟨90280965095852853398516099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60187310063901902265677399 90280965095852853398516099)
        ·
          refine ⟨135421447643779280097774149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90280965095852853398516099 135421447643779280097774149)
          ·
            refine ⟨25391521433208615018332653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135421447643779280097774149 25391521433208615018332653)
            ·
              refine ⟨9521820537453230631874745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25391521433208615018332653 9521820537453230631874745)
              ·
                refine ⟨7141365403089922973906059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521820537453230631874745 7141365403089922973906059)
                ·
                  refine ⟨10712048104634884460859089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141365403089922973906059 10712048104634884460859089)
                  ·
                    refine ⟨8034036078476163345644317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10712048104634884460859089 8034036078476163345644317)
                    ·
                      refine ⟨3012763529428561254616619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034036078476163345644317 3012763529428561254616619)
                      ·
                        rfl

theorem cell23_5867336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_5867336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867336 prefixEnd_5867336 := by exact prefixLift 5867336
  have htrace : WordTrace (prefixWord ++ tailWord_5867336) baseStart_5867336 baseEnd_5867336 := by
    simpa [prefixWord, tailWord_5867336, baseEnd_5867336] using wordTrace_append hprefix tailTrace_5867336
  have hstable : (prefixWord ++ tailWord_5867336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867336).length < 2 ^ (prefixWord ++ tailWord_5867336).sum := by decide
  have hdescent : baseEnd_5867336 < baseStart_5867336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867349 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5867349 : Nat := 118140960795 + 5867349 * 2 ^ 59
def prefixEnd_5867349 : Nat := 4983230072969 + 3 ^ 40 * 5867349 * 2
def baseEnd_5867349 : Nat := 3012770204677069703754059

theorem tailTrace_5867349 : CollatzResearch.WordTrace tailWord_5867349 prefixEnd_5867349 3012770204677069703754059 := by
  unfold tailWord_5867349
  simp only [CollatzResearch.WordTrace]
  refine ⟨213999798820604111275965101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142666532547069407517310067 213999798820604111275965101)
  ·
    refine ⟨80249924557726541728486913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213999798820604111275965101 80249924557726541728486913)
    ·
      refine ⟨60187443418294906296365185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80249924557726541728486913 60187443418294906296365185)
      ·
        refine ⟨45140582563721179722273889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60187443418294906296365185 45140582563721179722273889)
        ·
          refine ⟨33855436922790884791705417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45140582563721179722273889 33855436922790884791705417)
          ·
            refine ⟨25391577692093163593779063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33855436922790884791705417 25391577692093163593779063)
            ·
              refine ⟨38087366538139745390668595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25391577692093163593779063 38087366538139745390668595)
              ·
                refine ⟨57131049807209618086002893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38087366538139745390668595 57131049807209618086002893)
                ·
                  refine ⟨21424143677703606782251085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57131049807209618086002893 21424143677703606782251085)
                  ·
                    refine ⟨8034053879138852543344157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21424143677703606782251085 8034053879138852543344157)
                    ·
                      refine ⟨3012770204677069703754059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034053879138852543344157 3012770204677069703754059)
                      ·
                        rfl

theorem cell23_5867349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5867349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867349 prefixEnd_5867349 := by exact prefixLift 5867349
  have htrace : WordTrace (prefixWord ++ tailWord_5867349) baseStart_5867349 baseEnd_5867349 := by
    simpa [prefixWord, tailWord_5867349, baseEnd_5867349] using wordTrace_append hprefix tailTrace_5867349
  have hstable : (prefixWord ++ tailWord_5867349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867349).length < 2 ^ (prefixWord ++ tailWord_5867349).sum := by decide
  have hdescent : baseEnd_5867349 < baseStart_5867349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867410 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5867410 : Nat := 118140960795 + 5867410 * 2 ^ 59
def prefixEnd_5867410 : Nat := 4983230072969 + 3 ^ 40 * 5867410 * 2
def baseEnd_5867410 : Nat := 3012801526996993965091279

theorem tailTrace_5867410 : CollatzResearch.WordTrace tailWord_5867410 prefixEnd_5867410 3012801526996993965091279 := by
  unfold tailWord_5867410
  simp only [CollatzResearch.WordTrace]
  refine ⟨53500505918345779673483921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142668015782255412462623789 53500505918345779673483921)
  ·
    refine ⟨40125379438759334755112941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53500505918345779673483921 40125379438759334755112941)
    ·
      refine ⟨15047017289534750533167353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40125379438759334755112941 15047017289534750533167353)
      ·
        refine ⟨11285262967151062899875515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15047017289534750533167353 11285262967151062899875515)
        ·
          refine ⟨16927894450726594349813273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11285262967151062899875515 16927894450726594349813273)
          ·
            refine ⟨12695920838044945762359955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16927894450726594349813273 12695920838044945762359955)
            ·
              refine ⟨19043881257067418643539933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12695920838044945762359955 19043881257067418643539933)
              ·
                refine ⟨7141455471400281991327475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19043881257067418643539933 7141455471400281991327475)
                ·
                  refine ⟨10712183207100422986991213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141455471400281991327475 10712183207100422986991213)
                  ·
                    refine ⟨4017068702662658620121705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10712183207100422986991213 4017068702662658620121705)
                    ·
                      refine ⟨3012801526996993965091279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017068702662658620121705 3012801526996993965091279)
                      ·
                        rfl

theorem cell23_5867410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5867410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867410 prefixEnd_5867410 := by exact prefixLift 5867410
  have htrace : WordTrace (prefixWord ++ tailWord_5867410) baseStart_5867410 baseEnd_5867410 := by
    simpa [prefixWord, tailWord_5867410, baseEnd_5867410] using wordTrace_append hprefix tailTrace_5867410
  have hstable : (prefixWord ++ tailWord_5867410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867410).length < 2 ^ (prefixWord ++ tailWord_5867410).sum := by decide
  have hdescent : baseEnd_5867410 < baseStart_5867410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867439 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_5867439 : Nat := 118140960795 + 5867439 * 2 ^ 59
def prefixEnd_5867439 : Nat := 4983230072969 + 3 ^ 40 * 5867439 * 2
def baseEnd_5867439 : Nat := 3012816417935974351628645

theorem tailTrace_5867439 : CollatzResearch.WordTrace tailWord_5867439 prefixEnd_5867439 3012816417935974351628645 := by
  unfold tailWord_5867439
  simp only [CollatzResearch.WordTrace]
  refine ⟨214003081390278056646741371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142668720926852037764494247 214003081390278056646741371)
  ·
    refine ⟨321004622085417084970112057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214003081390278056646741371 321004622085417084970112057)
    ·
      refine ⟨240753466564062813727584043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321004622085417084970112057 240753466564062813727584043)
      ·
        refine ⟨361130199846094220591376065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240753466564062813727584043 361130199846094220591376065)
        ·
          refine ⟨270847649884570665443532049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361130199846094220591376065 270847649884570665443532049)
          ·
            refine ⟨203135737413427999082649037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270847649884570665443532049 203135737413427999082649037)
            ·
              refine ⟨76175901530035499655993389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203135737413427999082649037 76175901530035499655993389)
              ·
                refine ⟨28565963073763312370997521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76175901530035499655993389 28565963073763312370997521)
                ·
                  refine ⟨21424472305322484278248141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28565963073763312370997521 21424472305322484278248141)
                  ·
                    refine ⟨8034177114495931604343053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21424472305322484278248141 8034177114495931604343053)
                    ·
                      refine ⟨3012816417935974351628645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034177114495931604343053 3012816417935974351628645)
                      ·
                        rfl

theorem cell23_5867439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_5867439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867439 prefixEnd_5867439 := by exact prefixLift 5867439
  have htrace : WordTrace (prefixWord ++ tailWord_5867439) baseStart_5867439 baseEnd_5867439 := by
    simpa [prefixWord, tailWord_5867439, baseEnd_5867439] using wordTrace_append hprefix tailTrace_5867439
  have hstable : (prefixWord ++ tailWord_5867439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867439).length < 2 ^ (prefixWord ++ tailWord_5867439).sum := by decide
  have hdescent : baseEnd_5867439 < baseStart_5867439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867476 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_5867476 : Nat := 118140960795 + 5867476 * 2 ^ 59
def prefixEnd_5867476 : Nat := 4983230072969 + 3 ^ 40 * 5867476 * 2
def baseEnd_5867476 : Nat := 1004278472240063568955325

theorem tailTrace_5867476 : CollatzResearch.WordTrace tailWord_5867476 prefixEnd_5867476 1004278472240063568955325 := by
  unfold tailWord_5867476
  simp only [CollatzResearch.WordTrace]
  refine ⟨107002215445572005982919141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142669620594096007977225521 107002215445572005982919141)
  ·
    refine ⟨20062915396044751121797339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107002215445572005982919141 20062915396044751121797339)
    ·
      refine ⟨30094373094067126682696009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20062915396044751121797339 30094373094067126682696009)
      ·
        refine ⟨22570779820550345012022007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30094373094067126682696009 22570779820550345012022007)
        ·
          refine ⟨33856169730825517518033011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22570779820550345012022007 33856169730825517518033011)
          ·
            refine ⟨50784254596238276277049517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33856169730825517518033011 50784254596238276277049517)
            ·
              refine ⟨19044095473589353603893569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50784254596238276277049517 19044095473589353603893569)
              ·
                refine ⟨14283071605192015202920177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19044095473589353603893569 14283071605192015202920177)
                ·
                  refine ⟨10712303703894011402190133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14283071605192015202920177 10712303703894011402190133)
                  ·
                    refine ⟨1004278472240063568955325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10712303703894011402190133 1004278472240063568955325)
                    ·
                      rfl

theorem cell23_5867476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_5867476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867476 prefixEnd_5867476 := by exact prefixLift 5867476
  have htrace : WordTrace (prefixWord ++ tailWord_5867476) baseStart_5867476 baseEnd_5867476 := by
    simpa [prefixWord, tailWord_5867476, baseEnd_5867476] using wordTrace_append hprefix tailTrace_5867476
  have hstable : (prefixWord ++ tailWord_5867476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867476).length < 2 ^ (prefixWord ++ tailWord_5867476).sum := by decide
  have hdescent : baseEnd_5867476 < baseStart_5867476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867496 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_5867496 : Nat := 118140960795 + 5867496 * 2 ^ 59
def prefixEnd_5867496 : Nat := 4983230072969 + 3 ^ 40 * 5867496 * 2
def baseEnd_5867496 : Nat := 3012845686333280628615883

theorem tailTrace_5867496 : CollatzResearch.WordTrace tailWord_5867496 prefixEnd_5867496 3012845686333280628615883 := by
  unfold tailWord_5867496
  simp only [CollatzResearch.WordTrace]
  refine ⟨107002580175535777690783171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142670106900714370254377561 107002580175535777690783171)
  ·
    refine ⟨160503870263303666536174757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107002580175535777690783171 160503870263303666536174757)
    ·
      refine ⟨30094475674369437475532767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160503870263303666536174757 30094475674369437475532767)
      ·
        refine ⟨45141713511554156213299151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30094475674369437475532767 45141713511554156213299151)
        ·
          refine ⟨67712570267331234319948727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45141713511554156213299151 67712570267331234319948727)
          ·
            refine ⟨101568855400996851479923091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67712570267331234319948727 101568855400996851479923091)
            ·
              refine ⟨152353283101495277219884637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101568855400996851479923091 152353283101495277219884637)
              ·
                refine ⟨57132481163060728957456739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152353283101495277219884637 57132481163060728957456739)
                ·
                  refine ⟨85698721744591093436185109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57132481163060728957456739 85698721744591093436185109)
                  ·
                    refine ⟨4017127581777707504821177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85698721744591093436185109 4017127581777707504821177)
                    ·
                      refine ⟨3012845686333280628615883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017127581777707504821177 3012845686333280628615883)
                      ·
                        rfl

theorem cell23_5867496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_5867496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867496 prefixEnd_5867496 := by exact prefixLift 5867496
  have htrace : WordTrace (prefixWord ++ tailWord_5867496) baseStart_5867496 baseEnd_5867496 := by
    simpa [prefixWord, tailWord_5867496, baseEnd_5867496] using wordTrace_append hprefix tailTrace_5867496
  have hstable : (prefixWord ++ tailWord_5867496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867496).length < 2 ^ (prefixWord ++ tailWord_5867496).sum := by decide
  have hdescent : baseEnd_5867496 < baseStart_5867496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867499 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 3]
def baseStart_5867499 : Nat := 118140960795 + 5867499 * 2 ^ 59
def prefixEnd_5867499 : Nat := 4983230072969 + 3 ^ 40 * 5867499 * 2
def baseEnd_5867499 : Nat := 3012847226775244116878369

theorem tailTrace_5867499 : CollatzResearch.WordTrace tailWord_5867499 prefixEnd_5867499 3012847226775244116878369 := by
  unfold tailWord_5867499
  simp only [CollatzResearch.WordTrace]
  refine ⟨214005269770060686893925551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142670179846707124595950367 214005269770060686893925551)
  ·
    refine ⟨321007904655091030340888327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214005269770060686893925551 321007904655091030340888327)
    ·
      refine ⟨481511856982636545511332491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321007904655091030340888327 481511856982636545511332491)
      ·
        refine ⟨722267785473954818266998737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481511856982636545511332491 722267785473954818266998737)
        ·
          refine ⟨541700839105466113700249053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722267785473954818266998737 541700839105466113700249053)
          ·
            refine ⟨203137814664549792637593395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541700839105466113700249053 203137814664549792637593395)
            ·
              refine ⟨304706721996824688956390093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203137814664549792637593395 304706721996824688956390093)
              ·
                refine ⟨114265020748809258358646285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304706721996824688956390093 114265020748809258358646285)
                ·
                  refine ⟨42849382780803471884492357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114265020748809258358646285 42849382780803471884492357)
                  ·
                    refine ⟨8034259271400650978342317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42849382780803471884492357 8034259271400650978342317)
                    ·
                      refine ⟨3012847226775244116878369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034259271400650978342317 3012847226775244116878369)
                      ·
                        rfl

theorem cell23_5867499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 3].length) (baseStart_5867499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867499 prefixEnd_5867499 := by exact prefixLift 5867499
  have htrace : WordTrace (prefixWord ++ tailWord_5867499) baseStart_5867499 baseEnd_5867499 := by
    simpa [prefixWord, tailWord_5867499, baseEnd_5867499] using wordTrace_append hprefix tailTrace_5867499
  have hstable : (prefixWord ++ tailWord_5867499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867499).length < 2 ^ (prefixWord ++ tailWord_5867499).sum := by decide
  have hdescent : baseEnd_5867499 < baseStart_5867499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867583 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 1, 5]
def baseStart_5867583 : Nat := 118140960795 + 5867583 * 2 ^ 59
def prefixEnd_5867583 : Nat := 4983230072969 + 3 ^ 40 * 5867583 * 2
def baseEnd_5867583 : Nat := 1004296786383407262742661

theorem tailTrace_5867583 : CollatzResearch.WordTrace tailWord_5867583 prefixEnd_5867583 1004296786383407262742661 := by
  unfold tailWord_5867583
  simp only [CollatzResearch.WordTrace]
  refine ⟨214008333501756369239983403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142672222334504246159988935 214008333501756369239983403)
  ·
    refine ⟨321012500252634553859975105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214008333501756369239983403 321012500252634553859975105)
    ·
      refine ⟨240759375189475915394981329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321012500252634553859975105 240759375189475915394981329)
      ·
        refine ⟨180569531392106936546235997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240759375189475915394981329 180569531392106936546235997)
        ·
          refine ⟨67713574272040101204838499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180569531392106936546235997 67713574272040101204838499)
          ·
            refine ⟨101570361408060151807257749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67713574272040101204838499 101570361408060151807257749)
            ·
              refine ⟨4761110691002819615965207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101570361408060151807257749 4761110691002819615965207)
              ·
                refine ⟨7141666036504229423947811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761110691002819615965207 7141666036504229423947811)
                ·
                  refine ⟨10712499054756344135921717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141666036504229423947811 10712499054756344135921717)
                  ·
                    refine ⟨1004296786383407262742661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10712499054756344135921717 1004296786383407262742661)
                    ·
                      rfl

theorem cell23_5867583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 5].length) (baseStart_5867583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867583 prefixEnd_5867583 := by exact prefixLift 5867583
  have htrace : WordTrace (prefixWord ++ tailWord_5867583) baseStart_5867583 baseEnd_5867583 := by
    simpa [prefixWord, tailWord_5867583, baseEnd_5867583] using wordTrace_append hprefix tailTrace_5867583
  have hstable : (prefixWord ++ tailWord_5867583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867583).length < 2 ^ (prefixWord ++ tailWord_5867583).sum := by decide
  have hdescent : baseEnd_5867583 < baseStart_5867583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867597 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_5867597 : Nat := 118140960795 + 5867597 * 2 ^ 59
def prefixEnd_5867597 : Nat := 4983230072969 + 3 ^ 40 * 5867597 * 2
def baseEnd_5867597 : Nat := 3012897547879384733452919

theorem tailTrace_5867597 : CollatzResearch.WordTrace tailWord_5867597 prefixEnd_5867597 3012897547879384733452919 := by
  unfold tailWord_5867597
  simp only [CollatzResearch.WordTrace]
  refine ⟨214008844123705649630993045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142672562749137099753995363 214008844123705649630993045)
  ·
    refine ⟨10031664568298702326452799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214008844123705649630993045 10031664568298702326452799)
    ·
      refine ⟨15047496852448053489679199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10031664568298702326452799 15047496852448053489679199)
      ·
        refine ⟨22571245278672080234518799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15047496852448053489679199 22571245278672080234518799)
        ·
          refine ⟨33856867918008120351778199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22571245278672080234518799 33856867918008120351778199)
          ·
            refine ⟨50785301877012180527667299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33856867918008120351778199 50785301877012180527667299)
            ·
              refine ⟨76177952815518270791500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50785301877012180527667299 76177952815518270791500949)
              ·
                refine ⟨3570841538227418943351607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76177952815518270791500949 3570841538227418943351607)
                ·
                  refine ⟨5356262307341128415027411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570841538227418943351607 5356262307341128415027411)
                  ·
                    refine ⟨8034393461011692622541117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5356262307341128415027411 8034393461011692622541117)
                    ·
                      refine ⟨3012897547879384733452919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034393461011692622541117 3012897547879384733452919)
                      ·
                        rfl

theorem cell23_5867597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_5867597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867597 prefixEnd_5867597 := by exact prefixLift 5867597
  have htrace : WordTrace (prefixWord ++ tailWord_5867597) baseStart_5867597 baseEnd_5867597 := by
    simpa [prefixWord, tailWord_5867597, baseEnd_5867597] using wordTrace_append hprefix tailTrace_5867597
  have hstable : (prefixWord ++ tailWord_5867597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867597).length < 2 ^ (prefixWord ++ tailWord_5867597).sum := by decide
  have hdescent : baseEnd_5867597 < baseStart_5867597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867599 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_5867599 : Nat := 118140960795 + 5867599 * 2 ^ 59
def prefixEnd_5867599 : Nat := 4983230072969 + 3 ^ 40 * 5867599 * 2
def baseEnd_5867599 : Nat := 3012898574840693725627909

theorem tailTrace_5867599 : CollatzResearch.WordTrace tailWord_5867599 prefixEnd_5867599 3012898574840693725627909 := by
  unfold tailWord_5867599
  simp only [CollatzResearch.WordTrace]
  refine ⟨214008917069698403972565851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142672611379798935981710567 214008917069698403972565851)
  ·
    refine ⟨321013375604547605958848777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214008917069698403972565851 321013375604547605958848777)
    ·
      refine ⟨240760031703410704469136583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321013375604547605958848777 240760031703410704469136583)
      ·
        refine ⟨361140047555116056703704875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240760031703410704469136583 361140047555116056703704875)
        ·
          refine ⟨541710071332674085055557313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361140047555116056703704875 541710071332674085055557313)
          ·
            refine ⟨406282553499505563791667985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541710071332674085055557313 406282553499505563791667985)
            ·
              refine ⟨304711915124629172843750989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406282553499505563791667985 304711915124629172843750989)
              ·
                refine ⟨114266968171735939816406621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304711915124629172843750989 114266968171735939816406621)
                ·
                  refine ⟨42850113064400977431152483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114266968171735939816406621 42850113064400977431152483)
                  ·
                    refine ⟨64275169596601466146728725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42850113064400977431152483 64275169596601466146728725)
                    ·
                      refine ⟨3012898574840693725627909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64275169596601466146728725 3012898574840693725627909)
                      ·
                        rfl

theorem cell23_5867599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_5867599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867599 prefixEnd_5867599 := by exact prefixLift 5867599
  have htrace : WordTrace (prefixWord ++ tailWord_5867599) baseStart_5867599 baseEnd_5867599 := by
    simpa [prefixWord, tailWord_5867599, baseEnd_5867599] using wordTrace_append hprefix tailTrace_5867599
  have hstable : (prefixWord ++ tailWord_5867599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867599).length < 2 ^ (prefixWord ++ tailWord_5867599).sum := by decide
  have hdescent : baseEnd_5867599 < baseStart_5867599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867609 : List Nat := [1, 2, 1, 2, 2, 1, 4, 10]
def baseStart_5867609 : Nat := 118140960795 + 5867609 * 2 ^ 59
def prefixEnd_5867609 : Nat := 4983230072969 + 3 ^ 40 * 5867609 * 2
def baseEnd_5867609 : Nat := 111589026283231062463069

theorem tailTrace_5867609 : CollatzResearch.WordTrace tailWord_5867609 prefixEnd_5867609 111589026283231062463069 := by
  unfold tailWord_5867609
  simp only [CollatzResearch.WordTrace]
  refine ⟨214009281799662175680429881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142672854533108117120286587 214009281799662175680429881)
  ·
    refine ⟨160506961349746631760322411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214009281799662175680429881 160506961349746631760322411)
    ·
      refine ⟨240760442024619947640483617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160506961349746631760322411 240760442024619947640483617)
      ·
        refine ⟨180570331518464960730362713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240760442024619947640483617 180570331518464960730362713)
        ·
          refine ⟨135427748638848720547772035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180570331518464960730362713 135427748638848720547772035)
          ·
            refine ⟨203141622958273080821658053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135427748638848720547772035 203141622958273080821658053)
            ·
              refine ⟨38089054304676202654060885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203141622958273080821658053 38089054304676202654060885)
              ·
                refine ⟨111589026283231062463069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38089054304676202654060885 111589026283231062463069)
                ·
                  rfl

theorem cell23_5867609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 10].length) (baseStart_5867609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867609 prefixEnd_5867609 := by exact prefixLift 5867609
  have htrace : WordTrace (prefixWord ++ tailWord_5867609) baseStart_5867609 baseEnd_5867609 := by
    simpa [prefixWord, tailWord_5867609, baseEnd_5867609] using wordTrace_append hprefix tailTrace_5867609
  have hstable : (prefixWord ++ tailWord_5867609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867609).length < 2 ^ (prefixWord ++ tailWord_5867609).sum := by decide
  have hdescent : baseEnd_5867609 < baseStart_5867609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867616 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_5867616 : Nat := 118140960795 + 5867616 * 2 ^ 59
def prefixEnd_5867616 : Nat := 4983230072969 + 3 ^ 40 * 5867616 * 2
def baseEnd_5867616 : Nat := 3012907304011820159115331

theorem tailTrace_5867616 : CollatzResearch.WordTrace tailWord_5867616 prefixEnd_5867616 3012907304011820159115331 := by
  unfold tailWord_5867616
  simp only [CollatzResearch.WordTrace]
  refine ⟨107004768555318407937967351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142673024740424543917289801 107004768555318407937967351)
  ·
    refine ⟨160507152832977611906951027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107004768555318407937967351 160507152832977611906951027)
    ·
      refine ⟨240760729249466417860426541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160507152832977611906951027 240760729249466417860426541)
      ·
        refine ⟨90285273468549906697659953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240760729249466417860426541 90285273468549906697659953)
        ·
          refine ⟨67713955101412430023244965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90285273468549906697659953 67713955101412430023244965)
          ·
            refine ⟨12696366581514830629358431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67713955101412430023244965 12696366581514830629358431)
            ·
              refine ⟨19044549872272245944037647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12696366581514830629358431 19044549872272245944037647)
              ·
                refine ⟨28566824808408368916056471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19044549872272245944037647 28566824808408368916056471)
                ·
                  refine ⟨42850237212612553374084707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28566824808408368916056471 42850237212612553374084707)
                  ·
                    refine ⟨64275355818918830061127061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42850237212612553374084707 64275355818918830061127061)
                    ·
                      refine ⟨3012907304011820159115331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64275355818918830061127061 3012907304011820159115331)
                      ·
                        rfl

theorem cell23_5867616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_5867616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867616 prefixEnd_5867616 := by exact prefixLift 5867616
  have htrace : WordTrace (prefixWord ++ tailWord_5867616) baseStart_5867616 baseEnd_5867616 := by
    simpa [prefixWord, tailWord_5867616, baseEnd_5867616] using wordTrace_append hprefix tailTrace_5867616
  have hstable : (prefixWord ++ tailWord_5867616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867616).length < 2 ^ (prefixWord ++ tailWord_5867616).sum := by decide
  have hdescent : baseEnd_5867616 < baseStart_5867616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867620 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_5867620 : Nat := 118140960795 + 5867620 * 2 ^ 59
def prefixEnd_5867620 : Nat := 4983230072969 + 3 ^ 40 * 5867620 * 2
def baseEnd_5867620 : Nat := 3012909357934438143465313

theorem tailTrace_5867620 : CollatzResearch.WordTrace tailWord_5867620 prefixEnd_5867620 3012909357934438143465313 := by
  unfold tailWord_5867620
  simp only [CollatzResearch.WordTrace]
  refine ⟨107004841501311162279540157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142673122001748216372720209 107004841501311162279540157)
  ·
    refine ⟨40126815562991685854827559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107004841501311162279540157 40126815562991685854827559)
    ·
      refine ⟨60190223344487528782241339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40126815562991685854827559 60190223344487528782241339)
      ·
        refine ⟨90285335016731293173362009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60190223344487528782241339 90285335016731293173362009)
        ·
          refine ⟨67714001262548469880021507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90285335016731293173362009 67714001262548469880021507)
          ·
            refine ⟨101571001893822704820032261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67714001262548469880021507 101571001893822704820032261)
            ·
              refine ⟨19044562855091757153756049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101571001893822704820032261 19044562855091757153756049)
              ·
                refine ⟨14283422141318817865317037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19044562855091757153756049 14283422141318817865317037)
                ·
                  refine ⟨5356283302994556699493889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14283422141318817865317037 5356283302994556699493889)
                  ·
                    refine ⟨4017212477245917524620417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5356283302994556699493889 4017212477245917524620417)
                    ·
                      refine ⟨3012909357934438143465313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017212477245917524620417 3012909357934438143465313)
                      ·
                        rfl

theorem cell23_5867620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_5867620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867620 prefixEnd_5867620 := by exact prefixLift 5867620
  have htrace : WordTrace (prefixWord ++ tailWord_5867620) baseStart_5867620 baseEnd_5867620 := by
    simpa [prefixWord, tailWord_5867620, baseEnd_5867620] using wordTrace_append hprefix tailTrace_5867620
  have hstable : (prefixWord ++ tailWord_5867620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867620).length < 2 ^ (prefixWord ++ tailWord_5867620).sum := by decide
  have hdescent : baseEnd_5867620 < baseStart_5867620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867674 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5867674 : Nat := 118140960795 + 5867674 * 2 ^ 59
def prefixEnd_5867674 : Nat := 4983230072969 + 3 ^ 40 * 5867674 * 2
def baseEnd_5867674 : Nat := 3012937085889780932190065

theorem tailTrace_5867674 : CollatzResearch.WordTrace tailWord_5867674 prefixEnd_5867674 3012937085889780932190065 := by
  unfold tailWord_5867674
  simp only [CollatzResearch.WordTrace]
  refine ⟨53502913136106672945386519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142674435029617794521030717 53502913136106672945386519)
  ·
    refine ⟨80254369704160009418079779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53502913136106672945386519 80254369704160009418079779)
    ·
      refine ⟨120381554556240014127119669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80254369704160009418079779 120381554556240014127119669)
      ·
        refine ⟨11285770739647501324417469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120381554556240014127119669 11285770739647501324417469)
        ·
          refine ⟨4232164027367812996656551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11285770739647501324417469 4232164027367812996656551)
          ·
            refine ⟨6348246041051719494984827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232164027367812996656551 6348246041051719494984827)
            ·
              refine ⟨9522369061577579242477241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348246041051719494984827 9522369061577579242477241)
              ·
                refine ⟨7141776796183184431857931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9522369061577579242477241 7141776796183184431857931)
                ·
                  refine ⟨10712665194274776647786897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141776796183184431857931 10712665194274776647786897)
                  ·
                    refine ⟨8034498895706082485840173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10712665194274776647786897 8034498895706082485840173)
                    ·
                      refine ⟨3012937085889780932190065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034498895706082485840173 3012937085889780932190065)
                      ·
                        rfl

theorem cell23_5867674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5867674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867674 prefixEnd_5867674 := by exact prefixLift 5867674
  have htrace : WordTrace (prefixWord ++ tailWord_5867674) baseStart_5867674 baseEnd_5867674 := by
    simpa [prefixWord, tailWord_5867674, baseEnd_5867674] using wordTrace_append hprefix tailTrace_5867674
  have hstable : (prefixWord ++ tailWord_5867674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867674).length < 2 ^ (prefixWord ++ tailWord_5867674).sum := by decide
  have hdescent : baseEnd_5867674 < baseStart_5867674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867680 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 3, 3, 2]
def baseStart_5867680 : Nat := 118140960795 + 5867680 * 2 ^ 59
def prefixEnd_5867680 : Nat := 4983230072969 + 3 ^ 40 * 5867680 * 2
def baseEnd_5867680 : Nat := 3012940166773707908715037

theorem tailTrace_5867680 : CollatzResearch.WordTrace tailWord_5867680 prefixEnd_5867680 3012940166773707908715037 := by
  unfold tailWord_5867680
  simp only [CollatzResearch.WordTrace]
  refine ⟨107005935691202477403132247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142674580921603303204176329 107005935691202477403132247)
  ·
    refine ⟨160508903536803716104698371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107005935691202477403132247 160508903536803716104698371)
    ·
      refine ⟨240763355305205574157047557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160508903536803716104698371 240763355305205574157047557)
      ·
        refine ⟨45143129119726045154446417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240763355305205574157047557 45143129119726045154446417)
        ·
          refine ⟨33857346839794533865834813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45143129119726045154446417 33857346839794533865834813)
          ·
            refine ⟨12696505064922950199688055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33857346839794533865834813 12696505064922950199688055)
            ·
              refine ⟨19044757597384425299532083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12696505064922950199688055 19044757597384425299532083)
              ·
                refine ⟨28567136396076637949298125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19044757597384425299532083 28567136396076637949298125)
                ·
                  refine ⟨10712676148528739230986797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28567136396076637949298125 10712676148528739230986797)
                  ·
                    refine ⟨4017253555698277211620049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10712676148528739230986797 4017253555698277211620049)
                    ·
                      refine ⟨3012940166773707908715037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017253555698277211620049 3012940166773707908715037)
                      ·
                        rfl

theorem cell23_5867680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_5867680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867680 prefixEnd_5867680 := by exact prefixLift 5867680
  have htrace : WordTrace (prefixWord ++ tailWord_5867680) baseStart_5867680 baseEnd_5867680 := by
    simpa [prefixWord, tailWord_5867680, baseEnd_5867680] using wordTrace_append hprefix tailTrace_5867680
  have hstable : (prefixWord ++ tailWord_5867680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867680).length < 2 ^ (prefixWord ++ tailWord_5867680).sum := by decide
  have hdescent : baseEnd_5867680 < baseStart_5867680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867696 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_5867696 : Nat := 118140960795 + 5867696 * 2 ^ 59
def prefixEnd_5867696 : Nat := 4983230072969 + 3 ^ 40 * 5867696 * 2
def baseEnd_5867696 : Nat := 3012948382464179846114963

theorem tailTrace_5867696 : CollatzResearch.WordTrace tailWord_5867696 prefixEnd_5867696 3012948382464179846114963 := by
  unfold tailWord_5867696
  simp only [CollatzResearch.WordTrace]
  refine ⟨107006227475173494769423471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142674969966897993025897961 107006227475173494769423471)
  ·
    refine ⟨160509341212760242154135207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107006227475173494769423471 160509341212760242154135207)
    ·
      refine ⟨240764011819140363231202811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160509341212760242154135207 240764011819140363231202811)
      ·
        refine ⟨361146017728710544846804217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240764011819140363231202811 361146017728710544846804217)
        ·
          refine ⟨270859513296532908635103163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361146017728710544846804217 270859513296532908635103163)
          ·
            refine ⟨406289269944799362952654745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270859513296532908635103163 406289269944799362952654745)
            ·
              refine ⟨304716952458599522214491059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406289269944799362952654745 304716952458599522214491059)
              ·
                refine ⟨457075428687899283321736589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304716952458599522214491059 457075428687899283321736589)
                ·
                  refine ⟨171403285757962231245651221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457075428687899283321736589 171403285757962231245651221)
                  ·
                    refine ⟨8034529019904479589639901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 171403285757962231245651221 8034529019904479589639901)
                    ·
                      refine ⟨3012948382464179846114963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034529019904479589639901 3012948382464179846114963)
                      ·
                        rfl

theorem cell23_5867696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_5867696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867696 prefixEnd_5867696 := by exact prefixLift 5867696
  have htrace : WordTrace (prefixWord ++ tailWord_5867696) baseStart_5867696 baseEnd_5867696 := by
    simpa [prefixWord, tailWord_5867696, baseEnd_5867696] using wordTrace_append hprefix tailTrace_5867696
  have hstable : (prefixWord ++ tailWord_5867696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867696).length < 2 ^ (prefixWord ++ tailWord_5867696).sum := by decide
  have hdescent : baseEnd_5867696 < baseStart_5867696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867714 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_5867714 : Nat := 118140960795 + 5867714 * 2 ^ 59
def prefixEnd_5867714 : Nat := 4983230072969 + 3 ^ 40 * 5867714 * 2
def baseEnd_5867714 : Nat := 3012957625115960775689881

theorem tailTrace_5867714 : CollatzResearch.WordTrace tailWord_5867714 prefixEnd_5867714 3012957625115960775689881 := by
  unfold tailWord_5867714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53503277866070444653250549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142675407642854519075334797 53503277866070444653250549)
  ·
    refine ⟨5015932299944104186242239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53503277866070444653250549 5015932299944104186242239)
    ·
      refine ⟨7523898449916156279363359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015932299944104186242239 7523898449916156279363359)
      ·
        refine ⟨11285847674874234419045039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523898449916156279363359 11285847674874234419045039)
        ·
          refine ⟨16928771512311351628567559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11285847674874234419045039 16928771512311351628567559)
          ·
            refine ⟨25393157268467027442851339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16928771512311351628567559 25393157268467027442851339)
            ·
              refine ⟨38089735902700541164277009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25393157268467027442851339 38089735902700541164277009)
              ·
                refine ⟨28567301927025405873207757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38089735902700541164277009 28567301927025405873207757)
                ·
                  refine ⟨10712738222634527202452909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28567301927025405873207757 10712738222634527202452909)
                  ·
                    refine ⟨4017276833487947700919841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10712738222634527202452909 4017276833487947700919841)
                    ·
                      refine ⟨3012957625115960775689881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017276833487947700919841 3012957625115960775689881)
                      ·
                        rfl

theorem cell23_5867714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_5867714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867714 prefixEnd_5867714 := by exact prefixLift 5867714
  have htrace : WordTrace (prefixWord ++ tailWord_5867714) baseStart_5867714 baseEnd_5867714 := by
    simpa [prefixWord, tailWord_5867714, baseEnd_5867714] using wordTrace_append hprefix tailTrace_5867714
  have hstable : (prefixWord ++ tailWord_5867714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867714).length < 2 ^ (prefixWord ++ tailWord_5867714).sum := by decide
  have hdescent : baseEnd_5867714 < baseStart_5867714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867753 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 4, 5, 2]
def baseStart_5867753 : Nat := 118140960795 + 5867753 * 2 ^ 59
def prefixEnd_5867753 : Nat := 4983230072969 + 3 ^ 40 * 5867753 * 2
def baseEnd_5867753 : Nat := 3012977650861486123102201

theorem tailTrace_5867753 : CollatzResearch.WordTrace tailWord_5867753 prefixEnd_5867753 3012977650861486123102201 := by
  unfold tailWord_5867753
  simp only [CollatzResearch.WordTrace]
  refine ⟨214014533911140488273671913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142676355940760325515781275 214014533911140488273671913)
  ·
    refine ⟨160510900433355366205253935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214014533911140488273671913 160510900433355366205253935)
    ·
      refine ⟨240766350650033049307880903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160510900433355366205253935 240766350650033049307880903)
      ·
        refine ⟨361149525975049573961821355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240766350650033049307880903 361149525975049573961821355)
        ·
          refine ⟨541724288962574360942732033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361149525975049573961821355 541724288962574360942732033)
          ·
            refine ⟨406293216721930770707049025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541724288962574360942732033 406293216721930770707049025)
            ·
              refine ⟨304719912541448078030286769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406293216721930770707049025 304719912541448078030286769)
              ·
                refine ⟨228539934406086058522715077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304719912541448078030286769 228539934406086058522715077)
                ·
                  refine ⟨42851237701141135973009077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228539934406086058522715077 42851237701141135973009077)
                  ·
                    refine ⟨4017303534481981497469601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42851237701141135973009077 4017303534481981497469601)
                    ·
                      refine ⟨3012977650861486123102201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017303534481981497469601 3012977650861486123102201)
                      ·
                        rfl

theorem cell23_5867753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 5, 2].length) (baseStart_5867753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867753 prefixEnd_5867753 := by exact prefixLift 5867753
  have htrace : WordTrace (prefixWord ++ tailWord_5867753) baseStart_5867753 baseEnd_5867753 := by
    simpa [prefixWord, tailWord_5867753, baseEnd_5867753] using wordTrace_append hprefix tailTrace_5867753
  have hstable : (prefixWord ++ tailWord_5867753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867753).length < 2 ^ (prefixWord ++ tailWord_5867753).sum := by decide
  have hdescent : baseEnd_5867753 < baseStart_5867753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867803 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 3]
def baseStart_5867803 : Nat := 118140960795 + 5867803 * 2 ^ 59
def prefixEnd_5867803 : Nat := 4983230072969 + 3 ^ 40 * 5867803 * 2
def baseEnd_5867803 : Nat := 3013003324894210927476971

theorem tailTrace_5867803 : CollatzResearch.WordTrace tailWord_5867803 prefixEnd_5867803 3013003324894210927476971 := by
  unfold tailWord_5867803
  simp only [CollatzResearch.WordTrace]
  refine ⟨214016357560959346812992063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142677571707306231208661375 214016357560959346812992063)
  ·
    refine ⟨321024536341439020219488095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214016357560959346812992063 321024536341439020219488095)
    ·
      refine ⟨481536804512158530329232143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321024536341439020219488095 481536804512158530329232143)
      ·
        refine ⟨722305206768237795493848215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481536804512158530329232143 722305206768237795493848215)
        ·
          refine ⟨1083457810152356693240772323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722305206768237795493848215 1083457810152356693240772323)
          ·
            refine ⟨1625186715228535039861158485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083457810152356693240772323 1625186715228535039861158485)
            ·
              refine ⟨19045156819084394998372951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1625186715228535039861158485 19045156819084394998372951)
              ·
                refine ⟨28567735228626592497559427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19045156819084394998372951 28567735228626592497559427)
                ·
                  refine ⟨42851602842939888746339141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28567735228626592497559427 42851602842939888746339141)
                  ·
                    refine ⟨8034675533051229139938589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42851602842939888746339141 8034675533051229139938589)
                    ·
                      refine ⟨3013003324894210927476971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034675533051229139938589 3013003324894210927476971)
                      ·
                        rfl

theorem cell23_5867803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 3].length) (baseStart_5867803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867803 prefixEnd_5867803 := by exact prefixLift 5867803
  have htrace : WordTrace (prefixWord ++ tailWord_5867803) baseStart_5867803 baseEnd_5867803 := by
    simpa [prefixWord, tailWord_5867803, baseEnd_5867803] using wordTrace_append hprefix tailTrace_5867803
  have hstable : (prefixWord ++ tailWord_5867803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867803).length < 2 ^ (prefixWord ++ tailWord_5867803).sum := by decide
  have hdescent : baseEnd_5867803 < baseStart_5867803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867877 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 2, 3, 2]
def baseStart_5867877 : Nat := 118140960795 + 5867877 * 2 ^ 59
def prefixEnd_5867877 : Nat := 4983230072969 + 3 ^ 40 * 5867877 * 2
def baseEnd_5867877 : Nat := 3013041322462643637951631

theorem tailTrace_5867877 : CollatzResearch.WordTrace tailWord_5867877 prefixEnd_5867877 3013041322462643637951631 := by
  unfold tailWord_5867877
  simp only [CollatzResearch.WordTrace]
  refine ⟨214019056562691257451185885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142679371041794171634123923 214019056562691257451185885)
  ·
    refine ⟨80257146211009221544194707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214019056562691257451185885 80257146211009221544194707)
    ·
      refine ⟨120385719316513832316292061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80257146211009221544194707 120385719316513832316292061)
      ·
        refine ⟨45144644743692687118609523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120385719316513832316292061 45144644743692687118609523)
        ·
          refine ⟨67716967115539030677914285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45144644743692687118609523 67716967115539030677914285)
          ·
            refine ⟨25393862668327136504217857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67716967115539030677914285 25393862668327136504217857)
            ·
              refine ⟨19045397001245352378163393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25393862668327136504217857 19045397001245352378163393)
              ·
                refine ⟨14284047750934014283622545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19045397001245352378163393 14284047750934014283622545)
                ·
                  refine ⟨10713035813200510712716909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14284047750934014283622545 10713035813200510712716909)
                  ·
                    refine ⟨4017388429950191517268841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10713035813200510712716909 4017388429950191517268841)
                    ·
                      refine ⟨3013041322462643637951631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017388429950191517268841 3013041322462643637951631)
                      ·
                        rfl

theorem cell23_5867877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_5867877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867877 prefixEnd_5867877 := by exact prefixLift 5867877
  have htrace : WordTrace (prefixWord ++ tailWord_5867877) baseStart_5867877 baseEnd_5867877 := by
    simpa [prefixWord, tailWord_5867877, baseEnd_5867877] using wordTrace_append hprefix tailTrace_5867877
  have hstable : (prefixWord ++ tailWord_5867877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867877).length < 2 ^ (prefixWord ++ tailWord_5867877).sum := by decide
  have hdescent : baseEnd_5867877 < baseStart_5867877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867890 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_5867890 : Nat := 118140960795 + 5867890 * 2 ^ 59
def prefixEnd_5867890 : Nat := 4983230072969 + 3 ^ 40 * 5867890 * 2
def baseEnd_5867890 : Nat := 3013047997711152087089071

theorem tailTrace_5867890 : CollatzResearch.WordTrace tailWord_5867890 prefixEnd_5867890 3013047997711152087089071 := by
  unfold tailWord_5867890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53504882677911040167852281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142679687141096107114272749 53504882677911040167852281)
  ·
    refine ⟨40128662008433280125889211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53504882677911040167852281 40128662008433280125889211)
    ·
      refine ⟨60192993012649920188833817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40128662008433280125889211 60192993012649920188833817)
      ·
        refine ⟨45144744759487440141625363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60192993012649920188833817 45144744759487440141625363)
        ·
          refine ⟨67717117139231160212438045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45144744759487440141625363 67717117139231160212438045)
          ·
            refine ⟨25393918927211685079664267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67717117139231160212438045 25393918927211685079664267)
            ·
              refine ⟨38090878390817527619496401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25393918927211685079664267 38090878390817527619496401)
              ·
                refine ⟨28568158793113145714622301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38090878390817527619496401 28568158793113145714622301)
                ·
                  refine ⟨10713059547417429642983363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28568158793113145714622301 10713059547417429642983363)
                  ·
                    refine ⟨16069589321126144464475045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10713059547417429642983363 16069589321126144464475045)
                    ·
                      refine ⟨3013047997711152087089071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16069589321126144464475045 3013047997711152087089071)
                      ·
                        rfl

theorem cell23_5867890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_5867890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867890 prefixEnd_5867890 := by exact prefixLift 5867890
  have htrace : WordTrace (prefixWord ++ tailWord_5867890) baseStart_5867890 baseEnd_5867890 := by
    simpa [prefixWord, tailWord_5867890, baseEnd_5867890] using wordTrace_append hprefix tailTrace_5867890
  have hstable : (prefixWord ++ tailWord_5867890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867890).length < 2 ^ (prefixWord ++ tailWord_5867890).sum := by decide
  have hdescent : baseEnd_5867890 < baseStart_5867890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867903 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_5867903 : Nat := 118140960795 + 5867903 * 2 ^ 59
def prefixEnd_5867903 : Nat := 4983230072969 + 3 ^ 40 * 5867903 * 2
def baseEnd_5867903 : Nat := 3013054672959660536226511

theorem tailTrace_5867903 : CollatzResearch.WordTrace tailWord_5867903 prefixEnd_5867903 3013054672959660536226511 := by
  unfold tailWord_5867903
  simp only [CollatzResearch.WordTrace]
  refine ⟨214020004860597063891632363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142680003240398042594421575 214020004860597063891632363)
  ·
    refine ⟨321030007290895595837448545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214020004860597063891632363 321030007290895595837448545)
    ·
      refine ⟨240772505468171696878086409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321030007290895595837448545 240772505468171696878086409)
      ·
        refine ⟨180579379101128772658564807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240772505468171696878086409 180579379101128772658564807)
        ·
          refine ⟨270869068651693158987847211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180579379101128772658564807 270869068651693158987847211)
          ·
            refine ⟨406303602977539738481770817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270869068651693158987847211 406303602977539738481770817)
            ·
              refine ⟨304727702233154803861328113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406303602977539738481770817 304727702233154803861328113)
              ·
                refine ⟨228545776674866102895996085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304727702233154803861328113 228545776674866102895996085)
                ·
                  refine ⟨21426166563268697146499633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228545776674866102895996085 21426166563268697146499633)
                  ·
                    refine ⟨16069624922451522859874725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21426166563268697146499633 16069624922451522859874725)
                    ·
                      refine ⟨3013054672959660536226511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16069624922451522859874725 3013054672959660536226511)
                      ·
                        rfl

theorem cell23_5867903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_5867903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867903 prefixEnd_5867903 := by exact prefixLift 5867903
  have htrace : WordTrace (prefixWord ++ tailWord_5867903) baseStart_5867903 baseEnd_5867903 := by
    simpa [prefixWord, tailWord_5867903, baseEnd_5867903] using wordTrace_append hprefix tailTrace_5867903
  have hstable : (prefixWord ++ tailWord_5867903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867903).length < 2 ^ (prefixWord ++ tailWord_5867903).sum := by decide
  have hdescent : baseEnd_5867903 < baseStart_5867903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867924 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_5867924 : Nat := 118140960795 + 5867924 * 2 ^ 59
def prefixEnd_5867924 : Nat := 4983230072969 + 3 ^ 40 * 5867924 * 2
def baseEnd_5867924 : Nat := 3013065456053404954063915

theorem tailTrace_5867924 : CollatzResearch.WordTrace tailWord_5867924 prefixEnd_5867924 3013065456053404954063915 := by
  unfold tailWord_5867924
  simp only [CollatzResearch.WordTrace]
  refine ⟨107010385396760492239073413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142680513862347322985431217 107010385396760492239073413)
  ·
    refine ⟨20064447261892592294826265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107010385396760492239073413 20064447261892592294826265)
    ·
      refine ⟨15048335446419444221119699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20064447261892592294826265 15048335446419444221119699)
      ·
        refine ⟨22572503169629166331679549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15048335446419444221119699 22572503169629166331679549)
        ·
          refine ⟨8464688688610937374379831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22572503169629166331679549 8464688688610937374379831)
          ·
            refine ⟨12697033032916406061569747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464688688610937374379831 12697033032916406061569747)
            ·
              refine ⟨19045549549374609092354621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697033032916406061569747 19045549549374609092354621)
              ·
                refine ⟨7142081081015478409632983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19045549549374609092354621 7142081081015478409632983)
                ·
                  refine ⟨10713121621523217614449475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7142081081015478409632983 10713121621523217614449475)
                  ·
                    refine ⟨16069682432284826421674213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10713121621523217614449475 16069682432284826421674213)
                    ·
                      refine ⟨3013065456053404954063915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16069682432284826421674213 3013065456053404954063915)
                      ·
                        rfl

theorem cell23_5867924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_5867924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867924 prefixEnd_5867924 := by exact prefixLift 5867924
  have htrace : WordTrace (prefixWord ++ tailWord_5867924) baseStart_5867924 baseEnd_5867924 := by
    simpa [prefixWord, tailWord_5867924, baseEnd_5867924] using wordTrace_append hprefix tailTrace_5867924
  have hstable : (prefixWord ++ tailWord_5867924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867924).length < 2 ^ (prefixWord ++ tailWord_5867924).sum := by decide
  have hdescent : baseEnd_5867924 < baseStart_5867924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867934 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5867934 : Nat := 118140960795 + 5867934 * 2 ^ 59
def prefixEnd_5867934 : Nat := 4983230072969 + 3 ^ 40 * 5867934 * 2
def baseEnd_5867934 : Nat := 1004356863619983304979623

theorem tailTrace_5867934 : CollatzResearch.WordTrace tailWord_5867934 prefixEnd_5867934 1004356863619983304979623 := by
  unfold tailWord_5867934
  simp only [CollatzResearch.WordTrace]
  refine ⟨26752641940435594523251357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142680757015656504124007237 26752641940435594523251357)
  ·
    refine ⟨10032240727663347946219259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26752641940435594523251357 10032240727663347946219259)
    ·
      refine ⟨15048361091495021919328889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032240727663347946219259 15048361091495021919328889)
      ·
        refine ⟨11286270818621266439496667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15048361091495021919328889 11286270818621266439496667)
        ·
          refine ⟨16929406227931899659245001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11286270818621266439496667 16929406227931899659245001)
          ·
            refine ⟨12697054670948924744433751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16929406227931899659245001 12697054670948924744433751)
            ·
              refine ⟨19045582006423387116650627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697054670948924744433751 19045582006423387116650627)
              ·
                refine ⟨28568373009635080674975941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19045582006423387116650627 28568373009635080674975941)
                ·
                  refine ⟨5356569939306577626557989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28568373009635080674975941 5356569939306577626557989)
                  ·
                    refine ⟨1004356863619983304979623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356569939306577626557989 1004356863619983304979623)
                    ·
                      rfl

theorem cell23_5867934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5867934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867934 prefixEnd_5867934 := by exact prefixLift 5867934
  have htrace : WordTrace (prefixWord ++ tailWord_5867934) baseStart_5867934 baseEnd_5867934 := by
    simpa [prefixWord, tailWord_5867934, baseEnd_5867934] using wordTrace_append hprefix tailTrace_5867934
  have hstable : (prefixWord ++ tailWord_5867934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867934).length < 2 ^ (prefixWord ++ tailWord_5867934).sum := by decide
  have hdescent : baseEnd_5867934 < baseStart_5867934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867940 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_5867940 : Nat := 118140960795 + 5867940 * 2 ^ 59
def prefixEnd_5867940 : Nat := 4983230072969 + 3 ^ 40 * 5867940 * 2
def baseEnd_5867940 : Nat := 3013073671743876891463841

theorem tailTrace_5867940 : CollatzResearch.WordTrace tailWord_5867940 prefixEnd_5867940 3013073671743876891463841 := by
  unfold tailWord_5867940
  simp only [CollatzResearch.WordTrace]
  refine ⟨107010677180731509605364637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142680902907642012807152849 107010677180731509605364637)
  ·
    refine ⟨40129003942774316102011739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107010677180731509605364637 40129003942774316102011739)
    ·
      refine ⟨60193505914161474153017609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40129003942774316102011739 60193505914161474153017609)
      ·
        refine ⟨45145129435621105614763207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60193505914161474153017609 45145129435621105614763207)
        ·
          refine ⟨67717694153431658422144811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45145129435621105614763207 67717694153431658422144811)
          ·
            refine ⟨101576541230147487633217217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67717694153431658422144811 101576541230147487633217217)
            ·
              refine ⟨76182405922610615724912913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101576541230147487633217217 76182405922610615724912913)
              ·
                refine ⟨57136804441957961793684685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76182405922610615724912913 57136804441957961793684685)
                ·
                  refine ⟨21426301665734235672631757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57136804441957961793684685 21426301665734235672631757)
                  ·
                    refine ⟨8034863124650338377236909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21426301665734235672631757 8034863124650338377236909)
                    ·
                      refine ⟨3013073671743876891463841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034863124650338377236909 3013073671743876891463841)
                      ·
                        rfl

theorem cell23_5867940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_5867940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867940 prefixEnd_5867940 := by exact prefixLift 5867940
  have htrace : WordTrace (prefixWord ++ tailWord_5867940) baseStart_5867940 baseEnd_5867940 := by
    simpa [prefixWord, tailWord_5867940, baseEnd_5867940] using wordTrace_append hprefix tailTrace_5867940
  have hstable : (prefixWord ++ tailWord_5867940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867940).length < 2 ^ (prefixWord ++ tailWord_5867940).sum := by decide
  have hdescent : baseEnd_5867940 < baseStart_5867940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868000 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_5868000 : Nat := 118140960795 + 5868000 * 2 ^ 59
def prefixEnd_5868000 : Nat := 4983230072969 + 3 ^ 40 * 5868000 * 2
def baseEnd_5868000 : Nat := 3013104480583146656713565

theorem tailTrace_5868000 : CollatzResearch.WordTrace tailWord_5868000 prefixEnd_5868000 3013104480583146656713565 := by
  unfold tailWord_5868000
  simp only [CollatzResearch.WordTrace]
  refine ⟨107011771370622824728956727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142682361827497099638608969 107011771370622824728956727)
  ·
    refine ⟨160517657055934237093435091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107011771370622824728956727 160517657055934237093435091)
    ·
      refine ⟨240776485583901355640152637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160517657055934237093435091 240776485583901355640152637)
      ·
        refine ⟨90291182093963008365057239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240776485583901355640152637 90291182093963008365057239)
        ·
          refine ⟨135436773140944512547585859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90291182093963008365057239 135436773140944512547585859)
          ·
            refine ⟨203155159711416768821378789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135436773140944512547585859 203155159711416768821378789)
            ·
              refine ⟨38091592445890644154008523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203155159711416768821378789 38091592445890644154008523)
              ·
                refine ⟨57137388668835966231012785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38091592445890644154008523 57137388668835966231012785)
                ·
                  refine ⟨42853041501626974673259589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57137388668835966231012785 42853041501626974673259589)
                  ·
                    refine ⟨8034945281555057751236173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42853041501626974673259589 8034945281555057751236173)
                    ·
                      refine ⟨3013104480583146656713565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8034945281555057751236173 3013104480583146656713565)
                      ·
                        rfl

theorem cell23_5868000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_5868000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868000 prefixEnd_5868000 := by exact prefixLift 5868000
  have htrace : WordTrace (prefixWord ++ tailWord_5868000) baseStart_5868000 baseEnd_5868000 := by
    simpa [prefixWord, tailWord_5868000, baseEnd_5868000] using wordTrace_append hprefix tailTrace_5868000
  have hstable : (prefixWord ++ tailWord_5868000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868000).length < 2 ^ (prefixWord ++ tailWord_5868000).sum := by decide
  have hdescent : baseEnd_5868000 < baseStart_5868000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868018 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5868018 : Nat := 118140960795 + 5868018 * 2 ^ 59
def prefixEnd_5868018 : Nat := 4983230072969 + 3 ^ 40 * 5868018 * 2
def baseEnd_5868018 : Nat := 3013113723234927586288483

theorem tailTrace_5868018 : CollatzResearch.WordTrace tailWord_5868018 prefixEnd_5868018 3013113723234927586288483 := by
  unfold tailWord_5868018
  simp only [CollatzResearch.WordTrace]
  refine ⟨53506049813795109633017177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142682799503453625688045805 53506049813795109633017177)
  ·
    refine ⟨40129537360346332224762883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53506049813795109633017177 40129537360346332224762883)
    ·
      refine ⟨60194306040519498337144325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40129537360346332224762883 60194306040519498337144325)
      ·
        refine ⟨11286432382597405938214561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60194306040519498337144325 11286432382597405938214561)
        ·
          refine ⟨8464824286948054453660921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11286432382597405938214561 8464824286948054453660921)
          ·
            refine ⟨6348618215211040840245691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8464824286948054453660921 6348618215211040840245691)
            ·
              refine ⟨9522927322816561260368537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348618215211040840245691 9522927322816561260368537)
              ·
                refine ⟨7142195492112420945276403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9522927322816561260368537 7142195492112420945276403)
                ·
                  refine ⟨10713293238168631417914605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7142195492112420945276403 10713293238168631417914605)
                  ·
                    refine ⟨4017484964313236781717977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10713293238168631417914605 4017484964313236781717977)
                    ·
                      refine ⟨3013113723234927586288483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017484964313236781717977 3013113723234927586288483)
                      ·
                        rfl

theorem cell23_5868018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5868018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868018 prefixEnd_5868018 := by exact prefixLift 5868018
  have htrace : WordTrace (prefixWord ++ tailWord_5868018) baseStart_5868018 baseEnd_5868018 := by
    simpa [prefixWord, tailWord_5868018, baseEnd_5868018] using wordTrace_append hprefix tailTrace_5868018
  have hstable : (prefixWord ++ tailWord_5868018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868018).length < 2 ^ (prefixWord ++ tailWord_5868018).sum := by decide
  have hdescent : baseEnd_5868018 < baseStart_5868018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868064 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5868064 : Nat := 118140960795 + 5868064 * 2 ^ 59
def prefixEnd_5868064 : Nat := 4983230072969 + 3 ^ 40 * 5868064 * 2
def baseEnd_5868064 : Nat := 3013137343345034406313271

theorem tailTrace_5868064 : CollatzResearch.WordTrace tailWord_5868064 prefixEnd_5868064 3013137343345034406313271 := by
  unfold tailWord_5868064
  simp only [CollatzResearch.WordTrace]
  refine ⟨107012938506506894194121623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142683918008675858925495497 107012938506506894194121623)
  ·
    refine ⟨160519407759760341291182435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107012938506506894194121623 160519407759760341291182435)
    ·
      refine ⟨240779111639640511936773653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160519407759760341291182435 240779111639640511936773653)
      ·
        refine ⟨11286520858108148997036265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240779111639640511936773653 11286520858108148997036265)
        ·
          refine ⟨8464890643581111747777199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11286520858108148997036265 8464890643581111747777199)
          ·
            refine ⟨12697335965371667621665799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464890643581111747777199 12697335965371667621665799)
            ·
              refine ⟨19046003948057501432498699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697335965371667621665799 19046003948057501432498699)
              ·
                refine ⟨28569005922086252148748049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19046003948057501432498699 28569005922086252148748049)
                ·
                  refine ⟨21426754441564689111561037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28569005922086252148748049 21426754441564689111561037)
                  ·
                    refine ⟨8035032915586758416835389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21426754441564689111561037 8035032915586758416835389)
                    ·
                      refine ⟨3013137343345034406313271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8035032915586758416835389 3013137343345034406313271)
                      ·
                        rfl

theorem cell23_5868064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5868064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868064 prefixEnd_5868064 := by exact prefixLift 5868064
  have htrace : WordTrace (prefixWord ++ tailWord_5868064) baseStart_5868064 baseEnd_5868064 := by
    simpa [prefixWord, tailWord_5868064, baseEnd_5868064] using wordTrace_append hprefix tailTrace_5868064
  have hstable : (prefixWord ++ tailWord_5868064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868064).length < 2 ^ (prefixWord ++ tailWord_5868064).sum := by decide
  have hdescent : baseEnd_5868064 < baseStart_5868064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868087 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 6, 2]
def baseStart_5868087 : Nat := 118140960795 + 5868087 * 2 ^ 59
def prefixEnd_5868087 : Nat := 4983230072969 + 3 ^ 40 * 5868087 * 2
def baseEnd_5868087 : Nat := 3013149153400087816325665

theorem tailTrace_5868087 : CollatzResearch.WordTrace tailWord_5868087 prefixEnd_5868087 3013149153400087816325665 := by
  unfold tailWord_5868087
  simp only [CollatzResearch.WordTrace]
  refine ⟨214026715891930463316330515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142684477261286975544220343 214026715891930463316330515)
  ·
    refine ⟨321040073837895694974495773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214026715891930463316330515 321040073837895694974495773)
    ·
      refine ⟨120390027689210885615435915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321040073837895694974495773 120390027689210885615435915)
      ·
        refine ⟨180585041533816328423153873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120390027689210885615435915 180585041533816328423153873)
        ·
          refine ⟨135438781150362246317365405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180585041533816328423153873 135438781150362246317365405)
          ·
            refine ⟨50789542931385842369012027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135438781150362246317365405 50789542931385842369012027)
            ·
              refine ⟨76184314397078763553518041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50789542931385842369012027 76184314397078763553518041)
              ·
                refine ⟨57138235797809072665138531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76184314397078763553518041 57138235797809072665138531)
                ·
                  refine ⟨85707353696713608997707797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57138235797809072665138531 85707353696713608997707797)
                  ·
                    refine ⟨4017532204533450421767553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85707353696713608997707797 4017532204533450421767553)
                    ·
                      refine ⟨3013149153400087816325665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017532204533450421767553 3013149153400087816325665)
                      ·
                        rfl

theorem cell23_5868087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_5868087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868087 prefixEnd_5868087 := by exact prefixLift 5868087
  have htrace : WordTrace (prefixWord ++ tailWord_5868087) baseStart_5868087 baseEnd_5868087 := by
    simpa [prefixWord, tailWord_5868087, baseEnd_5868087] using wordTrace_append hprefix tailTrace_5868087
  have hstable : (prefixWord ++ tailWord_5868087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868087).length < 2 ^ (prefixWord ++ tailWord_5868087).sum := by decide
  have hdescent : baseEnd_5868087 < baseStart_5868087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868107 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 3]
def baseStart_5868107 : Nat := 118140960795 + 5868107 * 2 ^ 59
def prefixEnd_5868107 : Nat := 4983230072969 + 3 ^ 40 * 5868107 * 2
def baseEnd_5868107 : Nat := 3013159423013177738075573

theorem tailTrace_5868107 : CollatzResearch.WordTrace tailWord_5868107 prefixEnd_5868107 3013159423013177738075573 := by
  unfold tailWord_5868107
  simp only [CollatzResearch.WordTrace]
  refine ⟨214027445351858006732058575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142684963567905337821372383 214027445351858006732058575)
  ·
    refine ⟨321041168027787010098087863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214027445351858006732058575 321041168027787010098087863)
    ·
      refine ⟨481561752041680515147131795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321041168027787010098087863 481561752041680515147131795)
      ·
        refine ⟨722342628062520772720697693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481561752041680515147131795 722342628062520772720697693)
        ·
          refine ⟨270878485523445289770261635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722342628062520772720697693 270878485523445289770261635)
          ·
            refine ⟨406317728285167934655392453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270878485523445289770261635 406317728285167934655392453)
            ·
              refine ⟨76184574053468987747886085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406317728285167934655392453 76184574053468987747886085)
              ·
                refine ⟨14284607635025435202728641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76184574053468987747886085 14284607635025435202728641)
                ·
                  refine ⟨10713455726269076402046481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14284607635025435202728641 10713455726269076402046481)
                  ·
                    refine ⟨8035091794701807301534861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10713455726269076402046481 8035091794701807301534861)
                    ·
                      refine ⟨3013159423013177738075573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8035091794701807301534861 3013159423013177738075573)
                      ·
                        rfl

theorem cell23_5868107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 3].length) (baseStart_5868107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868107 prefixEnd_5868107 := by exact prefixLift 5868107
  have htrace : WordTrace (prefixWord ++ tailWord_5868107) baseStart_5868107 baseEnd_5868107 := by
    simpa [prefixWord, tailWord_5868107, baseEnd_5868107] using wordTrace_append hprefix tailTrace_5868107
  have hstable : (prefixWord ++ tailWord_5868107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868107).length < 2 ^ (prefixWord ++ tailWord_5868107).sum := by decide
  have hdescent : baseEnd_5868107 < baseStart_5868107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868114 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_5868114 : Nat := 118140960795 + 5868114 * 2 ^ 59
def prefixEnd_5868114 : Nat := 4983230072969 + 3 ^ 40 * 5868114 * 2
def baseEnd_5868114 : Nat := 1004387672459253070229347

theorem tailTrace_5868114 : CollatzResearch.WordTrace tailWord_5868114 prefixEnd_5868114 1004387672459253070229347 := by
  unfold tailWord_5868114
  simp only [CollatzResearch.WordTrace]
  refine ⟨53506925165708161731890849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142685133775221764618375597 53506925165708161731890849)
  ·
    refine ⟨40130193874281121298918137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53506925165708161731890849 40130193874281121298918137)
    ·
      refine ⟨30097645405710840974188603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40130193874281121298918137 30097645405710840974188603)
      ·
        refine ⟨45146468108566261461282905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30097645405710840974188603 45146468108566261461282905)
        ·
          refine ⟨33859851081424696095962179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45146468108566261461282905 33859851081424696095962179)
          ·
            refine ⟨50789776622137044143943269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33859851081424696095962179 50789776622137044143943269)
            ·
              refine ⟨9523083116650695776989363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50789776622137044143943269 9523083116650695776989363)
              ·
                refine ⟨14284624674976043665484045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9523083116650695776989363 14284624674976043665484045)
                ·
                  refine ⟨5356734253116016374556517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14284624674976043665484045 5356734253116016374556517)
                  ·
                    refine ⟨1004387672459253070229347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356734253116016374556517 1004387672459253070229347)
                    ·
                      rfl

theorem cell23_5868114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_5868114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868114 prefixEnd_5868114 := by exact prefixLift 5868114
  have htrace : WordTrace (prefixWord ++ tailWord_5868114) baseStart_5868114 baseEnd_5868114 := by
    simpa [prefixWord, tailWord_5868114, baseEnd_5868114] using wordTrace_append hprefix tailTrace_5868114
  have hstable : (prefixWord ++ tailWord_5868114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868114).length < 2 ^ (prefixWord ++ tailWord_5868114).sum := by decide
  have hdescent : baseEnd_5868114 < baseStart_5868114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868207 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_5868207 : Nat := 118140960795 + 5868207 * 2 ^ 59
def prefixEnd_5868207 : Nat := 4983230072969 + 3 ^ 40 * 5868207 * 2
def baseEnd_5868207 : Nat := 3013210771078627346825113

theorem tailTrace_5868207 : CollatzResearch.WordTrace tailWord_5868207 prefixEnd_5868207 3013210771078627346825113 := by
  unfold tailWord_5868207
  simp only [CollatzResearch.WordTrace]
  refine ⟨214031092651495723810698875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142687395100997149207132583 214031092651495723810698875)
  ·
    refine ⟨321046638977243585716048313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214031092651495723810698875 321046638977243585716048313)
    ·
      refine ⟨240784979232932689287036235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321046638977243585716048313 240784979232932689287036235)
      ·
        refine ⟨361177468849399033930554353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240784979232932689287036235 361177468849399033930554353)
        ·
          refine ⟨270883101637049275447915765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361177468849399033930554353 270883101637049275447915765)
          ·
            refine ⟨25395290778473369573242103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270883101637049275447915765 25395290778473369573242103)
            ·
              refine ⟨38092936167710054359863155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25395290778473369573242103 38092936167710054359863155)
              ·
                refine ⟨57139404251565081539794733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38092936167710054359863155 57139404251565081539794733)
                ·
                  refine ⟨21427276594336905577423025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57139404251565081539794733 21427276594336905577423025)
                  ·
                    refine ⟨16070457445752679183067269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21427276594336905577423025 16070457445752679183067269)
                    ·
                      refine ⟨3013210771078627346825113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16070457445752679183067269 3013210771078627346825113)
                      ·
                        rfl

theorem cell23_5868207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_5868207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868207 prefixEnd_5868207 := by exact prefixLift 5868207
  have htrace : WordTrace (prefixWord ++ tailWord_5868207) baseStart_5868207 baseEnd_5868207 := by
    simpa [prefixWord, tailWord_5868207, baseEnd_5868207] using wordTrace_append hprefix tailTrace_5868207
  have hstable : (prefixWord ++ tailWord_5868207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868207).length < 2 ^ (prefixWord ++ tailWord_5868207).sum := by decide
  have hdescent : baseEnd_5868207 < baseStart_5868207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868211 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 1, 1, 4]
def baseStart_5868211 : Nat := 118140960795 + 5868211 * 2 ^ 59
def prefixEnd_5868211 : Nat := 4983230072969 + 3 ^ 40 * 5868211 * 2
def baseEnd_5868211 : Nat := 3013212825001245331175095

theorem tailTrace_5868211 : CollatzResearch.WordTrace tailWord_5868211 prefixEnd_5868211 3013212825001245331175095 := by
  unfold tailWord_5868211
  simp only [CollatzResearch.WordTrace]
  refine ⟨214031238543481232493844487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142687492362320821662562991 214031238543481232493844487)
  ·
    refine ⟨321046857815221848740766731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214031238543481232493844487 321046857815221848740766731)
    ·
      refine ⟨481570286722832773111150097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321046857815221848740766731 481570286722832773111150097)
      ·
        refine ⟨361177715042124579833362573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481570286722832773111150097 361177715042124579833362573)
        ·
          refine ⟨135441643140796717437510965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361177715042124579833362573 135441643140796717437510965)
          ·
            refine ⟨12697654044449692259766653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135441643140796717437510965 12697654044449692259766653)
            ·
              refine ⟨4761620266668634597412495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12697654044449692259766653 4761620266668634597412495)
              ·
                refine ⟨7142430400002951896118743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761620266668634597412495 7142430400002951896118743)
                ·
                  refine ⟨10713645600004427844178115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7142430400002951896118743 10713645600004427844178115)
                  ·
                    refine ⟨16070468400006641766267173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10713645600004427844178115 16070468400006641766267173)
                    ·
                      refine ⟨3013212825001245331175095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16070468400006641766267173 3013212825001245331175095)
                      ·
                        rfl

theorem cell23_5868211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 1, 4].length) (baseStart_5868211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868211 prefixEnd_5868211 := by exact prefixLift 5868211
  have htrace : WordTrace (prefixWord ++ tailWord_5868211) baseStart_5868211 baseEnd_5868211 := by
    simpa [prefixWord, tailWord_5868211, baseEnd_5868211] using wordTrace_append hprefix tailTrace_5868211
  have hstable : (prefixWord ++ tailWord_5868211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868211).length < 2 ^ (prefixWord ++ tailWord_5868211).sum := by decide
  have hdescent : baseEnd_5868211 < baseStart_5868211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868221 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_5868221 : Nat := 118140960795 + 5868221 * 2 ^ 59
def prefixEnd_5868221 : Nat := 4983230072969 + 3 ^ 40 * 5868221 * 2
def baseEnd_5868221 : Nat := 1004405986602596764016683

theorem tailTrace_5868221 : CollatzResearch.WordTrace tailWord_5868221 prefixEnd_5868221 1004405986602596764016683 := by
  unfold tailWord_5868221
  simp only [CollatzResearch.WordTrace]
  refine ⟨214031603273445004201708517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142687735515630002801139011 214031603273445004201708517)
  ·
    refine ⟨40130925613770938287820347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214031603273445004201708517 40130925613770938287820347)
    ·
      refine ⟨60196388420656407431730521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40130925613770938287820347 60196388420656407431730521)
      ·
        refine ⟨45147291315492305573797891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60196388420656407431730521 45147291315492305573797891)
        ·
          refine ⟨67720936973238458360696837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45147291315492305573797891 67720936973238458360696837)
          ·
            refine ⟨12697675682482210942630657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67720936973238458360696837 12697675682482210942630657)
            ·
              refine ⟨9523256761861658206972993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12697675682482210942630657 9523256761861658206972993)
              ·
                refine ⟨7142442571396243655229745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9523256761861658206972993 7142442571396243655229745)
                ·
                  refine ⟨5356831928547182741422309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7142442571396243655229745 5356831928547182741422309)
                  ·
                    refine ⟨1004405986602596764016683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5356831928547182741422309 1004405986602596764016683)
                    ·
                      rfl

theorem cell23_5868221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_5868221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868221 prefixEnd_5868221 := by exact prefixLift 5868221
  have htrace : WordTrace (prefixWord ++ tailWord_5868221) baseStart_5868221 baseEnd_5868221 := by
    simpa [prefixWord, tailWord_5868221, baseEnd_5868221] using wordTrace_append hprefix tailTrace_5868221
  have hstable : (prefixWord ++ tailWord_5868221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868221).length < 2 ^ (prefixWord ++ tailWord_5868221).sum := by decide
  have hdescent : baseEnd_5868221 < baseStart_5868221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868234 : List Nat := [3, 1, 2, 1, 4, 3, 1, 8]
def baseStart_5868234 : Nat := 118140960795 + 5868234 * 2 ^ 59
def prefixEnd_5868234 : Nat := 4983230072969 + 3 ^ 40 * 5868234 * 2
def baseEnd_5868234 : Nat := 111600912409492545969907

theorem tailTrace_5868234 : CollatzResearch.WordTrace tailWord_5868234 prefixEnd_5868234 111600912409492545969907 := by
  unfold tailWord_5868234
  simp only [CollatzResearch.WordTrace]
  refine ⟨53508019355599476855482939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142688051614931938281287837 53508019355599476855482939)
  ·
    refine ⟨80262029033399215283224409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53508019355599476855482939 80262029033399215283224409)
    ·
      refine ⟨60196521775049411462418307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80262029033399215283224409 60196521775049411462418307)
      ·
        refine ⟨90294782662574117193627461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60196521775049411462418307 90294782662574117193627461)
        ·
          refine ⟨16930271749232646973805149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90294782662574117193627461 16930271749232646973805149)
          ·
            refine ⟨6348851905962242615176931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16930271749232646973805149 6348851905962242615176931)
            ·
              refine ⟨9523277858943363922765397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348851905962242615176931 9523277858943363922765397)
              ·
                refine ⟨111600912409492545969907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9523277858943363922765397 111600912409492545969907)
                ·
                  rfl

theorem cell23_5868234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_5868234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868234 prefixEnd_5868234 := by exact prefixLift 5868234
  have htrace : WordTrace (prefixWord ++ tailWord_5868234) baseStart_5868234 baseEnd_5868234 := by
    simpa [prefixWord, tailWord_5868234, baseEnd_5868234] using wordTrace_append hprefix tailTrace_5868234
  have hstable : (prefixWord ++ tailWord_5868234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868234).length < 2 ^ (prefixWord ++ tailWord_5868234).sum := by decide
  have hdescent : baseEnd_5868234 < baseStart_5868234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868245 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5868245 : Nat := 118140960795 + 5868245 * 2 ^ 59
def prefixEnd_5868245 : Nat := 4983230072969 + 3 ^ 40 * 5868245 * 2
def baseEnd_5868245 : Nat := 3013230283343498198149939

theorem tailTrace_5868245 : CollatzResearch.WordTrace tailWord_5868245 prefixEnd_5868245 3013230283343498198149939 := by
  unfold tailWord_5868245
  simp only [CollatzResearch.WordTrace]
  refine ⟨214032478625358056300582189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142688319083572037533721459 214032478625358056300582189)
  ·
    refine ⟨80262179484509271112718321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214032478625358056300582189 80262179484509271112718321)
    ·
      refine ⟨60196634613381953334538741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80262179484509271112718321 60196634613381953334538741)
      ·
        refine ⟨5643434495004558125113007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60196634613381953334538741 5643434495004558125113007)
        ·
          refine ⟨8465151742506837187669511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643434495004558125113007 8465151742506837187669511)
          ·
            refine ⟨12697727613760255781504267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465151742506837187669511 12697727613760255781504267)
            ·
              refine ⟨19046591420640383672256401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697727613760255781504267 19046591420640383672256401)
              ·
                refine ⟨14284943565480287754192301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19046591420640383672256401 14284943565480287754192301)
                ·
                  refine ⟨5356853837055107907822113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14284943565480287754192301 5356853837055107907822113)
                  ·
                    refine ⟨4017640377791330930866585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5356853837055107907822113 4017640377791330930866585)
                    ·
                      refine ⟨3013230283343498198149939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017640377791330930866585 3013230283343498198149939)
                      ·
                        rfl

theorem cell23_5868245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5868245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868245 prefixEnd_5868245 := by exact prefixLift 5868245
  have htrace : WordTrace (prefixWord ++ tailWord_5868245) baseStart_5868245 baseEnd_5868245 := by
    simpa [prefixWord, tailWord_5868245, baseEnd_5868245] using wordTrace_append hprefix tailTrace_5868245
  have hstable : (prefixWord ++ tailWord_5868245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868245).length < 2 ^ (prefixWord ++ tailWord_5868245).sum := by decide
  have hdescent : baseEnd_5868245 < baseStart_5868245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868287 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_5868287 : Nat := 118140960795 + 5868287 * 2 ^ 59
def prefixEnd_5868287 : Nat := 4983230072969 + 3 ^ 40 * 5868287 * 2
def baseEnd_5868287 : Nat := 3013251849530987033824745

theorem tailTrace_5868287 : CollatzResearch.WordTrace tailWord_5868287 prefixEnd_5868287 3013251849530987033824745 := by
  unfold tailWord_5868287
  simp only [CollatzResearch.WordTrace]
  refine ⟨214034010491205897473611115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142689340327470598315740743 214034010491205897473611115)
  ·
    refine ⟨321051015736808846210416673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214034010491205897473611115 321051015736808846210416673)
    ·
      refine ⟨240788261802606634657812505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321051015736808846210416673 240788261802606634657812505)
      ·
        refine ⟨180591196351954975993359379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240788261802606634657812505 180591196351954975993359379)
        ·
          refine ⟨270886794527932463990039069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180591196351954975993359379 270886794527932463990039069)
          ·
            refine ⟨101582547947974673996264651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270886794527932463990039069 101582547947974673996264651)
            ·
              refine ⟨152373821921962010994396977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101582547947974673996264651 152373821921962010994396977)
              ·
                refine ⟨114280366441471508245797733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152373821921962010994396977 114280366441471508245797733)
                ·
                  refine ⟨21427568707775907796087075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114280366441471508245797733 21427568707775907796087075)
                  ·
                    refine ⟨32141353061663861694130613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21427568707775907796087075 32141353061663861694130613)
                    ·
                      refine ⟨3013251849530987033824745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32141353061663861694130613 3013251849530987033824745)
                      ·
                        rfl

theorem cell23_5868287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_5868287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868287 prefixEnd_5868287 := by exact prefixLift 5868287
  have htrace : WordTrace (prefixWord ++ tailWord_5868287) baseStart_5868287 baseEnd_5868287 := by
    simpa [prefixWord, tailWord_5868287, baseEnd_5868287] using wordTrace_append hprefix tailTrace_5868287
  have hstable : (prefixWord ++ tailWord_5868287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868287).length < 2 ^ (prefixWord ++ tailWord_5868287).sum := by decide
  have hdescent : baseEnd_5868287 < baseStart_5868287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868295 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5868295 : Nat := 118140960795 + 5868295 * 2 ^ 59
def prefixEnd_5868295 : Nat := 4983230072969 + 3 ^ 40 * 5868295 * 2
def baseEnd_5868295 : Nat := 3013255957376223002524709

theorem tailTrace_5868295 : CollatzResearch.WordTrace tailWord_5868295 prefixEnd_5868295 3013255957376223002524709 := by
  unfold tailWord_5868295
  simp only [CollatzResearch.WordTrace]
  refine ⟨214034302275176914839902339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142689534850117943226601559 214034302275176914839902339)
  ·
    refine ⟨321051453412765372259853509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214034302275176914839902339 321051453412765372259853509)
    ·
      refine ⟨60197147514893507298722533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321051453412765372259853509 60197147514893507298722533)
      ·
        refine ⟨11286965159042532618510475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60197147514893507298722533 11286965159042532618510475)
        ·
          refine ⟨16930447738563798927765713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11286965159042532618510475 16930447738563798927765713)
          ·
            refine ⟨12697835803922849195824285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16930447738563798927765713 12697835803922849195824285)
            ·
              refine ⟨4761688426471068448434107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12697835803922849195824285 4761688426471068448434107)
              ·
                refine ⟨7142532639706602672651161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761688426471068448434107 7142532639706602672651161)
                ·
                  refine ⟨5356899479779952004488371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7142532639706602672651161 5356899479779952004488371)
                  ·
                    refine ⟨8035349219669928006732557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5356899479779952004488371 8035349219669928006732557)
                    ·
                      refine ⟨3013255957376223002524709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8035349219669928006732557 3013255957376223002524709)
                      ·
                        rfl

theorem cell23_5868295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5868295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868295 prefixEnd_5868295 := by exact prefixLift 5868295
  have htrace : WordTrace (prefixWord ++ tailWord_5868295) baseStart_5868295 baseEnd_5868295 := by
    simpa [prefixWord, tailWord_5868295, baseEnd_5868295] using wordTrace_append hprefix tailTrace_5868295
  have hstable : (prefixWord ++ tailWord_5868295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868295).length < 2 ^ (prefixWord ++ tailWord_5868295).sum := by decide
  have hdescent : baseEnd_5868295 < baseStart_5868295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868307 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 7]
def baseStart_5868307 : Nat := 118140960795 + 5868307 * 2 ^ 59
def prefixEnd_5868307 : Nat := 4983230072969 + 3 ^ 40 * 5868307 * 2
def baseEnd_5868307 : Nat := 334806902127119661730517

theorem tailTrace_5868307 : CollatzResearch.WordTrace tailWord_5868307 prefixEnd_5868307 334806902127119661730517 := by
  unfold tailWord_5868307
  simp only [CollatzResearch.WordTrace]
  refine ⟨214034739951133440889339175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142689826634088960592892783 214034739951133440889339175)
  ·
    refine ⟨321052109926700161334008763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214034739951133440889339175 321052109926700161334008763)
    ·
      refine ⟨481578164890050242001013145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321052109926700161334008763 481578164890050242001013145)
      ·
        refine ⟨361183623667537681500759859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481578164890050242001013145 361183623667537681500759859)
        ·
          refine ⟨541775435501306522251139789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361183623667537681500759859 541775435501306522251139789)
          ·
            refine ⟨203165788312989945844177421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541775435501306522251139789 203165788312989945844177421)
            ·
              refine ⟨76187170617371229691566533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203165788312989945844177421 76187170617371229691566533)
              ·
                refine ⟨14285094490757105567168725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76187170617371229691566533 14285094490757105567168725)
                ·
                  refine ⟨334806902127119661730517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14285094490757105567168725 334806902127119661730517)
                  ·
                    rfl

theorem cell23_5868307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 7].length) (baseStart_5868307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868307 prefixEnd_5868307 := by exact prefixLift 5868307
  have htrace : WordTrace (prefixWord ++ tailWord_5868307) baseStart_5868307 baseEnd_5868307 := by
    simpa [prefixWord, tailWord_5868307, baseEnd_5868307] using wordTrace_append hprefix tailTrace_5868307
  have hstable : (prefixWord ++ tailWord_5868307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868307).length < 2 ^ (prefixWord ++ tailWord_5868307).sum := by decide
  have hdescent : baseEnd_5868307 < baseStart_5868307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868341 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 7]
def baseStart_5868341 : Nat := 118140960795 + 5868341 * 2 ^ 59
def prefixEnd_5868341 : Nat := 4983230072969 + 3 ^ 40 * 5868341 * 2
def baseEnd_5868341 : Nat := 334808841942925535838833

theorem tailTrace_5868341 : CollatzResearch.WordTrace tailWord_5868341 prefixEnd_5868341 334808841942925535838833 := by
  unfold tailWord_5868341
  simp only [CollatzResearch.WordTrace]
  refine ⟨214035980033010264696076877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142690653355340176464051251 214035980033010264696076877)
  ·
    refine ⟨80263492512378849261028829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214035980033010264696076877 80263492512378849261028829)
    ·
      refine ⟨30098809692142068472885811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80263492512378849261028829 30098809692142068472885811)
      ·
        refine ⟨45148214538213102709328717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30098809692142068472885811 45148214538213102709328717)
        ·
          refine ⟨16930580451829913515998269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45148214538213102709328717 16930580451829913515998269)
          ·
            refine ⟨6348967669436217568499351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16930580451829913515998269 6348967669436217568499351)
            ·
              refine ⟨9523451504154326352749027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6348967669436217568499351 9523451504154326352749027)
              ·
                refine ⟨14285177256231489529123541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9523451504154326352749027 14285177256231489529123541)
                ·
                  refine ⟨334808841942925535838833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14285177256231489529123541 334808841942925535838833)
                  ·
                    rfl

theorem cell23_5868341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_5868341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868341 prefixEnd_5868341 := by exact prefixLift 5868341
  have htrace : WordTrace (prefixWord ++ tailWord_5868341) baseStart_5868341 baseEnd_5868341 := by
    simpa [prefixWord, tailWord_5868341, baseEnd_5868341] using wordTrace_append hprefix tailTrace_5868341
  have hstable : (prefixWord ++ tailWord_5868341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868341).length < 2 ^ (prefixWord ++ tailWord_5868341).sum := by decide
  have hdescent : baseEnd_5868341 < baseStart_5868341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868391 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_5868391 : Nat := 118140960795 + 5868391 * 2 ^ 59
def prefixEnd_5868391 : Nat := 4983230072969 + 3 ^ 40 * 5868391 * 2
def baseEnd_5868391 : Nat := 3013305251519054626924267

theorem tailTrace_5868391 : CollatzResearch.WordTrace tailWord_5868391 prefixEnd_5868391 3013305251519054626924267 := by
  unfold tailWord_5868391
  simp only [CollatzResearch.WordTrace]
  refine ⟨214037803682829123235397027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142691869121886082156931351 214037803682829123235397027)
  ·
    refine ⟨321056705524243684853095541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214037803682829123235397027 321056705524243684853095541)
    ·
      refine ⟨30099066142897845454977707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321056705524243684853095541 30099066142897845454977707)
      ·
        refine ⟨45148599214346768182466561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30099066142897845454977707 45148599214346768182466561)
        ·
          refine ⟨33861449410760076136849921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45148599214346768182466561 33861449410760076136849921)
          ·
            refine ⟨25396087058070057102637441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33861449410760076136849921 25396087058070057102637441)
            ·
              refine ⟨19047065293552542826978081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25396087058070057102637441 19047065293552542826978081)
              ·
                refine ⟨14285298970164407120233561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19047065293552542826978081 14285298970164407120233561)
                ·
                  refine ⟨10713974227623305340175171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14285298970164407120233561 10713974227623305340175171)
                  ·
                    refine ⟨16070961341434958010262757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10713974227623305340175171 16070961341434958010262757)
                    ·
                      refine ⟨3013305251519054626924267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16070961341434958010262757 3013305251519054626924267)
                      ·
                        rfl

theorem cell23_5868391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_5868391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868391 prefixEnd_5868391 := by exact prefixLift 5868391
  have htrace : WordTrace (prefixWord ++ tailWord_5868391) baseStart_5868391 baseEnd_5868391 := by
    simpa [prefixWord, tailWord_5868391, baseEnd_5868391] using wordTrace_append hprefix tailTrace_5868391
  have hstable : (prefixWord ++ tailWord_5868391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868391).length < 2 ^ (prefixWord ++ tailWord_5868391).sum := by decide
  have hdescent : baseEnd_5868391 < baseStart_5868391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868441 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 3]
def baseStart_5868441 : Nat := 118140960795 + 5868441 * 2 ^ 59
def prefixEnd_5868441 : Nat := 4983230072969 + 3 ^ 40 * 5868441 * 2
def baseEnd_5868441 : Nat := 3013330925551779431299037

theorem tailTrace_5868441 : CollatzResearch.WordTrace tailWord_5868441 prefixEnd_5868441 3013330925551779431299037 := by
  unfold tailWord_5868441
  simp only [CollatzResearch.WordTrace]
  refine ⟨214039627332647981774717177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142693084888431987849811451 214039627332647981774717177)
  ·
    refine ⟨160529720499485986331037883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214039627332647981774717177 160529720499485986331037883)
    ·
      refine ⟨240794580749228979496556825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160529720499485986331037883 240794580749228979496556825)
      ·
        refine ⟨180595935561921734622417619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240794580749228979496556825 180595935561921734622417619)
        ·
          refine ⟨270893903342882601933626429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180595935561921734622417619 270893903342882601933626429)
          ·
            refine ⟨101585213753580975725109911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270893903342882601933626429 101585213753580975725109911)
            ·
              refine ⟨152377820630371463587664867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101585213753580975725109911 152377820630371463587664867)
              ·
                refine ⟨228566730945557195381497301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152377820630371463587664867 228566730945557195381497301)
                ·
                  refine ⟨5357032756536496766753843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 228566730945557195381497301 5357032756536496766753843)
                  ·
                    refine ⟨8035549134804745150130765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357032756536496766753843 8035549134804745150130765)
                    ·
                      refine ⟨3013330925551779431299037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8035549134804745150130765 3013330925551779431299037)
                      ·
                        rfl

theorem cell23_5868441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_5868441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868441 prefixEnd_5868441 := by exact prefixLift 5868441
  have htrace : WordTrace (prefixWord ++ tailWord_5868441) baseStart_5868441 baseEnd_5868441 := by
    simpa [prefixWord, tailWord_5868441, baseEnd_5868441] using wordTrace_append hprefix tailTrace_5868441
  have hstable : (prefixWord ++ tailWord_5868441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868441).length < 2 ^ (prefixWord ++ tailWord_5868441).sum := by decide
  have hdescent : baseEnd_5868441 < baseStart_5868441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868478 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_5868478 : Nat := 118140960795 + 5868478 * 2 ^ 59
def prefixEnd_5868478 : Nat := 4983230072969 + 3 ^ 40 * 5868478 * 2
def baseEnd_5868478 : Nat := 1004449974778665262178789

theorem tailTrace_5868478 : CollatzResearch.WordTrace tailWord_5868478 prefixEnd_5868478 1004449974778665262178789 := by
  unfold tailWord_5868478
  simp only [CollatzResearch.WordTrace]
  refine ⟨26755122104189242136726761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142693984555675958062542725 26755122104189242136726761)
  ·
    refine ⟨20066341578141931602545071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26755122104189242136726761 20066341578141931602545071)
    ·
      refine ⟨30099512367212897403817607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20066341578141931602545071 30099512367212897403817607)
      ·
        refine ⟨45149268550819346105726411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30099512367212897403817607 45149268550819346105726411)
        ·
          refine ⟨67723902826229019158589617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45149268550819346105726411 67723902826229019158589617)
          ·
            refine ⟨50792927119671764368942213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67723902826229019158589617 50792927119671764368942213)
            ·
              refine ⟨9523673834938455819176665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50792927119671764368942213 9523673834938455819176665)
              ·
                refine ⟨7142755376203841864382499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9523673834938455819176665 7142755376203841864382499)
                ·
                  refine ⟨10714133064305762796573749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7142755376203841864382499 10714133064305762796573749)
                  ·
                    refine ⟨1004449974778665262178789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10714133064305762796573749 1004449974778665262178789)
                    ·
                      rfl

theorem cell23_5868478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_5868478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868478 prefixEnd_5868478 := by exact prefixLift 5868478
  have htrace : WordTrace (prefixWord ++ tailWord_5868478) baseStart_5868478 baseEnd_5868478 := by
    simpa [prefixWord, tailWord_5868478, baseEnd_5868478] using wordTrace_append hprefix tailTrace_5868478
  have hstable : (prefixWord ++ tailWord_5868478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868478).length < 2 ^ (prefixWord ++ tailWord_5868478).sum := by decide
  have hdescent : baseEnd_5868478 < baseStart_5868478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868491 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 4, 4]
def baseStart_5868491 : Nat := 118140960795 + 5868491 * 2 ^ 59
def prefixEnd_5868491 : Nat := 4983230072969 + 3 ^ 40 * 5868491 * 2
def baseEnd_5868491 : Nat := 1004452199861501411891269

theorem tailTrace_5868491 : CollatzResearch.WordTrace tailWord_5868491 prefixEnd_5868491 1004452199861501411891269 := by
  unfold tailWord_5868491
  simp only [CollatzResearch.WordTrace]
  refine ⟨214041450982466840314037327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142694300654977893542691551 214041450982466840314037327)
  ·
    refine ⟨321062176473700260471055991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214041450982466840314037327 321062176473700260471055991)
    ·
      refine ⟨481593264710550390706583987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321062176473700260471055991 481593264710550390706583987)
      ·
        refine ⟨722389897065825586059875981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481593264710550390706583987 722389897065825586059875981)
        ·
          refine ⟨270896211399684594772453493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722389897065825586059875981 270896211399684594772453493)
          ·
            refine ⟨25396519818720430759917515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270896211399684594772453493 25396519818720430759917515)
            ·
              refine ⟨38094779728080646139876273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25396519818720430759917515 38094779728080646139876273)
              ·
                refine ⟨28571084796060484604907205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38094779728080646139876273 28571084796060484604907205)
                ·
                  refine ⟨5357078399261340863420101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28571084796060484604907205 5357078399261340863420101)
                  ·
                    refine ⟨1004452199861501411891269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357078399261340863420101 1004452199861501411891269)
                    ·
                      rfl

theorem cell23_5868491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 4].length) (baseStart_5868491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868491 prefixEnd_5868491 := by exact prefixLift 5868491
  have htrace : WordTrace (prefixWord ++ tailWord_5868491) baseStart_5868491 baseEnd_5868491 := by
    simpa [prefixWord, tailWord_5868491, baseEnd_5868491] using wordTrace_append hprefix tailTrace_5868491
  have hstable : (prefixWord ++ tailWord_5868491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868491).length < 2 ^ (prefixWord ++ tailWord_5868491).sum := by decide
  have hdescent : baseEnd_5868491 < baseStart_5868491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868502 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_5868502 : Nat := 118140960795 + 5868502 * 2 ^ 59
def prefixEnd_5868502 : Nat := 4983230072969 + 3 ^ 40 * 5868502 * 2
def baseEnd_5868502 : Nat := 3013362247871703692636257

theorem tailTrace_5868502 : CollatzResearch.WordTrace tailWord_5868502 prefixEnd_5868502 3013362247871703692636257 := by
  unfold tailWord_5868502
  simp only [CollatzResearch.WordTrace]
  refine ⟨13377615761589186824542985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142694568123617992795125173 13377615761589186824542985)
  ·
    refine ⟨10033211821191890118407239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13377615761589186824542985 10033211821191890118407239)
    ·
      refine ⟨15049817731787835177610859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10033211821191890118407239 15049817731787835177610859)
      ·
        refine ⟨22574726597681752766416289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15049817731787835177610859 22574726597681752766416289)
        ·
          refine ⟨16931044948261314574812217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22574726597681752766416289 16931044948261314574812217)
          ·
            refine ⟨12698283711195985931109163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16931044948261314574812217 12698283711195985931109163)
            ·
              refine ⟨19047425566793978896663745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12698283711195985931109163 19047425566793978896663745)
              ·
                refine ⟨14285569175095484172497809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19047425566793978896663745 14285569175095484172497809)
                ·
                  refine ⟨10714176881321613129373357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14285569175095484172497809 10714176881321613129373357)
                  ·
                    refine ⟨4017816330495604923515009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10714176881321613129373357 4017816330495604923515009)
                    ·
                      refine ⟨3013362247871703692636257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017816330495604923515009 3013362247871703692636257)
                      ·
                        rfl

theorem cell23_5868502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_5868502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868502 prefixEnd_5868502 := by exact prefixLift 5868502
  have htrace : WordTrace (prefixWord ++ tailWord_5868502) baseStart_5868502 baseEnd_5868502 := by
    simpa [prefixWord, tailWord_5868502, baseEnd_5868502] using wordTrace_append hprefix tailTrace_5868502
  have hstable : (prefixWord ++ tailWord_5868502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868502).length < 2 ^ (prefixWord ++ tailWord_5868502).sum := by decide
  have hdescent : baseEnd_5868502 < baseStart_5868502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868504 : List Nat := [2, 1, 2, 2, 2, 3, 11]
def baseStart_5868504 : Nat := 118140960795 + 5868504 * 2 ^ 59
def prefixEnd_5868504 : Nat := 4983230072969 + 3 ^ 40 * 5868504 * 2
def baseEnd_5868504 : Nat := 37202015738679168948287

theorem tailTrace_5868504 : CollatzResearch.WordTrace tailWord_5868504 prefixEnd_5868504 37202015738679168948287 := by
  unfold tailWord_5868504
  simp only [CollatzResearch.WordTrace]
  refine ⟨107020962565709871767130283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142694616754279829022840377 107020962565709871767130283)
  ·
    refine ⟨160531443848564807650695425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107020962565709871767130283 160531443848564807650695425)
    ·
      refine ⟨120398582886423605738021569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160531443848564807650695425 120398582886423605738021569)
      ·
        refine ⟨90298937164817704303516177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120398582886423605738021569 90298937164817704303516177)
        ·
          refine ⟨67724202873613278227637133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90298937164817704303516177 67724202873613278227637133)
          ·
            refine ⟨25396576077604979335363925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67724202873613278227637133 25396576077604979335363925)
            ·
              refine ⟨37202015738679168948287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25396576077604979335363925 37202015738679168948287)
              ·
                rfl

theorem cell23_5868504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 11].length) (baseStart_5868504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868504 prefixEnd_5868504 := by exact prefixLift 5868504
  have htrace : WordTrace (prefixWord ++ tailWord_5868504) baseStart_5868504 baseEnd_5868504 := by
    simpa [prefixWord, tailWord_5868504, baseEnd_5868504] using wordTrace_append hprefix tailTrace_5868504
  have hstable : (prefixWord ++ tailWord_5868504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868504).length < 2 ^ (prefixWord ++ tailWord_5868504).sum := by decide
  have hdescent : baseEnd_5868504 < baseStart_5868504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868509 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5868509 : Nat := 118140960795 + 5868509 * 2 ^ 59
def prefixEnd_5868509 : Nat := 4983230072969 + 3 ^ 40 * 5868509 * 2
def baseEnd_5868509 : Nat := 3013365842236285165248725

theorem tailTrace_5868509 : CollatzResearch.WordTrace tailWord_5868509 prefixEnd_5868509 3013365842236285165248725 := by
  unfold tailWord_5868509
  simp only [CollatzResearch.WordTrace]
  refine ⟨214042107496401629388192581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142694738330934419592128387 214042107496401629388192581)
  ·
    refine ⟨40132895155575305510286109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214042107496401629388192581 40132895155575305510286109)
    ·
      refine ⟨15049835683340739566357291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40132895155575305510286109 15049835683340739566357291)
      ·
        refine ⟨22574753525011109349535937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15049835683340739566357291 22574753525011109349535937)
        ·
          refine ⟨16931065143758332012151953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22574753525011109349535937 16931065143758332012151953)
          ·
            refine ⟨12698298857818749009113965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16931065143758332012151953 12698298857818749009113965)
            ·
              refine ⟨4761862071682030878417737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12698298857818749009113965 4761862071682030878417737)
              ·
                refine ⟨3571396553761523158813303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761862071682030878417737 3571396553761523158813303)
                ·
                  refine ⟨5357094830642284738219955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571396553761523158813303 5357094830642284738219955)
                  ·
                    refine ⟨8035642245963427107329933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357094830642284738219955 8035642245963427107329933)
                    ·
                      refine ⟨3013365842236285165248725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8035642245963427107329933 3013365842236285165248725)
                      ·
                        rfl

theorem cell23_5868509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5868509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868509 prefixEnd_5868509 := by exact prefixLift 5868509
  have htrace : WordTrace (prefixWord ++ tailWord_5868509) baseStart_5868509 baseEnd_5868509 := by
    simpa [prefixWord, tailWord_5868509, baseEnd_5868509] using wordTrace_append hprefix tailTrace_5868509
  have hstable : (prefixWord ++ tailWord_5868509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868509).length < 2 ^ (prefixWord ++ tailWord_5868509).sum := by decide
  have hdescent : baseEnd_5868509 < baseStart_5868509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868544 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_5868544 : Nat := 118140960795 + 5868544 * 2 ^ 59
def prefixEnd_5868544 : Nat := 4983230072969 + 3 ^ 40 * 5868544 * 2
def baseEnd_5868544 : Nat := 3013383814059192528311063

theorem tailTrace_5868544 : CollatzResearch.WordTrace tailWord_5868544 prefixEnd_5868544 3013383814059192528311063 := by
  unfold tailWord_5868544
  simp only [CollatzResearch.WordTrace]
  refine ⟨107021692025637415182858343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142695589367516553577144457 107021692025637415182858343)
  ·
    refine ⟨160532538038456122774287515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107021692025637415182858343 160532538038456122774287515)
    ·
      refine ⟨240798807057684184161431273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160532538038456122774287515 240798807057684184161431273)
      ·
        refine ⟨180599105293263138121073455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240798807057684184161431273 180599105293263138121073455)
        ·
          refine ⟨270898657939894707181610183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180599105293263138121073455 270898657939894707181610183)
          ·
            refine ⟨406347986909842060772415275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270898657939894707181610183 406347986909842060772415275)
            ·
              refine ⟨609521980364763091158622913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406347986909842060772415275 609521980364763091158622913)
              ·
                refine ⟨457141485273572318368967185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609521980364763091158622913 457141485273572318368967185)
                ·
                  refine ⟨342856113955179238776725389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457141485273572318368967185 342856113955179238776725389)
                  ·
                    refine ⟨128571042733192214541272021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342856113955179238776725389 128571042733192214541272021)
                    ·
                      refine ⟨3013383814059192528311063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128571042733192214541272021 3013383814059192528311063)
                      ·
                        rfl

theorem cell23_5868544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_5868544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868544 prefixEnd_5868544 := by exact prefixLift 5868544
  have htrace : WordTrace (prefixWord ++ tailWord_5868544) baseStart_5868544 baseEnd_5868544 := by
    simpa [prefixWord, tailWord_5868544, baseEnd_5868544] using wordTrace_append hprefix tailTrace_5868544
  have hstable : (prefixWord ++ tailWord_5868544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868544).length < 2 ^ (prefixWord ++ tailWord_5868544).sum := by decide
  have hdescent : baseEnd_5868544 < baseStart_5868544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868565 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_5868565 : Nat := 118140960795 + 5868565 * 2 ^ 59
def prefixEnd_5868565 : Nat := 4983230072969 + 3 ^ 40 * 5868565 * 2
def baseEnd_5868565 : Nat := 3013394597152936946148467

theorem tailTrace_5868565 : CollatzResearch.WordTrace tailWord_5868565 prefixEnd_5868565 3013394597152936946148467 := by
  unfold tailWord_5868565
  simp only [CollatzResearch.WordTrace]
  refine ⟨214044149984198750952231149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142696099989465833968154099 214044149984198750952231149)
  ·
    refine ⟨80266556244074531607086681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214044149984198750952231149 80266556244074531607086681)
    ·
      refine ⟨60199917183055898705315011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80266556244074531607086681 60199917183055898705315011)
      ·
        refine ⟨90299875774583848057972517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60199917183055898705315011 90299875774583848057972517)
        ·
          refine ⟨16931226707734471510869847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90299875774583848057972517 16931226707734471510869847)
          ·
            refine ⟨25396840061601707266304771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16931226707734471510869847 25396840061601707266304771)
            ·
              refine ⟨38095260092402560899457157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25396840061601707266304771 38095260092402560899457157)
              ·
                refine ⟨7142861267325480168648217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38095260092402560899457157 7142861267325480168648217)
                ·
                  refine ⟨5357145950494110126486163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7142861267325480168648217 5357145950494110126486163)
                  ·
                    refine ⟨8035718925741165189729245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357145950494110126486163 8035718925741165189729245)
                    ·
                      refine ⟨3013394597152936946148467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8035718925741165189729245 3013394597152936946148467)
                      ·
                        rfl

theorem cell23_5868565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_5868565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868565 prefixEnd_5868565 := by exact prefixLift 5868565
  have htrace : WordTrace (prefixWord ++ tailWord_5868565) baseStart_5868565 baseEnd_5868565 := by
    simpa [prefixWord, tailWord_5868565, baseEnd_5868565] using wordTrace_append hprefix tailTrace_5868565
  have hstable : (prefixWord ++ tailWord_5868565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868565).length < 2 ^ (prefixWord ++ tailWord_5868565).sum := by decide
  have hdescent : baseEnd_5868565 < baseStart_5868565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868581 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_5868581 : Nat := 118140960795 + 5868581 * 2 ^ 59
def prefixEnd_5868581 : Nat := 4983230072969 + 3 ^ 40 * 5868581 * 2
def baseEnd_5868581 : Nat := 1004467604281136294516131

theorem tailTrace_5868581 : CollatzResearch.WordTrace tailWord_5868581 prefixEnd_5868581 1004467604281136294516131 := by
  unfold tailWord_5868581
  simp only [CollatzResearch.WordTrace]
  refine ⟨214044733552140785684813597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142696489034760523789875731 214044733552140785684813597)
  ·
    refine ⟨80266775082052794631805099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214044733552140785684813597 80266775082052794631805099)
    ·
      refine ⟨120400162623079191947707649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80266775082052794631805099 120400162623079191947707649)
      ·
        refine ⟨90300121967309393960780737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120400162623079191947707649 90300121967309393960780737)
        ·
          refine ⟨67725091475482045470585553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90300121967309393960780737 67725091475482045470585553)
          ·
            refine ⟨50793818606611534102939165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67725091475482045470585553 50793818606611534102939165)
            ·
              refine ⟨19047681977479325288602187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50793818606611534102939165 19047681977479325288602187)
              ·
                refine ⟨28571522966218987932903281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19047681977479325288602187 28571522966218987932903281)
                ·
                  refine ⟨21428642224664240949677461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28571522966218987932903281 21428642224664240949677461)
                  ·
                    refine ⟨1004467604281136294516131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21428642224664240949677461 1004467604281136294516131)
                    ·
                      rfl

theorem cell23_5868581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_5868581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868581 prefixEnd_5868581 := by exact prefixLift 5868581
  have htrace : WordTrace (prefixWord ++ tailWord_5868581) baseStart_5868581 baseEnd_5868581 := by
    simpa [prefixWord, tailWord_5868581, baseEnd_5868581] using wordTrace_append hprefix tailTrace_5868581
  have hstable : (prefixWord ++ tailWord_5868581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868581).length < 2 ^ (prefixWord ++ tailWord_5868581).sum := by decide
  have hdescent : baseEnd_5868581 < baseStart_5868581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868605 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5868605 : Nat := 118140960795 + 5868605 * 2 ^ 59
def prefixEnd_5868605 : Nat := 4983230072969 + 3 ^ 40 * 5868605 * 2
def baseEnd_5868605 : Nat := 3013415136379116789648283

theorem tailTrace_5868605 : CollatzResearch.WordTrace tailWord_5868605 prefixEnd_5868605 3013415136379116789648283 := by
  unfold tailWord_5868605
  simp only [CollatzResearch.WordTrace]
  refine ⟨214045608904053837783687269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142697072602702558522458179 214045608904053837783687269)
  ·
    refine ⟨40133551669510094584441363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214045608904053837783687269 40133551669510094584441363)
    ·
      refine ⟨60200327504265141876662045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40133551669510094584441363 60200327504265141876662045)
      ·
        refine ⟨22575122814099428203748267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60200327504265141876662045 22575122814099428203748267)
        ·
          refine ⟨33862684221149142305622401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22575122814099428203748267 33862684221149142305622401)
          ·
            refine ⟨25397013165861856729216801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33862684221149142305622401 25397013165861856729216801)
            ·
              refine ⟨19047759874396392546912601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25397013165861856729216801 19047759874396392546912601)
              ·
                refine ⟨14285819905797294410184451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19047759874396392546912601 14285819905797294410184451)
                ·
                  refine ⟨21428729858695941615276677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14285819905797294410184451 21428729858695941615276677)
                  ·
                    refine ⟨4017886848505489052864377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21428729858695941615276677 4017886848505489052864377)
                    ·
                      refine ⟨3013415136379116789648283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4017886848505489052864377 3013415136379116789648283)
                      ·
                        rfl

theorem cell23_5868605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5868605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868605 prefixEnd_5868605 := by exact prefixLift 5868605
  have htrace : WordTrace (prefixWord ++ tailWord_5868605) baseStart_5868605 baseEnd_5868605 := by
    simpa [prefixWord, tailWord_5868605, baseEnd_5868605] using wordTrace_append hprefix tailTrace_5868605
  have hstable : (prefixWord ++ tailWord_5868605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868605).length < 2 ^ (prefixWord ++ tailWord_5868605).sum := by decide
  have hdescent : baseEnd_5868605 < baseStart_5868605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868641 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_5868641 : Nat := 118140960795 + 5868641 * 2 ^ 59
def prefixEnd_5868641 : Nat := 4983230072969 + 3 ^ 40 * 5868641 * 2
def baseEnd_5868641 : Nat := 1004477873894226216266039

theorem tailTrace_5868641 : CollatzResearch.WordTrace tailWord_5868641 prefixEnd_5868641 1004477873894226216266039 := by
  unfold tailWord_5868641
  simp only [CollatzResearch.WordTrace]
  refine ⟨214046921931923415931997777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142697947954615610621331851 214046921931923415931997777)
  ·
    refine ⟨160535191448942561948998333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214046921931923415931997777 160535191448942561948998333)
    ·
      refine ⟨60200696793353460730874375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160535191448942561948998333 60200696793353460730874375)
      ·
        refine ⟨90301045190030191096311563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60200696793353460730874375 90301045190030191096311563)
        ·
          refine ⟨135451567785045286644467345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90301045190030191096311563 135451567785045286644467345)
          ·
            refine ⟨101588675838783964983350509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135451567785045286644467345 101588675838783964983350509)
            ·
              refine ⟨38095753439543986868756441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101588675838783964983350509 38095753439543986868756441)
              ·
                refine ⟨28571815079657990151567331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38095753439543986868756441 28571815079657990151567331)
                ·
                  refine ⟨42857722619486985227350997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28571815079657990151567331 42857722619486985227350997)
                  ·
                    refine ⟨1004477873894226216266039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42857722619486985227350997 1004477873894226216266039)
                    ·
                      rfl

theorem cell23_5868641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_5868641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868641 prefixEnd_5868641 := by exact prefixLift 5868641
  have htrace : WordTrace (prefixWord ++ tailWord_5868641) baseStart_5868641 baseEnd_5868641 := by
    simpa [prefixWord, tailWord_5868641, baseEnd_5868641] using wordTrace_append hprefix tailTrace_5868641
  have hstable : (prefixWord ++ tailWord_5868641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868641).length < 2 ^ (prefixWord ++ tailWord_5868641).sum := by decide
  have hdescent : baseEnd_5868641 < baseStart_5868641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868658 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_5868658 : Nat := 118140960795 + 5868658 * 2 ^ 59
def prefixEnd_5868658 : Nat := 4983230072969 + 3 ^ 40 * 5868658 * 2
def baseEnd_5868658 : Nat := 1004480783617935027428513

theorem tailTrace_5868658 : CollatzResearch.WordTrace tailWord_5868658 prefixEnd_5868658 1004480783617935027428513 := by
  unfold tailWord_5868658
  simp only [CollatzResearch.WordTrace]
  refine ⟨53511885493215456958841657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142698361315241218556911085 53511885493215456958841657)
  ·
    refine ⟨40133914119911592719131243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53511885493215456958841657 40133914119911592719131243)
    ·
      refine ⟨60200871179867389078696865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40133914119911592719131243 60200871179867389078696865)
      ·
        refine ⟨45150653384900541809022649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60200871179867389078696865 45150653384900541809022649)
        ·
          refine ⟨33862990038675406356766987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45150653384900541809022649 33862990038675406356766987)
          ·
            refine ⟨50794485058013109535150481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33862990038675406356766987 50794485058013109535150481)
            ·
              refine ⟨38095863793509832151362861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50794485058013109535150481 38095863793509832151362861)
              ·
                refine ⟨14285948922566187056761073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38095863793509832151362861 14285948922566187056761073)
                ·
                  refine ⟨10714461691924640292570805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14285948922566187056761073 10714461691924640292570805)
                  ·
                    refine ⟨1004480783617935027428513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10714461691924640292570805 1004480783617935027428513)
                    ·
                      rfl

theorem cell23_5868658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_5868658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868658 prefixEnd_5868658 := by exact prefixLift 5868658
  have htrace : WordTrace (prefixWord ++ tailWord_5868658) baseStart_5868658 baseEnd_5868658 := by
    simpa [prefixWord, tailWord_5868658, baseEnd_5868658] using wordTrace_append hprefix tailTrace_5868658
  have hstable : (prefixWord ++ tailWord_5868658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868658).length < 2 ^ (prefixWord ++ tailWord_5868658).sum := by decide
  have hdescent : baseEnd_5868658 < baseStart_5868658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868688 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 3, 4]
def baseStart_5868688 : Nat := 118140960795 + 5868688 * 2 ^ 59
def prefixEnd_5868688 : Nat := 4983230072969 + 3 ^ 40 * 5868688 * 2
def baseEnd_5868688 : Nat := 1004485918424479988303467

theorem tailTrace_5868688 : CollatzResearch.WordTrace tailWord_5868688 prefixEnd_5868688 1004485918424479988303467 := by
  unfold tailWord_5868688
  simp only [CollatzResearch.WordTrace]
  refine ⟨107024318081376571479479359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142699090775168761972639145 107024318081376571479479359)
  ·
    refine ⟨160536477122064857219219039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107024318081376571479479359 160536477122064857219219039)
    ·
      refine ⟨240804715683097285828828559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160536477122064857219219039 240804715683097285828828559)
      ·
        refine ⟨361207073524645928743242839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240804715683097285828828559 361207073524645928743242839)
        ·
          refine ⟨541810610286968893114864259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361207073524645928743242839 541810610286968893114864259)
          ·
            refine ⟨812715915430453339672296389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541810610286968893114864259 812715915430453339672296389)
            ·
              refine ⟨152384234143210001188555573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 812715915430453339672296389 152384234143210001188555573)
              ·
                refine ⟨14286021950925937611427085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152384234143210001188555573 14286021950925937611427085)
                ·
                  refine ⟨5357258231597226604285157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14286021950925937611427085 5357258231597226604285157)
                  ·
                    refine ⟨1004485918424479988303467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357258231597226604285157 1004485918424479988303467)
                    ·
                      rfl

theorem cell23_5868688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_5868688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868688 prefixEnd_5868688 := by exact prefixLift 5868688
  have htrace : WordTrace (prefixWord ++ tailWord_5868688) baseStart_5868688 baseEnd_5868688 := by
    simpa [prefixWord, tailWord_5868688, baseEnd_5868688] using wordTrace_append hprefix tailTrace_5868688
  have hstable : (prefixWord ++ tailWord_5868688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868688).length < 2 ^ (prefixWord ++ tailWord_5868688).sum := by decide
  have hdescent : baseEnd_5868688 < baseStart_5868688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868691 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_5868691 : Nat := 118140960795 + 5868691 * 2 ^ 59
def prefixEnd_5868691 : Nat := 4983230072969 + 3 ^ 40 * 5868691 * 2
def baseEnd_5868691 : Nat := 3013459295715403453172887

theorem tailTrace_5868691 : CollatzResearch.WordTrace tailWord_5868691 prefixEnd_5868691 3013459295715403453172887 := by
  unfold tailWord_5868691
  simp only [CollatzResearch.WordTrace]
  refine ⟨214048745581742274471317927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142699163721161516314211951 214048745581742274471317927)
  ·
    refine ⟨321073118372613411706976891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214048745581742274471317927 321073118372613411706976891)
    ·
      refine ⟨481609677558920117560465337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321073118372613411706976891 481609677558920117560465337)
      ·
        refine ⟨361207258169190088170349003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481609677558920117560465337 361207258169190088170349003)
        ·
          refine ⟨541810887253785132255523505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361207258169190088170349003 541810887253785132255523505)
          ·
            refine ⟨406358165440338849191642629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541810887253785132255523505 406358165440338849191642629)
            ·
              refine ⟨76192156020063534223432993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406358165440338849191642629 76192156020063534223432993)
              ·
                refine ⟨57144117015047650667574745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76192156020063534223432993 57144117015047650667574745)
                ·
                  refine ⟨42858087761285738000681059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57144117015047650667574745 42858087761285738000681059)
                  ·
                    refine ⟨64287131641928607001021589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42858087761285738000681059 64287131641928607001021589)
                    ·
                      refine ⟨3013459295715403453172887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64287131641928607001021589 3013459295715403453172887)
                      ·
                        rfl

theorem cell23_5868691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_5868691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868691 prefixEnd_5868691 := by exact prefixLift 5868691
  have htrace : WordTrace (prefixWord ++ tailWord_5868691) baseStart_5868691 baseEnd_5868691 := by
    simpa [prefixWord, tailWord_5868691, baseEnd_5868691] using wordTrace_append hprefix tailTrace_5868691
  have hstable : (prefixWord ++ tailWord_5868691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868691).length < 2 ^ (prefixWord ++ tailWord_5868691).sum := by decide
  have hdescent : baseEnd_5868691 < baseStart_5868691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868772 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_5868772 : Nat := 118140960795 + 5868772 * 2 ^ 59
def prefixEnd_5868772 : Nat := 4983230072969 + 3 ^ 40 * 5868772 * 2
def baseEnd_5868772 : Nat := 3013500887648417636260015

theorem tailTrace_5868772 : CollatzResearch.WordTrace tailWord_5868772 prefixEnd_5868772 3013500887648417636260015 := by
  unfold tailWord_5868772
  simp only [CollatzResearch.WordTrace]
  refine ⟨107025849947224412652508285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142701133262965883536677713 107025849947224412652508285)
  ·
    refine ⟨40134693730209154744690607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107025849947224412652508285 40134693730209154744690607)
    ·
      refine ⟨60202040595313732117035911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40134693730209154744690607 60202040595313732117035911)
      ·
        refine ⟨90303060892970598175553867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60202040595313732117035911 90303060892970598175553867)
        ·
          refine ⟨135454591339455897263330801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90303060892970598175553867 135454591339455897263330801)
          ·
            refine ⟨101590943504591922947498101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135454591339455897263330801 101590943504591922947498101)
            ·
              refine ⟨9524150953555492776327947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101590943504591922947498101 9524150953555492776327947)
              ·
                refine ⟨14286226430333239164491921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9524150953555492776327947 14286226430333239164491921)
                ·
                  refine ⟨10714669822749929373368941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14286226430333239164491921 10714669822749929373368941)
                  ·
                    refine ⟨4018001183531223515013353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10714669822749929373368941 4018001183531223515013353)
                    ·
                      refine ⟨3013500887648417636260015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018001183531223515013353 3013500887648417636260015)
                      ·
                        rfl

theorem cell23_5868772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_5868772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868772 prefixEnd_5868772 := by exact prefixLift 5868772
  have htrace : WordTrace (prefixWord ++ tailWord_5868772) baseStart_5868772 baseEnd_5868772 := by
    simpa [prefixWord, tailWord_5868772, baseEnd_5868772] using wordTrace_append hprefix tailTrace_5868772
  have hstable : (prefixWord ++ tailWord_5868772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868772).length < 2 ^ (prefixWord ++ tailWord_5868772).sum := by decide
  have hdescent : baseEnd_5868772 < baseStart_5868772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868779 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 1, 1, 3]
def baseStart_5868779 : Nat := 118140960795 + 5868779 * 2 ^ 59
def prefixEnd_5868779 : Nat := 4983230072969 + 3 ^ 40 * 5868779 * 2
def baseEnd_5868779 : Nat := 3013504482012999108872483

theorem tailTrace_5868779 : CollatzResearch.WordTrace tailWord_5868779 prefixEnd_5868779 3013504482012999108872483 := by
  unfold tailWord_5868779
  simp only [CollatzResearch.WordTrace]
  refine ⟨214051955205423465500521391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142701303470282310333680927 214051955205423465500521391)
  ·
    refine ⟨321077932808135198250782087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214051955205423465500521391 321077932808135198250782087)
    ·
      refine ⟨481616899212202797376173131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321077932808135198250782087 481616899212202797376173131)
      ·
        refine ⟨722425348818304196064259697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481616899212202797376173131 722425348818304196064259697)
        ·
          refine ⟨541819011613728147048194773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722425348818304196064259697 541819011613728147048194773)
          ·
            refine ⟨12698883084696753446442065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 541819011613728147048194773 12698883084696753446442065)
            ·
              refine ⟨9524162313522565084831549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12698883084696753446442065 9524162313522565084831549)
              ·
                refine ⟨3571560867570961906811831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9524162313522565084831549 3571560867570961906811831)
                ·
                  refine ⟨5357341301356442860217747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571560867570961906811831 5357341301356442860217747)
                  ·
                    refine ⟨8036011952034664290326621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357341301356442860217747 8036011952034664290326621)
                    ·
                      refine ⟨3013504482012999108872483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036011952034664290326621 3013504482012999108872483)
                      ·
                        rfl

theorem cell23_5868779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 1, 1, 3].length) (baseStart_5868779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868779 prefixEnd_5868779 := by exact prefixLift 5868779
  have htrace : WordTrace (prefixWord ++ tailWord_5868779) baseStart_5868779 baseEnd_5868779 := by
    simpa [prefixWord, tailWord_5868779, baseEnd_5868779] using wordTrace_append hprefix tailTrace_5868779
  have hstable : (prefixWord ++ tailWord_5868779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868779).length < 2 ^ (prefixWord ++ tailWord_5868779).sum := by decide
  have hdescent : baseEnd_5868779 < baseStart_5868779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868782 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_5868782 : Nat := 118140960795 + 5868782 * 2 ^ 59
def prefixEnd_5868782 : Nat := 4983230072969 + 3 ^ 40 * 5868782 * 2
def baseEnd_5868782 : Nat := 1004502007484987532378323

theorem tailTrace_5868782 : CollatzResearch.WordTrace tailWord_5868782 prefixEnd_5868782 1004502007484987532378323 := by
  unfold tailWord_5868782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26756508078051574626610075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142701376416275064675253733 26756508078051574626610075)
  ·
    refine ⟨40134762117077361939915113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26756508078051574626610075 40134762117077361939915113)
    ·
      refine ⟨30101071587808021454936335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40134762117077361939915113 30101071587808021454936335)
      ·
        refine ⟨45151607381712032182404503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30101071587808021454936335 45151607381712032182404503)
        ·
          refine ⟨67727411072568048273606755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45151607381712032182404503 67727411072568048273606755)
          ·
            refine ⟨101591116608852072410410133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67727411072568048273606755 101591116608852072410410133)
            ·
              refine ⟨4762083591039940894237975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101591116608852072410410133 4762083591039940894237975)
              ·
                refine ⟨7143125386559911341356963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762083591039940894237975 7143125386559911341356963)
                ·
                  refine ⟨10714688079839867012035445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143125386559911341356963 10714688079839867012035445)
                  ·
                    refine ⟨1004502007484987532378323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10714688079839867012035445 1004502007484987532378323)
                    ·
                      rfl

theorem cell23_5868782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_5868782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868782 prefixEnd_5868782 := by exact prefixLift 5868782
  have htrace : WordTrace (prefixWord ++ tailWord_5868782) baseStart_5868782 baseEnd_5868782 := by
    simpa [prefixWord, tailWord_5868782, baseEnd_5868782] using wordTrace_append hprefix tailTrace_5868782
  have hstable : (prefixWord ++ tailWord_5868782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868782).length < 2 ^ (prefixWord ++ tailWord_5868782).sum := by decide
  have hdescent : baseEnd_5868782 < baseStart_5868782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868830 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5868830 : Nat := 118140960795 + 5868830 * 2 ^ 59
def prefixEnd_5868830 : Nat := 4983230072969 + 3 ^ 40 * 5868830 * 2
def baseEnd_5868830 : Nat := 3013530669526378409334749

theorem tailTrace_5868830 : CollatzResearch.WordTrace tailWord_5868830 prefixEnd_5868830 3013530669526378409334749 := by
  unfold tailWord_5868830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26756726916029837651328493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142702543552159134140418629 26756726916029837651328493)
  ·
    refine ⟨10033772593511189119248185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26756726916029837651328493 10033772593511189119248185)
    ·
      refine ⟨7525329445133391839436139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10033772593511189119248185 7525329445133391839436139)
      ·
        refine ⟨11287994167700087759154209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7525329445133391839436139 11287994167700087759154209)
        ·
          refine ⟨8465995625775065819365657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11287994167700087759154209 8465995625775065819365657)
          ·
            refine ⟨6349496719331299364524243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8465995625775065819365657 6349496719331299364524243)
            ·
              refine ⟨9524245078996949046786365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349496719331299364524243 9524245078996949046786365)
              ·
                refine ⟨3571591904623855892544887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9524245078996949046786365 3571591904623855892544887)
                ·
                  refine ⟨5357387856935783838817331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571591904623855892544887 5357387856935783838817331)
                  ·
                    refine ⟨8036081785403675758225997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357387856935783838817331 8036081785403675758225997)
                    ·
                      refine ⟨3013530669526378409334749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036081785403675758225997 3013530669526378409334749)
                      ·
                        rfl

theorem cell23_5868830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5868830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868830 prefixEnd_5868830 := by exact prefixLift 5868830
  have htrace : WordTrace (prefixWord ++ tailWord_5868830) baseStart_5868830 baseEnd_5868830 := by
    simpa [prefixWord, tailWord_5868830, baseEnd_5868830] using wordTrace_append hprefix tailTrace_5868830
  have hstable : (prefixWord ++ tailWord_5868830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868830).length < 2 ^ (prefixWord ++ tailWord_5868830).sum := by decide
  have hdescent : baseEnd_5868830 < baseStart_5868830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868848 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_5868848 : Nat := 118140960795 + 5868848 * 2 ^ 59
def prefixEnd_5868848 : Nat := 4983230072969 + 3 ^ 40 * 5868848 * 2
def baseEnd_5868848 : Nat := 3013539912178159338909665

theorem tailTrace_5868848 : CollatzResearch.WordTrace tailWord_5868848 prefixEnd_5868848 3013539912178159338909665 := by
  unfold tailWord_5868848
  simp only [CollatzResearch.WordTrace]
  refine ⟨107027235921086745142391599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142702981228115660189855465 107027235921086745142391599)
  ·
    refine ⟨160540853881630117713587399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107027235921086745142391599 160540853881630117713587399)
    ·
      refine ⟨240811280822445176570381099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160540853881630117713587399 240811280822445176570381099)
      ·
        refine ⟨361216921233667764855571649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240811280822445176570381099 361216921233667764855571649)
        ·
          refine ⟨270912690925250823641678737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361216921233667764855571649 270912690925250823641678737)
          ·
            refine ⟨203184518193938117731259053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270912690925250823641678737 203184518193938117731259053)
            ·
              refine ⟨76194194322726794149222145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203184518193938117731259053 76194194322726794149222145)
              ·
                refine ⟨57145645742045095611916609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76194194322726794149222145 57145645742045095611916609)
                ·
                  refine ⟨42859234306533821708937457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57145645742045095611916609 42859234306533821708937457)
                  ·
                    refine ⟨32144425729900366281703093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42859234306533821708937457 32144425729900366281703093)
                    ·
                      refine ⟨3013539912178159338909665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32144425729900366281703093 3013539912178159338909665)
                      ·
                        rfl

theorem cell23_5868848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_5868848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868848 prefixEnd_5868848 := by exact prefixLift 5868848
  have htrace : WordTrace (prefixWord ++ tailWord_5868848) baseStart_5868848 baseEnd_5868848 := by
    simpa [prefixWord, tailWord_5868848, baseEnd_5868848] using wordTrace_append hprefix tailTrace_5868848
  have hstable : (prefixWord ++ tailWord_5868848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868848).length < 2 ^ (prefixWord ++ tailWord_5868848).sum := by decide
  have hdescent : baseEnd_5868848 < baseStart_5868848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868853 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_5868853 : Nat := 118140960795 + 5868853 * 2 ^ 59
def prefixEnd_5868853 : Nat := 4983230072969 + 3 ^ 40 * 5868853 * 2
def baseEnd_5868853 : Nat := 3013542479581431819347143

theorem tailTrace_5868853 : CollatzResearch.WordTrace tailWord_5868853 prefixEnd_5868853 3013542479581431819347143 := by
  unfold tailWord_5868853
  simp only [CollatzResearch.WordTrace]
  refine ⟨214054654207155376138715213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142703102804770250759143475 214054654207155376138715213)
  ·
    refine ⟨80270495327683266052018205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214054654207155376138715213 80270495327683266052018205)
    ·
      refine ⟨30101435747881224769506827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80270495327683266052018205 30101435747881224769506827)
      ·
        refine ⟨45152153621821837154260241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30101435747881224769506827 45152153621821837154260241)
        ·
          refine ⟨33864115216366377865695181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45152153621821837154260241 33864115216366377865695181)
          ·
            refine ⟨12699043206137391699635693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33864115216366377865695181 12699043206137391699635693)
            ·
              refine ⟨4762141202301521887363385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12699043206137391699635693 4762141202301521887363385)
              ·
                refine ⟨3571605901726141415522539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762141202301521887363385 3571605901726141415522539)
                ·
                  refine ⟨5357408852589212123283809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571605901726141415522539 5357408852589212123283809)
                  ·
                    refine ⟨4018056639441909092462857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5357408852589212123283809 4018056639441909092462857)
                    ·
                      refine ⟨3013542479581431819347143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018056639441909092462857 3013542479581431819347143)
                      ·
                        rfl

theorem cell23_5868853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_5868853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868853 prefixEnd_5868853 := by exact prefixLift 5868853
  have htrace : WordTrace (prefixWord ++ tailWord_5868853) baseStart_5868853 baseEnd_5868853 := by
    simpa [prefixWord, tailWord_5868853, baseEnd_5868853] using wordTrace_append hprefix tailTrace_5868853
  have hstable : (prefixWord ++ tailWord_5868853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868853).length < 2 ^ (prefixWord ++ tailWord_5868853).sum := by decide
  have hdescent : baseEnd_5868853 < baseStart_5868853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868870 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5868870 : Nat := 118140960795 + 5868870 * 2 ^ 59
def prefixEnd_5868870 : Nat := 4983230072969 + 3 ^ 40 * 5868870 * 2
def baseEnd_5868870 : Nat := 3013551208752558252834565

theorem tailTrace_5868870 : CollatzResearch.WordTrace tailWord_5868870 prefixEnd_5868870 3013551208752558252834565 := by
  unfold tailWord_5868870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689227320252930876315127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142703516165395858694722709 6689227320252930876315127)
  ·
    refine ⟨10033840980379396314472691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6689227320252930876315127 10033840980379396314472691)
    ·
      refine ⟨15050761470569094471709037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10033840980379396314472691 15050761470569094471709037)
      ·
        refine ⟨5644035551463410426890889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15050761470569094471709037 5644035551463410426890889)
        ·
          refine ⟨4233026663597557820168167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5644035551463410426890889 4233026663597557820168167)
          ·
            refine ⟨6349539995396336730252251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233026663597557820168167 6349539995396336730252251)
            ·
              refine ⟨9524309993094505095378377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349539995396336730252251 9524309993094505095378377)
              ·
                refine ⟨7143232494820878821533783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9524309993094505095378377 7143232494820878821533783)
                ·
                  refine ⟨10714848742231318232300675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143232494820878821533783 10714848742231318232300675)
                  ·
                    refine ⟨16072273113346977348451013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10714848742231318232300675 16072273113346977348451013)
                    ·
                      refine ⟨3013551208752558252834565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16072273113346977348451013 3013551208752558252834565)
                      ·
                        rfl

theorem cell23_5868870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5868870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868870 prefixEnd_5868870 := by exact prefixLift 5868870
  have htrace : WordTrace (prefixWord ++ tailWord_5868870) baseStart_5868870 baseEnd_5868870 := by
    simpa [prefixWord, tailWord_5868870, baseEnd_5868870] using wordTrace_append hprefix tailTrace_5868870
  have hstable : (prefixWord ++ tailWord_5868870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868870).length < 2 ^ (prefixWord ++ tailWord_5868870).sum := by decide
  have hdescent : baseEnd_5868870 < baseStart_5868870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868896 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 1, 3, 2]
def baseStart_5868896 : Nat := 118140960795 + 5868896 * 2 ^ 59
def prefixEnd_5868896 : Nat := 4983230072969 + 3 ^ 40 * 5868896 * 2
def baseEnd_5868896 : Nat := 3013564559249575151109445

theorem tailTrace_5868896 : CollatzResearch.WordTrace tailWord_5868896 prefixEnd_5868896 3013564559249575151109445 := by
  unfold tailWord_5868896
  simp only [CollatzResearch.WordTrace]
  refine ⟨107028111272999797241265271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142704148363999729655020361 107028111272999797241265271)
  ·
    refine ⟨160542166909499695861897907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107028111272999797241265271 160542166909499695861897907)
    ·
      refine ⟨240813250364249543792846861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160542166909499695861897907 240813250364249543792846861)
      ·
        refine ⟨90304968886593578922317573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240813250364249543792846861 90304968886593578922317573)
        ·
          refine ⟨16932181666236296047934545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90304968886593578922317573 16932181666236296047934545)
          ·
            refine ⟨12699136249677222035950909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16932181666236296047934545 12699136249677222035950909)
            ·
              refine ⟨4762176093628958263481591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12699136249677222035950909 4762176093628958263481591)
              ·
                refine ⟨7143264140443437395222387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762176093628958263481591 7143264140443437395222387)
                ·
                  refine ⟨10714896210665156092833581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143264140443437395222387 10714896210665156092833581)
                  ·
                    refine ⟨4018086078999433534812593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10714896210665156092833581 4018086078999433534812593)
                    ·
                      refine ⟨3013564559249575151109445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018086078999433534812593 3013564559249575151109445)
                      ·
                        rfl

theorem cell23_5868896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_5868896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868896 prefixEnd_5868896 := by exact prefixLift 5868896
  have htrace : WordTrace (prefixWord ++ tailWord_5868896) baseStart_5868896 baseEnd_5868896 := by
    simpa [prefixWord, tailWord_5868896, baseEnd_5868896] using wordTrace_append hprefix tailTrace_5868896
  have hstable : (prefixWord ++ tailWord_5868896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868896).length < 2 ^ (prefixWord ++ tailWord_5868896).sum := by decide
  have hdescent : baseEnd_5868896 < baseStart_5868896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5868992 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 3, 4]
def baseStart_5868992 : Nat := 118140960795 + 5868992 * 2 ^ 59
def prefixEnd_5868992 : Nat := 4983230072969 + 3 ^ 40 * 5868992 * 2
def baseEnd_5868992 : Nat := 1004537951130802258503001

theorem tailTrace_5868992 : CollatzResearch.WordTrace tailWord_5868992 prefixEnd_5868992 1004537951130802258503001 := by
  unfold tailWord_5868992
  simp only [CollatzResearch.WordTrace]
  refine ⟨107029861976825901439012615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142706482635767868585350153 107029861976825901439012615)
  ·
    refine ⟨160544792965238852158518923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107029861976825901439012615 160544792965238852158518923)
    ·
      refine ⟨240817189447858278237778385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160544792965238852158518923 240817189447858278237778385)
      ·
        refine ⟨180612892085893708678333789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240817189447858278237778385 180612892085893708678333789)
        ·
          refine ⟨67729834532210140754375171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180612892085893708678333789 67729834532210140754375171)
          ·
            refine ⟨101594751798315211131562757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67729834532210140754375171 101594751798315211131562757)
            ·
              refine ⟨19049015962184102087168017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101594751798315211131562757 19049015962184102087168017)
              ·
                refine ⟨14286761971638076565376013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19049015962184102087168017 14286761971638076565376013)
                ·
                  refine ⟨5357535739364278712016005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14286761971638076565376013 5357535739364278712016005)
                  ·
                    refine ⟨1004537951130802258503001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357535739364278712016005 1004537951130802258503001)
                    ·
                      rfl

theorem cell23_5868992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_5868992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5868992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5868992 prefixEnd_5868992 := by exact prefixLift 5868992
  have htrace : WordTrace (prefixWord ++ tailWord_5868992) baseStart_5868992 baseEnd_5868992 := by
    simpa [prefixWord, tailWord_5868992, baseEnd_5868992] using wordTrace_append hprefix tailTrace_5868992
  have hstable : (prefixWord ++ tailWord_5868992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5868992).length < 2 ^ (prefixWord ++ tailWord_5868992).sum := by decide
  have hdescent : baseEnd_5868992 < baseStart_5868992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5868992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869002 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_5869002 : Nat := 118140960795 + 5869002 * 2 ^ 59
def prefixEnd_5869002 : Nat := 4983230072969 + 3 ^ 40 * 5869002 * 2
def baseEnd_5869002 : Nat := 3013618988198951736383957

theorem tailTrace_5869002 : CollatzResearch.WordTrace tailWord_5869002 prefixEnd_5869002 3013618988198951736383957 := by
  unfold tailWord_5869002
  simp only [CollatzResearch.WordTrace]
  refine ⟨53515022170903893646472315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142706725789077049723926173 53515022170903893646472315)
  ·
    refine ⟨80272533256355840469708473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53515022170903893646472315 80272533256355840469708473)
    ·
      refine ⟨60204399942266880352281355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80272533256355840469708473 60204399942266880352281355)
      ·
        refine ⟨90306599913400320528422033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60204399942266880352281355 90306599913400320528422033)
        ·
          refine ⟨67729949935050240396316525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90306599913400320528422033 67729949935050240396316525)
          ·
            refine ⟨25398731225643840148618697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67729949935050240396316525 25398731225643840148618697)
            ·
              refine ⟨19049048419232880111464023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25398731225643840148618697 19049048419232880111464023)
              ·
                refine ⟨28573572628849320167196035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19049048419232880111464023 28573572628849320167196035)
                ·
                  refine ⟨42860358943273980250794053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28573572628849320167196035 42860358943273980250794053)
                  ·
                    refine ⟨8036317301863871297023885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42860358943273980250794053 8036317301863871297023885)
                    ·
                      refine ⟨3013618988198951736383957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036317301863871297023885 3013618988198951736383957)
                      ·
                        rfl

theorem cell23_5869002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_5869002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869002 prefixEnd_5869002 := by exact prefixLift 5869002
  have htrace : WordTrace (prefixWord ++ tailWord_5869002) baseStart_5869002 baseEnd_5869002 := by
    simpa [prefixWord, tailWord_5869002, baseEnd_5869002] using wordTrace_append hprefix tailTrace_5869002
  have hstable : (prefixWord ++ tailWord_5869002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869002).length < 2 ^ (prefixWord ++ tailWord_5869002).sum := by decide
  have hdescent : baseEnd_5869002 < baseStart_5869002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869109 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_5869109 : Nat := 118140960795 + 5869109 * 2 ^ 59
def prefixEnd_5869109 : Nat := 4983230072969 + 3 ^ 40 * 5869109 * 2
def baseEnd_5869109 : Nat := 3013673930628982817745965

theorem tailTrace_5869109 : CollatzResearch.WordTrace tailWord_5869109 prefixEnd_5869109 3013673930628982817745965 := by
  unfold tailWord_5869109
  simp only [CollatzResearch.WordTrace]
  refine ⟨214063991294227931860034381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142709327529485287906689587 214063991294227931860034381)
  ·
    refine ⟨80273996735335474447512893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214063991294227931860034381 80273996735335474447512893)
    ·
      refine ⟨30102748775750802917817335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80273996735335474447512893 30102748775750802917817335)
      ·
        refine ⟨45154123163626204376726003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30102748775750802917817335 45154123163626204376726003)
        ·
          refine ⟨67731184745439306565089005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45154123163626204376726003 67731184745439306565089005)
          ·
            refine ⟨25399194279539739961908377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67731184745439306565089005 25399194279539739961908377)
            ·
              refine ⟨19049395709654804971431283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25399194279539739961908377 19049395709654804971431283)
              ·
                refine ⟨28574093564482207457146925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19049395709654804971431283 28574093564482207457146925)
                ·
                  refine ⟨10715285086680827796430097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28574093564482207457146925 10715285086680827796430097)
                  ·
                    refine ⟨8036463815010620847322573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10715285086680827796430097 8036463815010620847322573)
                    ·
                      refine ⟨3013673930628982817745965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036463815010620847322573 3013673930628982817745965)
                      ·
                        rfl

theorem cell23_5869109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_5869109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869109 prefixEnd_5869109 := by exact prefixLift 5869109
  have htrace : WordTrace (prefixWord ++ tailWord_5869109) baseStart_5869109 baseEnd_5869109 := by
    simpa [prefixWord, tailWord_5869109, baseEnd_5869109] using wordTrace_append hprefix tailTrace_5869109
  have hstable : (prefixWord ++ tailWord_5869109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869109).length < 2 ^ (prefixWord ++ tailWord_5869109).sum := by decide
  have hdescent : baseEnd_5869109 < baseStart_5869109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869110 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_5869110 : Nat := 118140960795 + 5869110 * 2 ^ 59
def prefixEnd_5869110 : Nat := 4983230072969 + 3 ^ 40 * 5869110 * 2
def baseEnd_5869110 : Nat := 3013674444109637313833461

theorem tailTrace_5869110 : CollatzResearch.WordTrace tailWord_5869110 prefixEnd_5869110 3013674444109637313833461 := by
  unfold tailWord_5869110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379001735451519314426299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142709351844816206020547189 13379001735451519314426299)
  ·
    refine ⟨20068502603177278971639449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13379001735451519314426299 20068502603177278971639449)
    ·
      refine ⟨15051376952382959228729587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20068502603177278971639449 15051376952382959228729587)
      ·
        refine ⟨22577065428574438843094381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15051376952382959228729587 22577065428574438843094381)
        ·
          refine ⟨8466399535715414566160393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22577065428574438843094381 8466399535715414566160393)
          ·
            refine ⟨6349799651786560924620295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8466399535715414566160393 6349799651786560924620295)
            ·
              refine ⟨9524699477679841386930443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349799651786560924620295 9524699477679841386930443)
              ·
                refine ⟨14287049216519762080395665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9524699477679841386930443 14287049216519762080395665)
                ·
                  refine ⟨10715286912389821560296749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14287049216519762080395665 10715286912389821560296749)
                  ·
                    refine ⟨4018232592146183085111281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10715286912389821560296749 4018232592146183085111281)
                    ·
                      refine ⟨3013674444109637313833461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018232592146183085111281 3013674444109637313833461)
                      ·
                        rfl

theorem cell23_5869110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_5869110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869110 prefixEnd_5869110 := by exact prefixLift 5869110
  have htrace : WordTrace (prefixWord ++ tailWord_5869110) baseStart_5869110 baseEnd_5869110 := by
    simpa [prefixWord, tailWord_5869110, baseEnd_5869110] using wordTrace_append hprefix tailTrace_5869110
  have hstable : (prefixWord ++ tailWord_5869110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869110).length < 2 ^ (prefixWord ++ tailWord_5869110).sum := by decide
  have hdescent : baseEnd_5869110 < baseStart_5869110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869156 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_5869156 : Nat := 118140960795 + 5869156 * 2 ^ 59
def prefixEnd_5869156 : Nat := 4983230072969 + 3 ^ 40 * 5869156 * 2
def baseEnd_5869156 : Nat := 3013698064219744133858249

theorem tailTrace_5869156 : CollatzResearch.WordTrace tailWord_5869156 prefixEnd_5869156 3013698064219744133858249 := by
  unfold tailWord_5869156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107032852762528829443497661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142710470350038439257996881 107032852762528829443497661)
  ·
    refine ⟨40137319785948311041311623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107032852762528829443497661 40137319785948311041311623)
    ·
      refine ⟨60205979678922466561967435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40137319785948311041311623 60205979678922466561967435)
      ·
        refine ⟨90308969518383699842951153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60205979678922466561967435 90308969518383699842951153)
        ·
          refine ⟨67731727138787774882213365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90308969518383699842951153 67731727138787774882213365)
          ·
            refine ⟨6349849419261353895207503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67731727138787774882213365 6349849419261353895207503)
            ·
              refine ⟨9524774128892030842811255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349849419261353895207503 9524774128892030842811255)
              ·
                refine ⟨14287161193338046264216883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9524774128892030842811255 14287161193338046264216883)
                ·
                  refine ⟨21430741790007069396325325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14287161193338046264216883 21430741790007069396325325)
                  ·
                    refine ⟨8036528171252651023621997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21430741790007069396325325 8036528171252651023621997)
                    ·
                      refine ⟨3013698064219744133858249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036528171252651023621997 3013698064219744133858249)
                      ·
                        rfl

theorem cell23_5869156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_5869156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869156 prefixEnd_5869156 := by exact prefixLift 5869156
  have htrace : WordTrace (prefixWord ++ tailWord_5869156) baseStart_5869156 baseEnd_5869156 := by
    simpa [prefixWord, tailWord_5869156, baseEnd_5869156] using wordTrace_append hprefix tailTrace_5869156
  have hstable : (prefixWord ++ tailWord_5869156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869156).length < 2 ^ (prefixWord ++ tailWord_5869156).sum := by decide
  have hdescent : baseEnd_5869156 < baseStart_5869156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869179 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 3, 4, 2]
def baseStart_5869179 : Nat := 118140960795 + 5869179 * 2 ^ 59
def prefixEnd_5869179 : Nat := 4983230072969 + 3 ^ 40 * 5869179 * 2
def baseEnd_5869179 : Nat := 3013709874274797543870643

theorem tailTrace_5869179 : CollatzResearch.WordTrace tailWord_5869179 prefixEnd_5869179 3013709874274797543870643 := by
  unfold tailWord_5869179
  simp only [CollatzResearch.WordTrace]
  refine ⟨214066544403974333815082591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142711029602649555876721727 214066544403974333815082591)
  ·
    refine ⟨321099816605961500722623887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214066544403974333815082591 321099816605961500722623887)
    ·
      refine ⟨481649724908942251083935831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321099816605961500722623887 481649724908942251083935831)
      ·
        refine ⟨722474587363413376625903747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481649724908942251083935831 722474587363413376625903747)
        ·
          refine ⟨1083711881045120064938855621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722474587363413376625903747 1083711881045120064938855621)
          ·
            refine ⟨203195977695960012176035429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1083711881045120064938855621 203195977695960012176035429)
            ·
              refine ⟨38099245817992502283006643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203195977695960012176035429 38099245817992502283006643)
              ·
                refine ⟨57148868726988753424509965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38099245817992502283006643 57148868726988753424509965)
                ·
                  refine ⟨21430825772620782534191237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57148868726988753424509965 21430825772620782534191237)
                  ·
                    refine ⟨4018279832366396725160857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21430825772620782534191237 4018279832366396725160857)
                    ·
                      refine ⟨3013709874274797543870643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018279832366396725160857 3013709874274797543870643)
                      ·
                        rfl

theorem cell23_5869179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4, 2].length) (baseStart_5869179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869179 prefixEnd_5869179 := by exact prefixLift 5869179
  have htrace : WordTrace (prefixWord ++ tailWord_5869179) baseStart_5869179 baseEnd_5869179 := by
    simpa [prefixWord, tailWord_5869179, baseEnd_5869179] using wordTrace_append hprefix tailTrace_5869179
  have hstable : (prefixWord ++ tailWord_5869179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869179).length < 2 ^ (prefixWord ++ tailWord_5869179).sum := by decide
  have hdescent : baseEnd_5869179 < baseStart_5869179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869196 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 4, 2, 2]
def baseStart_5869196 : Nat := 118140960795 + 5869196 * 2 ^ 59
def prefixEnd_5869196 : Nat := 4983230072969 + 3 ^ 40 * 5869196 * 2
def baseEnd_5869196 : Nat := 3013718603445923977358065

theorem tailTrace_5869196 : CollatzResearch.WordTrace tailWord_5869196 prefixEnd_5869196 3013718603445923977358065 := by
  unfold tailWord_5869196
  simp only [CollatzResearch.WordTrace]
  refine ⟨107033582222456372859225721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142711442963275163812300961 107033582222456372859225721)
  ·
    refine ⟨80275186666842279644419291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107033582222456372859225721 80275186666842279644419291)
    ·
      refine ⟨120412780000263419466628937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80275186666842279644419291 120412780000263419466628937)
      ·
        refine ⟨90309585000197564599971703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120412780000263419466628937 90309585000197564599971703)
        ·
          refine ⟨135464377500296346899957555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90309585000197564599971703 135464377500296346899957555)
          ·
            refine ⟨203196566250444520349936333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135464377500296346899957555 203196566250444520349936333)
            ·
              refine ⟨76198712343916695131226125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203196566250444520349936333 76198712343916695131226125)
              ·
                refine ⟨28574517128968760674209797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76198712343916695131226125 28574517128968760674209797)
                ·
                  refine ⟨5357721961681642626414337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28574517128968760674209797 5357721961681642626414337)
                  ·
                    refine ⟨4018291471261231969810753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5357721961681642626414337 4018291471261231969810753)
                    ·
                      refine ⟨3013718603445923977358065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018291471261231969810753 3013718603445923977358065)
                      ·
                        rfl

theorem cell23_5869196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_5869196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869196 prefixEnd_5869196 := by exact prefixLift 5869196
  have htrace : WordTrace (prefixWord ++ tailWord_5869196) baseStart_5869196 baseEnd_5869196 := by
    simpa [prefixWord, tailWord_5869196, baseEnd_5869196] using wordTrace_append hprefix tailTrace_5869196
  have hstable : (prefixWord ++ tailWord_5869196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869196).length < 2 ^ (prefixWord ++ tailWord_5869196).sum := by decide
  have hdescent : baseEnd_5869196 < baseStart_5869196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869230 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5869230 : Nat := 118140960795 + 5869230 * 2 ^ 59
def prefixEnd_5869230 : Nat := 4983230072969 + 3 ^ 40 * 5869230 * 2
def baseEnd_5869230 : Nat := 3013736061788176844332909

theorem tailTrace_5869230 : CollatzResearch.WordTrace tailWord_5869230 prefixEnd_5869230 3013736061788176844332909 := by
  unfold tailWord_5869230
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758550565848696190648643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142712269684526379683459429 26758550565848696190648643)
  ·
    refine ⟨40137825848773044285972965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26758550565848696190648643 40137825848773044285972965)
    ·
      refine ⟨7525842346644945803619931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40137825848773044285972965 7525842346644945803619931)
      ·
        refine ⟨11288763519967418705429897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7525842346644945803619931 11288763519967418705429897)
        ·
          refine ⟨8466572639975564029072423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11288763519967418705429897 8466572639975564029072423)
          ·
            refine ⟨12699858959963346043608635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8466572639975564029072423 12699858959963346043608635)
            ·
              refine ⟨19049788439945019065412953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12699858959963346043608635 19049788439945019065412953)
              ·
                refine ⟨14287341329958764299059715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19049788439945019065412953 14287341329958764299059715)
                ·
                  refine ⟨21431011994938146448589573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14287341329958764299059715 21431011994938146448589573)
                  ·
                    refine ⟨4018314749050902459110545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21431011994938146448589573 4018314749050902459110545)
                    ·
                      refine ⟨3013736061788176844332909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018314749050902459110545 3013736061788176844332909)
                      ·
                        rfl

theorem cell23_5869230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5869230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869230 prefixEnd_5869230 := by exact prefixLift 5869230
  have htrace : WordTrace (prefixWord ++ tailWord_5869230) baseStart_5869230 baseEnd_5869230 := by
    simpa [prefixWord, tailWord_5869230, baseEnd_5869230] using wordTrace_append hprefix tailTrace_5869230
  have hstable : (prefixWord ++ tailWord_5869230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869230).length < 2 ^ (prefixWord ++ tailWord_5869230).sum := by decide
  have hdescent : baseEnd_5869230 < baseStart_5869230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869232 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_5869232 : Nat := 118140960795 + 5869232 * 2 ^ 59
def prefixEnd_5869232 : Nat := 4983230072969 + 3 ^ 40 * 5869232 * 2
def baseEnd_5869232 : Nat := 1004579029583161945502633

theorem tailTrace_5869232 : CollatzResearch.WordTrace tailWord_5869232 prefixEnd_5869232 1004579029583161945502633 := by
  unfold tailWord_5869232
  simp only [CollatzResearch.WordTrace]
  refine ⟨107034238736391161933380975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142712318315188215911174633 107034238736391161933380975)
  ·
    refine ⟨160551358104586742900071463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107034238736391161933380975 160551358104586742900071463)
    ·
      refine ⟨240827037156880114350107195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160551358104586742900071463 240827037156880114350107195)
      ·
        refine ⟨361240555735320171525160793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240827037156880114350107195 361240555735320171525160793)
        ·
          refine ⟨270930416801490128643870595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361240555735320171525160793 270930416801490128643870595)
          ·
            refine ⟨406395625202235192965805893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270930416801490128643870595 406395625202235192965805893)
            ·
              refine ⟨76199179725419098681088605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406395625202235192965805893 76199179725419098681088605)
              ·
                refine ⟨28574692397032162005408227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76199179725419098681088605 28574692397032162005408227)
                ·
                  refine ⟨42862038595548243008112341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28574692397032162005408227 42862038595548243008112341)
                  ·
                    refine ⟨1004579029583161945502633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42862038595548243008112341 1004579029583161945502633)
                    ·
                      rfl

theorem cell23_5869232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_5869232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869232 prefixEnd_5869232 := by exact prefixLift 5869232
  have htrace : WordTrace (prefixWord ++ tailWord_5869232) baseStart_5869232 baseEnd_5869232 := by
    simpa [prefixWord, tailWord_5869232, baseEnd_5869232] using wordTrace_append hprefix tailTrace_5869232
  have hstable : (prefixWord ++ tailWord_5869232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869232).length < 2 ^ (prefixWord ++ tailWord_5869232).sum := by decide
  have hdescent : baseEnd_5869232 < baseStart_5869232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869283 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 2, 5]
def baseStart_5869283 : Nat := 118140960795 + 5869283 * 2 ^ 59
def prefixEnd_5869283 : Nat := 4983230072969 + 3 ^ 40 * 5869283 * 2
def baseEnd_5869283 : Nat := 1004587758754288378990055

theorem tailTrace_5869283 : CollatzResearch.WordTrace tailWord_5869283 prefixEnd_5869283 1004587758754288378990055 := by
  unfold tailWord_5869283
  simp only [CollatzResearch.WordTrace]
  refine ⟨214070337595597559576868503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142713558397065039717912335 214070337595597559576868503)
  ·
    refine ⟨321105506393396339365302755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214070337595597559576868503 321105506393396339365302755)
    ·
      refine ⟨481658259590094509047954133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321105506393396339365302755 481658259590094509047954133)
      ·
        refine ⟨11288865459142840055811425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 481658259590094509047954133 11288865459142840055811425)
        ·
          refine ⟨8466649094357130041858569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11288865459142840055811425 8466649094357130041858569)
          ·
            refine ⟨6349986820767847531393927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8466649094357130041858569 6349986820767847531393927)
            ·
              refine ⟨9524980231151771297090891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349986820767847531393927 9524980231151771297090891)
              ·
                refine ⟨14287470346727656945636337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9524980231151771297090891 14287470346727656945636337)
                ·
                  refine ⟨10715602760045742709227253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14287470346727656945636337 10715602760045742709227253)
                  ·
                    refine ⟨1004587758754288378990055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10715602760045742709227253 1004587758754288378990055)
                    ·
                      rfl

theorem cell23_5869283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 5].length) (baseStart_5869283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869283 prefixEnd_5869283 := by exact prefixLift 5869283
  have htrace : WordTrace (prefixWord ++ tailWord_5869283) baseStart_5869283 baseEnd_5869283 := by
    simpa [prefixWord, tailWord_5869283, baseEnd_5869283] using wordTrace_append hprefix tailTrace_5869283
  have hstable : (prefixWord ++ tailWord_5869283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869283).length < 2 ^ (prefixWord ++ tailWord_5869283).sum := by decide
  have hdescent : baseEnd_5869283 < baseStart_5869283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869309 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 6]
def baseStart_5869309 : Nat := 118140960795 + 5869309 * 2 ^ 59
def prefixEnd_5869309 : Nat := 4983230072969 + 3 ^ 40 * 5869309 * 2
def baseEnd_5869309 : Nat := 334864069639986892805005

theorem tailTrace_5869309 : CollatzResearch.WordTrace tailWord_5869309 prefixEnd_5869309 334864069639986892805005 := by
  unfold tailWord_5869309
  simp only [CollatzResearch.WordTrace]
  refine ⟨214071285893503366017314981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142714190595668910678209987 214071285893503366017314981)
  ·
    refine ⟨40138366105031881128246559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214071285893503366017314981 40138366105031881128246559)
    ·
      refine ⟨60207549157547821692369839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40138366105031881128246559 60207549157547821692369839)
      ·
        refine ⟨90311323736321732538554759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60207549157547821692369839 90311323736321732538554759)
        ·
          refine ⟨135466985604482598807832139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90311323736321732538554759 135466985604482598807832139)
          ·
            refine ⟨203200478406723898211748209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135466985604482598807832139 203200478406723898211748209)
            ·
              refine ⟨152400358805042923658811157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203200478406723898211748209 152400358805042923658811157)
              ·
                refine ⟨7143766818986387046506773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152400358805042923658811157 7143766818986387046506773)
                ·
                  refine ⟨334864069639986892805005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7143766818986387046506773 334864069639986892805005)
                  ·
                    rfl

theorem cell23_5869309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_5869309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869309 prefixEnd_5869309 := by exact prefixLift 5869309
  have htrace : WordTrace (prefixWord ++ tailWord_5869309) baseStart_5869309 baseEnd_5869309 := by
    simpa [prefixWord, tailWord_5869309, baseEnd_5869309] using wordTrace_append hprefix tailTrace_5869309
  have hstable : (prefixWord ++ tailWord_5869309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869309).length < 2 ^ (prefixWord ++ tailWord_5869309).sum := by decide
  have hdescent : baseEnd_5869309 < baseStart_5869309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869313 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 1, 4]
def baseStart_5869313 : Nat := 118140960795 + 5869313 * 2 ^ 59
def prefixEnd_5869313 : Nat := 4983230072969 + 3 ^ 40 * 5869313 * 2
def baseEnd_5869313 : Nat := 1004592893560833339865009

theorem tailTrace_5869313 : CollatzResearch.WordTrace tailWord_5869313 prefixEnd_5869313 1004592893560833339865009 := by
  unfold tailWord_5869313
  simp only [CollatzResearch.WordTrace]
  refine ⟨214071431785488874700460593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142714287856992583133640395 214071431785488874700460593)
  ·
    refine ⟨160553573839116656025345445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214071431785488874700460593 160553573839116656025345445)
    ·
      refine ⟨30103795094834373004752271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160553573839116656025345445 30103795094834373004752271)
      ·
        refine ⟨45155692642251559507128407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30103795094834373004752271 45155692642251559507128407)
        ·
          refine ⟨67733538963377339260692611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45155692642251559507128407 67733538963377339260692611)
          ·
            refine ⟨101600308445066008891038917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67733538963377339260692611 101600308445066008891038917)
            ·
              refine ⟨19050057833449876667069797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101600308445066008891038917 19050057833449876667069797)
              ·
                refine ⟨3571885843771851875075587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19050057833449876667069797 3571885843771851875075587)
                ·
                  refine ⟨5357828765657777812613381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571885843771851875075587 5357828765657777812613381)
                  ·
                    refine ⟨1004592893560833339865009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5357828765657777812613381 1004592893560833339865009)
                    ·
                      rfl

theorem cell23_5869313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_5869313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869313 prefixEnd_5869313 := by exact prefixLift 5869313
  have htrace : WordTrace (prefixWord ++ tailWord_5869313) baseStart_5869313 baseEnd_5869313 := by
    simpa [prefixWord, tailWord_5869313, baseEnd_5869313] using wordTrace_append hprefix tailTrace_5869313
  have hstable : (prefixWord ++ tailWord_5869313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869313).length < 2 ^ (prefixWord ++ tailWord_5869313).sum := by decide
  have hdescent : baseEnd_5869313 < baseStart_5869313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869356 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_5869356 : Nat := 118140960795 + 5869356 * 2 ^ 59
def prefixEnd_5869356 : Nat := 4983230072969 + 3 ^ 40 * 5869356 * 2
def baseEnd_5869356 : Nat := 1004600253450214450452443

theorem tailTrace_5869356 : CollatzResearch.WordTrace tailWord_5869356 prefixEnd_5869356 1004600253450214450452443 := by
  unfold tailWord_5869356
  simp only [CollatzResearch.WordTrace]
  refine ⟨107036500062166546522137961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142715333416222062029517281 107036500062166546522137961)
  ·
    refine ⟨80277375046624909891603471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107036500062166546522137961 80277375046624909891603471)
    ·
      refine ⟨120416062569937364837405207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80277375046624909891603471 120416062569937364837405207)
      ·
        refine ⟨180624093854906047256107811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120416062569937364837405207 180624093854906047256107811)
        ·
          refine ⟨270936140782359070884161717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180624093854906047256107811 270936140782359070884161717)
          ·
            refine ⟨25400263198346162895390161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270936140782359070884161717 25400263198346162895390161)
            ·
              refine ⟨19050197398759622171542621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25400263198346162895390161 19050197398759622171542621)
              ·
                refine ⟨7143824024534858314328483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19050197398759622171542621 7143824024534858314328483)
                ·
                  refine ⟨10715736036802287471492725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143824024534858314328483 10715736036802287471492725)
                  ·
                    refine ⟨1004600253450214450452443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10715736036802287471492725 1004600253450214450452443)
                    ·
                      rfl

theorem cell23_5869356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_5869356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869356 prefixEnd_5869356 := by exact prefixLift 5869356
  have htrace : WordTrace (prefixWord ++ tailWord_5869356) baseStart_5869356 baseEnd_5869356 := by
    simpa [prefixWord, tailWord_5869356, baseEnd_5869356] using wordTrace_append hprefix tailTrace_5869356
  have hstable : (prefixWord ++ tailWord_5869356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869356).length < 2 ^ (prefixWord ++ tailWord_5869356).sum := by decide
  have hdescent : baseEnd_5869356 < baseStart_5869356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869370 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_5869370 : Nat := 118140960795 + 5869370 * 2 ^ 59
def prefixEnd_5869370 : Nat := 4983230072969 + 3 ^ 40 * 5869370 * 2
def baseEnd_5869370 : Nat := 3013807949079806296582265

theorem tailTrace_5869370 : CollatzResearch.WordTrace tailWord_5869370 prefixEnd_5869370 3013807949079806296582265 := by
  unfold tailWord_5869370
  simp only [CollatzResearch.WordTrace]
  refine ⟨53518377686570593358821391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142715673830854915623523709 53518377686570593358821391)
  ·
    refine ⟨80277566529855890038232087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53518377686570593358821391 80277566529855890038232087)
    ·
      refine ⟨120416349794783835057348131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80277566529855890038232087 120416349794783835057348131)
      ·
        refine ⟨180624524692175752586022197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120416349794783835057348131 180624524692175752586022197)
        ·
          refine ⟨16933549189891476804939581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180624524692175752586022197 16933549189891476804939581)
          ·
            refine ⟨6350080946209303801852343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16933549189891476804939581 6350080946209303801852343)
            ·
              refine ⟨9525121419313955702778515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350080946209303801852343 9525121419313955702778515)
              ·
                refine ⟨14287682128970933554167773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9525121419313955702778515 14287682128970933554167773)
                ·
                  refine ⟨5357880798364100082812915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14287682128970933554167773 5357880798364100082812915)
                  ·
                    refine ⟨8036821197546150124219373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357880798364100082812915 8036821197546150124219373)
                    ·
                      refine ⟨3013807949079806296582265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036821197546150124219373 3013807949079806296582265)
                      ·
                        rfl

theorem cell23_5869370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_5869370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869370 prefixEnd_5869370 := by exact prefixLift 5869370
  have htrace : WordTrace (prefixWord ++ tailWord_5869370) baseStart_5869370 baseEnd_5869370 := by
    simpa [prefixWord, tailWord_5869370, baseEnd_5869370] using wordTrace_append hprefix tailTrace_5869370
  have hstable : (prefixWord ++ tailWord_5869370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869370).length < 2 ^ (prefixWord ++ tailWord_5869370).sum := by decide
  have hdescent : baseEnd_5869370 < baseStart_5869370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869393 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_5869393 : Nat := 118140960795 + 5869393 * 2 ^ 59
def prefixEnd_5869393 : Nat := 4983230072969 + 3 ^ 40 * 5869393 * 2
def baseEnd_5869393 : Nat := 3013819759134859706594659

theorem tailTrace_5869393 : CollatzResearch.WordTrace tailWord_5869393 prefixEnd_5869393 3013819759134859706594659 := by
  unfold tailWord_5869393
  simp only [CollatzResearch.WordTrace]
  refine ⟨214074349625199048363372833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142716233083466032242248555 214074349625199048363372833)
  ·
    refine ⟨160555762218899286272529625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214074349625199048363372833 160555762218899286272529625)
    ·
      refine ⟨120416821664174464704397219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160555762218899286272529625 120416821664174464704397219)
      ·
        refine ⟨180625232496261697056595829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120416821664174464704397219 180625232496261697056595829)
        ·
          refine ⟨16933615546524534099055859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180625232496261697056595829 16933615546524534099055859)
          ·
            refine ⟨25400423319786801148583789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16933615546524534099055859 25400423319786801148583789)
            ·
              refine ⟨9525158744920050430718921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25400423319786801148583789 9525158744920050430718921)
              ·
                refine ⟨7143869058690037823039191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9525158744920050430718921 7143869058690037823039191)
                ·
                  refine ⟨10715803588035056734558787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143869058690037823039191 10715803588035056734558787)
                  ·
                    refine ⟨16073705382052585101838181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10715803588035056734558787 16073705382052585101838181)
                    ·
                      refine ⟨3013819759134859706594659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16073705382052585101838181 3013819759134859706594659)
                      ·
                        rfl

theorem cell23_5869393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_5869393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869393 prefixEnd_5869393 := by exact prefixLift 5869393
  have htrace : WordTrace (prefixWord ++ tailWord_5869393) baseStart_5869393 baseEnd_5869393 := by
    simpa [prefixWord, tailWord_5869393, baseEnd_5869393] using wordTrace_append hprefix tailTrace_5869393
  have hstable : (prefixWord ++ tailWord_5869393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869393).length < 2 ^ (prefixWord ++ tailWord_5869393).sum := by decide
  have hdescent : baseEnd_5869393 < baseStart_5869393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869426 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_5869426 : Nat := 118140960795 + 5869426 * 2 ^ 59
def prefixEnd_5869426 : Nat := 4983230072969 + 3 ^ 40 * 5869426 * 2
def baseEnd_5869426 : Nat := 3013836703996458077482007

theorem tailTrace_5869426 : CollatzResearch.WordTrace tailWord_5869426 prefixEnd_5869426 3013836703996458077482007 := by
  unfold tailWord_5869426
  simp only [CollatzResearch.WordTrace]
  refine ⟨53518888308519873749831033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142717035489386329999549421 53518888308519873749831033)
  ·
    refine ⟨40139166231389905312373275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53518888308519873749831033 40139166231389905312373275)
    ·
      refine ⟨60208749347084857968559913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40139166231389905312373275 60208749347084857968559913)
      ·
        refine ⟨45156562010313643476419935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60208749347084857968559913 45156562010313643476419935)
        ·
          refine ⟨67734843015470465214629903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45156562010313643476419935 67734843015470465214629903)
          ·
            refine ⟨101602264523205697821944855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67734843015470465214629903 101602264523205697821944855)
            ·
              refine ⟨152403396784808546732917283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101602264523205697821944855 152403396784808546732917283)
              ·
                refine ⟨228605095177212820099375925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152403396784808546732917283 228605095177212820099375925)
                ·
                  refine ⟨21431727672863701884316493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228605095177212820099375925 21431727672863701884316493)
                  ·
                    refine ⟨8036897877323888206618685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21431727672863701884316493 8036897877323888206618685)
                    ·
                      refine ⟨3013836703996458077482007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036897877323888206618685 3013836703996458077482007)
                      ·
                        rfl

theorem cell23_5869426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_5869426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869426 prefixEnd_5869426 := by exact prefixLift 5869426
  have htrace : WordTrace (prefixWord ++ tailWord_5869426) baseStart_5869426 baseEnd_5869426 := by
    simpa [prefixWord, tailWord_5869426, baseEnd_5869426] using wordTrace_append hprefix tailTrace_5869426
  have hstable : (prefixWord ++ tailWord_5869426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869426).length < 2 ^ (prefixWord ++ tailWord_5869426).sum := by decide
  have hdescent : baseEnd_5869426 < baseStart_5869426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869439 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_5869439 : Nat := 118140960795 + 5869439 * 2 ^ 59
def prefixEnd_5869439 : Nat := 4983230072969 + 3 ^ 40 * 5869439 * 2
def baseEnd_5869439 : Nat := 3013843379244966526619447

theorem tailTrace_5869439 : CollatzResearch.WordTrace tailWord_5869439 prefixEnd_5869439 3013843379244966526619447 := by
  unfold tailWord_5869439
  simp only [CollatzResearch.WordTrace]
  refine ⟨214076027383032398219547371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142717351588688265479698247 214076027383032398219547371)
  ·
    refine ⟨321114041074548597329321057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214076027383032398219547371 321114041074548597329321057)
    ·
      refine ⟨240835530805911447996990793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321114041074548597329321057 240835530805911447996990793)
      ·
        refine ⟨180626648104433585997743095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240835530805911447996990793 180626648104433585997743095)
        ·
          refine ⟨270939972156650378996614643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180626648104433585997743095 270939972156650378996614643)
          ·
            refine ⟨406409958234975568494921965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270939972156650378996614643 406409958234975568494921965)
            ·
              refine ⟨152403734338115838185595737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406409958234975568494921965 152403734338115838185595737)
              ·
                refine ⟨114302800753586878639196803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152403734338115838185595737 114302800753586878639196803)
                ·
                  refine ⟨171454201130380317958795205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114302800753586878639196803 171454201130380317958795205)
                  ·
                    refine ⟨32147662711946309617274101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171454201130380317958795205 32147662711946309617274101)
                    ·
                      refine ⟨3013843379244966526619447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32147662711946309617274101 3013843379244966526619447)
                      ·
                        rfl

theorem cell23_5869439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_5869439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869439 prefixEnd_5869439 := by exact prefixLift 5869439
  have htrace : WordTrace (prefixWord ++ tailWord_5869439) baseStart_5869439 baseEnd_5869439 := by
    simpa [prefixWord, tailWord_5869439, baseEnd_5869439] using wordTrace_append hprefix tailTrace_5869439
  have hstable : (prefixWord ++ tailWord_5869439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869439).length < 2 ^ (prefixWord ++ tailWord_5869439).sum := by decide
  have hdescent : baseEnd_5869439 < baseStart_5869439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869443 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 3]
def baseStart_5869443 : Nat := 118140960795 + 5869443 * 2 ^ 59
def prefixEnd_5869443 : Nat := 4983230072969 + 3 ^ 40 * 5869443 * 2
def baseEnd_5869443 : Nat := 3013845433167584510969429

theorem tailTrace_5869443 : CollatzResearch.WordTrace tailWord_5869443 prefixEnd_5869443 3013845433167584510969429 := by
  unfold tailWord_5869443
  simp only [CollatzResearch.WordTrace]
  refine ⟨214076173275017906902692983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142717448850011937935128655 214076173275017906902692983)
  ·
    refine ⟨321114259912526860354039475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214076173275017906902692983 321114259912526860354039475)
    ·
      refine ⟨481671389868790290531059213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321114259912526860354039475 481671389868790290531059213)
      ·
        refine ⟨180626771200796358949147205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481671389868790290531059213 180626771200796358949147205)
        ·
          refine ⟨33867519600149317302965101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180626771200796358949147205 33867519600149317302965101)
          ·
            refine ⟨12700319850055993988611913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33867519600149317302965101 12700319850055993988611913)
            ·
              refine ⟨9525239887541995491458935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12700319850055993988611913 9525239887541995491458935)
              ·
                refine ⟨14287859831312993237188403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9525239887541995491458935 14287859831312993237188403)
                ·
                  refine ⟨21431789746969489855782605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14287859831312993237188403 21431789746969489855782605)
                  ·
                    refine ⟨8036921155113558695918477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21431789746969489855782605 8036921155113558695918477)
                    ·
                      refine ⟨3013845433167584510969429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036921155113558695918477 3013845433167584510969429)
                      ·
                        rfl

theorem cell23_5869443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_5869443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869443 prefixEnd_5869443 := by exact prefixLift 5869443
  have htrace : WordTrace (prefixWord ++ tailWord_5869443) baseStart_5869443 baseEnd_5869443 := by
    simpa [prefixWord, tailWord_5869443, baseEnd_5869443] using wordTrace_append hprefix tailTrace_5869443
  have hstable : (prefixWord ++ tailWord_5869443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869443).length < 2 ^ (prefixWord ++ tailWord_5869443).sum := by decide
  have hdescent : baseEnd_5869443 < baseStart_5869443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869464 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5869464 : Nat := 118140960795 + 5869464 * 2 ^ 59
def prefixEnd_5869464 : Nat := 4983230072969 + 3 ^ 40 * 5869464 * 2
def baseEnd_5869464 : Nat := 3013856216261328928806833

theorem tailTrace_5869464 : CollatzResearch.WordTrace tailWord_5869464 prefixEnd_5869464 3013856216261328928806833 := by
  unfold tailWord_5869464
  simp only [CollatzResearch.WordTrace]
  refine ⟨107038469603970913744603723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142717959471961218326138297 107038469603970913744603723)
  ·
    refine ⟨160557704405956370616905585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107038469603970913744603723 160557704405956370616905585)
    ·
      refine ⟨120418278304467277962679189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160557704405956370616905585 120418278304467277962679189)
      ·
        refine ⟨5644606795521903654500587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120418278304467277962679189 5644606795521903654500587)
        ·
          refine ⟨8466910193282855481750881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5644606795521903654500587 8466910193282855481750881)
          ·
            refine ⟨6350182644962141611313161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8466910193282855481750881 6350182644962141611313161)
            ·
              refine ⟨4762636983721606208484871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350182644962141611313161 4762636983721606208484871)
              ·
                refine ⟨7143955475582409312727307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762636983721606208484871 7143955475582409312727307)
                ·
                  refine ⟨10715933213373613969090961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143955475582409312727307 10715933213373613969090961)
                  ·
                    refine ⟨8036949910030210476818221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10715933213373613969090961 8036949910030210476818221)
                    ·
                      refine ⟨3013856216261328928806833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8036949910030210476818221 3013856216261328928806833)
                      ·
                        rfl

theorem cell23_5869464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5869464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869464 prefixEnd_5869464 := by exact prefixLift 5869464
  have htrace : WordTrace (prefixWord ++ tailWord_5869464) baseStart_5869464 baseEnd_5869464 := by
    simpa [prefixWord, tailWord_5869464, baseEnd_5869464] using wordTrace_append hprefix tailTrace_5869464
  have hstable : (prefixWord ++ tailWord_5869464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869464).length < 2 ^ (prefixWord ++ tailWord_5869464).sum := by decide
  have hdescent : baseEnd_5869464 < baseStart_5869464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869476 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_5869476 : Nat := 118140960795 + 5869476 * 2 ^ 59
def prefixEnd_5869476 : Nat := 4983230072969 + 3 ^ 40 * 5869476 * 2
def baseEnd_5869476 : Nat := 1004620792676394293952259

theorem tailTrace_5869476 : CollatzResearch.WordTrace tailWord_5869476 prefixEnd_5869476 1004620792676394293952259 := by
  unfold tailWord_5869476
  simp only [CollatzResearch.WordTrace]
  refine ⟨107038688441949176769322141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142718251255932235692429521 107038688441949176769322141)
  ·
    refine ⟨40139508165730941288495803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107038688441949176769322141 40139508165730941288495803)
    ·
      refine ⟨60209262248596411932743705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40139508165730941288495803 60209262248596411932743705)
      ·
        refine ⟨45156946686447308949557779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60209262248596411932743705 45156946686447308949557779)
        ·
          refine ⟨67735420029670963424336669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45156946686447308949557779 67735420029670963424336669)
          ·
            refine ⟨25400782511126611284126251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67735420029670963424336669 25400782511126611284126251)
            ·
              refine ⟨38101173766689916926189377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25400782511126611284126251 38101173766689916926189377)
              ·
                refine ⟨28575880325017437694642033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38101173766689916926189377 28575880325017437694642033)
                ·
                  refine ⟨21431910243763078270981525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28575880325017437694642033 21431910243763078270981525)
                  ·
                    refine ⟨1004620792676394293952259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21431910243763078270981525 1004620792676394293952259)
                    ·
                      rfl

theorem cell23_5869476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_5869476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869476 prefixEnd_5869476 := by exact prefixLift 5869476
  have htrace : WordTrace (prefixWord ++ tailWord_5869476) baseStart_5869476 baseEnd_5869476 := by
    simpa [prefixWord, tailWord_5869476, baseEnd_5869476] using wordTrace_append hprefix tailTrace_5869476
  have hstable : (prefixWord ++ tailWord_5869476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869476).length < 2 ^ (prefixWord ++ tailWord_5869476).sum := by decide
  have hdescent : baseEnd_5869476 < baseStart_5869476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869496 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_5869496 : Nat := 118140960795 + 5869496 * 2 ^ 59
def prefixEnd_5869496 : Nat := 4983230072969 + 3 ^ 40 * 5869496 * 2
def baseEnd_5869496 : Nat := 3013872647642272803606685

theorem tailTrace_5869496 : CollatzResearch.WordTrace tailWord_5869496 prefixEnd_5869496 3013872647642272803606685 := by
  unfold tailWord_5869496
  simp only [CollatzResearch.WordTrace]
  refine ⟨107039053171912948477186171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142718737562550597969581561 107039053171912948477186171)
  ·
    refine ⟨160558579757869422715779257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107039053171912948477186171 160558579757869422715779257)
    ·
      refine ⟨120418934818402067036834443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160558579757869422715779257 120418934818402067036834443)
      ·
        refine ⟨180628402227603100555251665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120418934818402067036834443 180628402227603100555251665)
        ·
          refine ⟨135471301670702325416438749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180628402227603100555251665 135471301670702325416438749)
          ·
            refine ⟨50801738126513372031164531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135471301670702325416438749 50801738126513372031164531)
            ·
              refine ⟨76202607189770058046746797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50801738126513372031164531 76202607189770058046746797)
              ·
                refine ⟨28575977696163771767530049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76202607189770058046746797 28575977696163771767530049)
                ·
                  refine ⟨21431983272122828825647537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28575977696163771767530049 21431983272122828825647537)
                  ·
                    refine ⟨16073987454092121619235653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21431983272122828825647537 16073987454092121619235653)
                    ·
                      refine ⟨3013872647642272803606685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16073987454092121619235653 3013872647642272803606685)
                      ·
                        rfl

theorem cell23_5869496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_5869496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869496 prefixEnd_5869496 := by exact prefixLift 5869496
  have htrace : WordTrace (prefixWord ++ tailWord_5869496) baseStart_5869496 baseEnd_5869496 := by
    simpa [prefixWord, tailWord_5869496, baseEnd_5869496] using wordTrace_append hprefix tailTrace_5869496
  have hstable : (prefixWord ++ tailWord_5869496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869496).length < 2 ^ (prefixWord ++ tailWord_5869496).sum := by decide
  have hdescent : baseEnd_5869496 < baseStart_5869496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869540 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 5]
def baseStart_5869540 : Nat := 118140960795 + 5869540 * 2 ^ 59
def prefixEnd_5869540 : Nat := 4983230072969 + 3 ^ 40 * 5869540 * 2
def baseEnd_5869540 : Nat := 334877248976785625717387

theorem tailTrace_5869540 : CollatzResearch.WordTrace tailWord_5869540 prefixEnd_5869540 334877248976785625717387 := by
  unfold tailWord_5869540
  simp only [CollatzResearch.WordTrace]
  refine ⟨107039855577833246234487037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142719807437110994979316049 107039855577833246234487037)
  ·
    refine ⟨40139945841687467337932639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107039855577833246234487037 40139945841687467337932639)
    ·
      refine ⟨60209918762531201006898959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40139945841687467337932639 60209918762531201006898959)
      ·
        refine ⟨90314878143796801510348439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60209918762531201006898959 90314878143796801510348439)
        ·
          refine ⟨135472317215695202265522659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90314878143796801510348439 135472317215695202265522659)
          ·
            refine ⟨203208475823542803398283989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135472317215695202265522659 203208475823542803398283989)
            ·
              refine ⟨4762698652114284454647281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 203208475823542803398283989 4762698652114284454647281)
              ·
                refine ⟨3572023989085713340985461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762698652114284454647281 3572023989085713340985461)
                ·
                  refine ⟨334877248976785625717387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3572023989085713340985461 334877248976785625717387)
                  ·
                    rfl

theorem cell23_5869540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_5869540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869540 prefixEnd_5869540 := by exact prefixLift 5869540
  have htrace : WordTrace (prefixWord ++ tailWord_5869540) baseStart_5869540 baseEnd_5869540 := by
    simpa [prefixWord, tailWord_5869540, baseEnd_5869540] using wordTrace_append hprefix tailTrace_5869540
  have hstable : (prefixWord ++ tailWord_5869540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869540).length < 2 ^ (prefixWord ++ tailWord_5869540).sum := by decide
  have hdescent : baseEnd_5869540 < baseStart_5869540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869573 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_5869573 : Nat := 118140960795 + 5869573 * 2 ^ 59
def prefixEnd_5869573 : Nat := 4983230072969 + 3 ^ 40 * 5869573 * 2
def baseEnd_5869573 : Nat := 3013912185652669002343831

theorem tailTrace_5869573 : CollatzResearch.WordTrace tailWord_5869573 prefixEnd_5869573 3013912185652669002343831 := by
  unfold tailWord_5869573
  simp only [CollatzResearch.WordTrace]
  refine ⟨214080914764546939104925373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142720609843031292736616915 214080914764546939104925373)
  ·
    refine ⟨80280343036705102164347015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214080914764546939104925373 80280343036705102164347015)
    ·
      refine ⟨120420514555057653246520523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80280343036705102164347015 120420514555057653246520523)
      ·
        refine ⟨180630771832586479869780785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120420514555057653246520523 180630771832586479869780785)
        ·
          refine ⟨135473078874439859902335589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180630771832586479869780785 135473078874439859902335589)
          ·
            refine ⟨25401202288957473731687923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135473078874439859902335589 25401202288957473731687923)
            ·
              refine ⟨38101803433436210597531885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25401202288957473731687923 38101803433436210597531885)
              ·
                refine ⟨14288176287538578974074457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38101803433436210597531885 14288176287538578974074457)
                ·
                  refine ⟨10716132215653934230555843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14288176287538578974074457 10716132215653934230555843)
                  ·
                    refine ⟨16074198323480901345833765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10716132215653934230555843 16074198323480901345833765)
                    ·
                      refine ⟨3013912185652669002343831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16074198323480901345833765 3013912185652669002343831)
                      ·
                        rfl

theorem cell23_5869573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_5869573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869573 prefixEnd_5869573 := by exact prefixLift 5869573
  have htrace : WordTrace (prefixWord ++ tailWord_5869573) baseStart_5869573 baseEnd_5869573 := by
    simpa [prefixWord, tailWord_5869573, baseEnd_5869573] using wordTrace_append hprefix tailTrace_5869573
  have hstable : (prefixWord ++ tailWord_5869573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869573).length < 2 ^ (prefixWord ++ tailWord_5869573).sum := by decide
  have hdescent : baseEnd_5869573 < baseStart_5869573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869643 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 1, 5]
def baseStart_5869643 : Nat := 118140960795 + 5869643 * 2 ^ 59
def prefixEnd_5869643 : Nat := 4983230072969 + 3 ^ 40 * 5869643 * 2
def baseEnd_5869643 : Nat := 1004649376432827909489503

theorem tailTrace_5869643 : CollatzResearch.WordTrace tailWord_5869643 prefixEnd_5869643 1004649376432827909489503 := by
  unfold tailWord_5869643
  simp only [CollatzResearch.WordTrace]
  refine ⟨214083467874293341059973583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142722311916195560706649055 214083467874293341059973583)
  ·
    refine ⟨321125201811440011589960375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214083467874293341059973583 321125201811440011589960375)
    ·
      refine ⟨481687802717160017384940563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321125201811440011589960375 481687802717160017384940563)
      ·
        refine ⟨722531704075740026077410845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481687802717160017384940563 722531704075740026077410845)
        ·
          refine ⟨270949389028402509779029067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722531704075740026077410845 270949389028402509779029067)
          ·
            refine ⟨406424083542603764668543601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270949389028402509779029067 406424083542603764668543601)
            ·
              refine ⟨304818062656952823501407701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406424083542603764668543601 304818062656952823501407701)
              ·
                refine ⟨7144173343522331800814243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 304818062656952823501407701 7144173343522331800814243)
                ·
                  refine ⟨10716260015283497701221365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144173343522331800814243 10716260015283497701221365)
                  ·
                    refine ⟨1004649376432827909489503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10716260015283497701221365 1004649376432827909489503)
                    ·
                      rfl

theorem cell23_5869643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 5].length) (baseStart_5869643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869643 prefixEnd_5869643 := by exact prefixLift 5869643
  have htrace : WordTrace (prefixWord ++ tailWord_5869643) baseStart_5869643 baseEnd_5869643 := by
    simpa [prefixWord, tailWord_5869643, baseEnd_5869643] using wordTrace_append hprefix tailTrace_5869643
  have hstable : (prefixWord ++ tailWord_5869643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869643).length < 2 ^ (prefixWord ++ tailWord_5869643).sum := by decide
  have hdescent : baseEnd_5869643 < baseStart_5869643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869657 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 1, 1, 3]
def baseStart_5869657 : Nat := 118140960795 + 5869657 * 2 ^ 59
def prefixEnd_5869657 : Nat := 4983230072969 + 3 ^ 40 * 5869657 * 2
def baseEnd_5869657 : Nat := 3013955318027646673693445

theorem tailTrace_5869657 : CollatzResearch.WordTrace tailWord_5869657 prefixEnd_5869657 3013955318027646673693445 := by
  unfold tailWord_5869657
  simp only [CollatzResearch.WordTrace]
  refine ⟨214083978496242621450983225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142722652330828414300655483 214083978496242621450983225)
  ·
    refine ⟨160562983872181966088237419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214083978496242621450983225 160562983872181966088237419)
    ·
      refine ⟨240844475808272949132356129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160562983872181966088237419 240844475808272949132356129)
      ·
        refine ⟨180633356856204711849267097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240844475808272949132356129 180633356856204711849267097)
        ·
          refine ⟨135475017642153533886950323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180633356856204711849267097 135475017642153533886950323)
          ·
            refine ⟨203212526463230300830425485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135475017642153533886950323 203212526463230300830425485)
            ·
              refine ⟨76204697423711362811409557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203212526463230300830425485 76204697423711362811409557)
              ·
                refine ⟨3572095191736470131784823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76204697423711362811409557 3572095191736470131784823)
                ·
                  refine ⟨5358142787604705197677235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572095191736470131784823 5358142787604705197677235)
                  ·
                    refine ⟨8037214181407057796515853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5358142787604705197677235 8037214181407057796515853)
                    ·
                      refine ⟨3013955318027646673693445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8037214181407057796515853 3013955318027646673693445)
                      ·
                        rfl

theorem cell23_5869657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_5869657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869657 prefixEnd_5869657 := by exact prefixLift 5869657
  have htrace : WordTrace (prefixWord ++ tailWord_5869657) baseStart_5869657 baseEnd_5869657 := by
    simpa [prefixWord, tailWord_5869657, baseEnd_5869657] using wordTrace_append hprefix tailTrace_5869657
  have hstable : (prefixWord ++ tailWord_5869657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869657).length < 2 ^ (prefixWord ++ tailWord_5869657).sum := by decide
  have hdescent : baseEnd_5869657 < baseStart_5869657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869663 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_5869663 : Nat := 118140960795 + 5869663 * 2 ^ 59
def prefixEnd_5869663 : Nat := 4983230072969 + 3 ^ 40 * 5869663 * 2
def baseEnd_5869663 : Nat := 3013958398911573650218417

theorem tailTrace_5869663 : CollatzResearch.WordTrace tailWord_5869663 prefixEnd_5869663 3013958398911573650218417 := by
  unfold tailWord_5869663
  simp only [CollatzResearch.WordTrace]
  refine ⟨214084197334220884475701643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142722798222813922983801095 214084197334220884475701643)
  ·
    refine ⟨321126296001331326713552465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214084197334220884475701643 321126296001331326713552465)
    ·
      refine ⟨240844722000998495035164349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321126296001331326713552465 240844722000998495035164349)
      ·
        refine ⟨90316770750374435638186631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240844722000998495035164349 90316770750374435638186631)
        ·
          refine ⟨135475156125561653457279947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90316770750374435638186631 135475156125561653457279947)
          ·
            refine ⟨203212734188342480185919921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135475156125561653457279947 203212734188342480185919921)
            ·
              refine ⟨152409550641256860139439941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203212734188342480185919921 152409550641256860139439941)
              ·
                refine ⟨28576790745235661276144989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152409550641256860139439941 28576790745235661276144989)
                ·
                  refine ⟨10716296529463372978554371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28576790745235661276144989 10716296529463372978554371)
                  ·
                    refine ⟨16074444794195059467831557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10716296529463372978554371 16074444794195059467831557)
                    ·
                      refine ⟨3013958398911573650218417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16074444794195059467831557 3013958398911573650218417)
                      ·
                        rfl

theorem cell23_5869663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_5869663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869663 prefixEnd_5869663 := by exact prefixLift 5869663
  have htrace : WordTrace (prefixWord ++ tailWord_5869663) baseStart_5869663 baseEnd_5869663 := by
    simpa [prefixWord, tailWord_5869663, baseEnd_5869663] using wordTrace_append hprefix tailTrace_5869663
  have hstable : (prefixWord ++ tailWord_5869663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869663).length < 2 ^ (prefixWord ++ tailWord_5869663).sum := by decide
  have hdescent : baseEnd_5869663 < baseStart_5869663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869680 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4]
def baseStart_5869680 : Nat := 118140960795 + 5869680 * 2 ^ 59
def prefixEnd_5869680 : Nat := 4983230072969 + 3 ^ 40 * 5869680 * 2
def baseEnd_5869680 : Nat := 3013967128082700083705839

theorem tailTrace_5869680 : CollatzResearch.WordTrace tailWord_5869680 prefixEnd_5869680 3013967128082700083705839 := by
  unfold tailWord_5869680
  simp only [CollatzResearch.WordTrace]
  refine ⟨107042408687579648189535247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142723211583439530919380329 107042408687579648189535247)
  ·
    refine ⟨160563613031369472284302871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107042408687579648189535247 160563613031369472284302871)
    ·
      refine ⟨240845419547054208426454307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160563613031369472284302871 240845419547054208426454307)
      ·
        refine ⟨361268129320581312639681461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240845419547054208426454307 361268129320581312639681461)
        ·
          refine ⟨33868887123804498059970137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 361268129320581312639681461 33868887123804498059970137)
          ·
            refine ⟨25401665342853373544977603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33868887123804498059970137 25401665342853373544977603)
            ·
              refine ⟨38102498014280060317466405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25401665342853373544977603 38102498014280060317466405)
              ·
                refine ⟨7144218377677511309524951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38102498014280060317466405 7144218377677511309524951)
                ·
                  refine ⟨10716327566516266964287427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144218377677511309524951 10716327566516266964287427)
                  ·
                    refine ⟨16074491349774400446431141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10716327566516266964287427 16074491349774400446431141)
                    ·
                      refine ⟨3013967128082700083705839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16074491349774400446431141 3013967128082700083705839)
                      ·
                        rfl

theorem cell23_5869680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_5869680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869680 prefixEnd_5869680 := by exact prefixLift 5869680
  have htrace : WordTrace (prefixWord ++ tailWord_5869680) baseStart_5869680 baseEnd_5869680 := by
    simpa [prefixWord, tailWord_5869680, baseEnd_5869680] using wordTrace_append hprefix tailTrace_5869680
  have hstable : (prefixWord ++ tailWord_5869680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869680).length < 2 ^ (prefixWord ++ tailWord_5869680).sum := by decide
  have hdescent : baseEnd_5869680 < baseStart_5869680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869700 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_5869700 : Nat := 118140960795 + 5869700 * 2 ^ 59
def prefixEnd_5869700 : Nat := 4983230072969 + 3 ^ 40 * 5869700 * 2
def baseEnd_5869700 : Nat := 3013977397695790005455747

theorem tailTrace_5869700 : CollatzResearch.WordTrace tailWord_5869700 prefixEnd_5869700 3013977397695790005455747 := by
  unfold tailWord_5869700
  simp only [CollatzResearch.WordTrace]
  refine ⟨107042773417543419897399277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142723697890057893196532369 107042773417543419897399277)
  ·
    refine ⟨40141040031578782461524729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107042773417543419897399277 40141040031578782461524729)
    ·
      refine ⟨30105780023684086846143547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40141040031578782461524729 30105780023684086846143547)
      ·
        refine ⟨45158670035526130269215321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30105780023684086846143547 45158670035526130269215321)
        ·
          refine ⟨33869002526644597701911491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45158670035526130269215321 33869002526644597701911491)
          ·
            refine ⟨50803503789966896552867237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33869002526644597701911491 50803503789966896552867237)
            ·
              refine ⟨9525656960618793103662607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50803503789966896552867237 9525656960618793103662607)
              ·
                refine ⟨14288485440928189655493911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9525656960618793103662607 14288485440928189655493911)
                ·
                  refine ⟨21432728161392284483240867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14288485440928189655493911 21432728161392284483240867)
                  ·
                    refine ⟨32149092242088426724861301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21432728161392284483240867 32149092242088426724861301)
                    ·
                      refine ⟨3013977397695790005455747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32149092242088426724861301 3013977397695790005455747)
                      ·
                        rfl

theorem cell23_5869700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_5869700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869700 prefixEnd_5869700 := by exact prefixLift 5869700
  have htrace : WordTrace (prefixWord ++ tailWord_5869700) baseStart_5869700 baseEnd_5869700 := by
    simpa [prefixWord, tailWord_5869700, baseEnd_5869700] using wordTrace_append hprefix tailTrace_5869700
  have hstable : (prefixWord ++ tailWord_5869700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869700).length < 2 ^ (prefixWord ++ tailWord_5869700).sum := by decide
  have hdescent : baseEnd_5869700 < baseStart_5869700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869720 : List Nat := [2, 1, 2, 4, 3, 1, 2, 8]
def baseStart_5869720 : Nat := 118140960795 + 5869720 * 2 ^ 59
def prefixEnd_5869720 : Nat := 4983230072969 + 3 ^ 40 * 5869720 * 2
def baseEnd_5869720 : Nat := 111629172863291849155765

theorem tailTrace_5869720 : CollatzResearch.WordTrace tailWord_5869720 prefixEnd_5869720 111629172863291849155765 := by
  unfold tailWord_5869720
  simp only [CollatzResearch.WordTrace]
  refine ⟨107043138147507191605263307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142724184196676255473684409 107043138147507191605263307)
  ·
    refine ⟨160564707221260787407894961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107043138147507191605263307 160564707221260787407894961)
    ·
      refine ⟨120423530415945590555921221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160564707221260787407894961 120423530415945590555921221)
      ·
        refine ⟨22579411952989798229235229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120423530415945590555921221 22579411952989798229235229)
        ·
          refine ⟨8467279482371174335963211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22579411952989798229235229 8467279482371174335963211)
          ·
            refine ⟨12700919223556761503944817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8467279482371174335963211 12700919223556761503944817)
            ·
              refine ⟨9525689417667571127958613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12700919223556761503944817 9525689417667571127958613)
              ·
                refine ⟨111629172863291849155765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9525689417667571127958613 111629172863291849155765)
                ·
                  rfl

theorem cell23_5869720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 8].length) (baseStart_5869720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869720 prefixEnd_5869720 := by exact prefixLift 5869720
  have htrace : WordTrace (prefixWord ++ tailWord_5869720) baseStart_5869720 baseEnd_5869720 := by
    simpa [prefixWord, tailWord_5869720, baseEnd_5869720] using wordTrace_append hprefix tailTrace_5869720
  have hstable : (prefixWord ++ tailWord_5869720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869720).length < 2 ^ (prefixWord ++ tailWord_5869720).sum := by decide
  have hdescent : baseEnd_5869720 < baseStart_5869720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869764 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_5869764 : Nat := 118140960795 + 5869764 * 2 ^ 59
def prefixEnd_5869764 : Nat := 4983230072969 + 3 ^ 40 * 5869764 * 2
def baseEnd_5869764 : Nat := 3014010260457677755055453

theorem tailTrace_5869764 : CollatzResearch.WordTrace tailWord_5869764 prefixEnd_5869764 3014010260457677755055453 := by
  unfold tailWord_5869764
  simp only [CollatzResearch.WordTrace]
  refine ⟨107043940553427489362564173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142725254071236652483418897 107043940553427489362564173)
  ·
    refine ⟨40141477707535308510961565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107043940553427489362564173 40141477707535308510961565)
    ·
      refine ⟨15053054140325740691610587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40141477707535308510961565 15053054140325740691610587)
      ·
        refine ⟨22579581210488611037415881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15053054140325740691610587 22579581210488611037415881)
        ·
          refine ⟨16934685907866458278061911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22579581210488611037415881 16934685907866458278061911)
          ·
            refine ⟨25402028861799687417092867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16934685907866458278061911 25402028861799687417092867)
            ·
              refine ⟨38103043292699531125639301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25402028861799687417092867 38103043292699531125639301)
              ·
                refine ⟨7144320617381162086057369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38103043292699531125639301 7144320617381162086057369)
                ·
                  refine ⟨5358240463035871564543027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7144320617381162086057369 5358240463035871564543027)
                  ·
                    refine ⟨8037360694553807346814541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5358240463035871564543027 8037360694553807346814541)
                    ·
                      refine ⟨3014010260457677755055453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8037360694553807346814541 3014010260457677755055453)
                      ·
                        rfl

theorem cell23_5869764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_5869764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869764 prefixEnd_5869764 := by exact prefixLift 5869764
  have htrace : WordTrace (prefixWord ++ tailWord_5869764) baseStart_5869764 baseEnd_5869764 := by
    simpa [prefixWord, tailWord_5869764, baseEnd_5869764] using wordTrace_append hprefix tailTrace_5869764
  have hstable : (prefixWord ++ tailWord_5869764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869764).length < 2 ^ (prefixWord ++ tailWord_5869764).sum := by decide
  have hdescent : baseEnd_5869764 < baseStart_5869764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869861 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 5]
def baseStart_5869861 : Nat := 118140960795 + 5869861 * 2 ^ 59
def prefixEnd_5869861 : Nat := 4983230072969 + 3 ^ 40 * 5869861 * 2
def baseEnd_5869861 : Nat := 334895563120129319504723

theorem tailTrace_5869861 : CollatzResearch.WordTrace tailWord_5869861 prefixEnd_5869861 334895563120129319504723 := by
  unfold tailWord_5869861
  simp only [CollatzResearch.WordTrace]
  refine ⟨214091418987503564291409437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142727612658335709527606291 214091418987503564291409437)
  ·
    refine ⟨80284282120313836609278539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214091418987503564291409437 80284282120313836609278539)
    ·
      refine ⟨120426423180470754913917809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80284282120313836609278539 120426423180470754913917809)
      ·
        refine ⟨90319817385353066185438357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120426423180470754913917809 90319817385353066185438357)
        ·
          refine ⟨4233741439938424977442423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90319817385353066185438357 4233741439938424977442423)
          ·
            refine ⟨6350612159907637466163635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233741439938424977442423 6350612159907637466163635)
            ·
              refine ⟨9525918239861456199245453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350612159907637466163635 9525918239861456199245453)
              ·
                refine ⟨3572219339948046074717045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9525918239861456199245453 3572219339948046074717045)
                ·
                  refine ⟨334895563120129319504723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3572219339948046074717045 334895563120129319504723)
                  ·
                    rfl

theorem cell23_5869861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_5869861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869861 prefixEnd_5869861 := by exact prefixLift 5869861
  have htrace : WordTrace (prefixWord ++ tailWord_5869861) baseStart_5869861 baseEnd_5869861 := by
    simpa [prefixWord, tailWord_5869861, baseEnd_5869861] using wordTrace_append hprefix tailTrace_5869861
  have hstable : (prefixWord ++ tailWord_5869861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869861).length < 2 ^ (prefixWord ++ tailWord_5869861).sum := by decide
  have hdescent : baseEnd_5869861 < baseStart_5869861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869877 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_5869877 : Nat := 118140960795 + 5869877 * 2 ^ 59
def prefixEnd_5869877 : Nat := 4983230072969 + 3 ^ 40 * 5869877 * 2
def baseEnd_5869877 : Nat := 3014068283771635812942433

theorem tailTrace_5869877 : CollatzResearch.WordTrace tailWord_5869877 prefixEnd_5869877 3014068283771635812942433 := by
  unfold tailWord_5869877
  simp only [CollatzResearch.WordTrace]
  refine ⟨214092002555445599023991885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142728001703630399349327923 214092002555445599023991885)
  ·
    refine ⟨80284500958292099633996957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214092002555445599023991885 80284500958292099633996957)
    ·
      refine ⟨30106687859359537362748859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80284500958292099633996957 30106687859359537362748859)
      ·
        refine ⟨45160031789039306044123289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30106687859359537362748859 45160031789039306044123289)
        ·
          refine ⟨33870023841779479533092467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45160031789039306044123289 33870023841779479533092467)
          ·
            refine ⟨50805035762669219299638701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33870023841779479533092467 50805035762669219299638701)
            ·
              refine ⟨19051888411000957237364513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50805035762669219299638701 19051888411000957237364513)
              ·
                refine ⟨14288916308250717928023385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19051888411000957237364513 14288916308250717928023385)
                ·
                  refine ⟨10716687231188038446017539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14288916308250717928023385 10716687231188038446017539)
                  ·
                    refine ⟨16075030846782057669026309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10716687231188038446017539 16075030846782057669026309)
                    ·
                      refine ⟨3014068283771635812942433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16075030846782057669026309 3014068283771635812942433)
                      ·
                        rfl

theorem cell23_5869877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_5869877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869877 prefixEnd_5869877 := by exact prefixLift 5869877
  have htrace : WordTrace (prefixWord ++ tailWord_5869877) baseStart_5869877 baseEnd_5869877 := by
    simpa [prefixWord, tailWord_5869877, baseEnd_5869877] using wordTrace_append hprefix tailTrace_5869877
  have hstable : (prefixWord ++ tailWord_5869877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869877).length < 2 ^ (prefixWord ++ tailWord_5869877).sum := by decide
  have hdescent : baseEnd_5869877 < baseStart_5869877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869937 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 3, 5, 2]
def baseStart_5869937 : Nat := 118140960795 + 5869937 * 2 ^ 59
def prefixEnd_5869937 : Nat := 4983230072969 + 3 ^ 40 * 5869937 * 2
def baseEnd_5869937 : Nat := 3014099092610905578192157

theorem tailTrace_5869937 : CollatzResearch.WordTrace tailWord_5869937 prefixEnd_5869937 3014099092610905578192157 := by
  unfold tailWord_5869937
  simp only [CollatzResearch.WordTrace]
  refine ⟨214094190935228229271176065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142729460623485486180784043 214094190935228229271176065)
  ·
    refine ⟨160570643201421171953382049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214094190935228229271176065 160570643201421171953382049)
    ·
      refine ⟨120427982401065878965036537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160570643201421171953382049 120427982401065878965036537)
      ·
        refine ⟨90320986800799409223777403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120427982401065878965036537 90320986800799409223777403)
        ·
          refine ⟨135481480201199113835666105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90320986800799409223777403 135481480201199113835666105)
          ·
            refine ⟨101611110150899335376749579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135481480201199113835666105 101611110150899335376749579)
            ·
              refine ⟨152416665226349003065124369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101611110150899335376749579 152416665226349003065124369)
              ·
                refine ⟨114312498919761752298843277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152416665226349003065124369 114312498919761752298843277)
                ·
                  refine ⟨42867187094910657112066229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114312498919761752298843277 42867187094910657112066229)
                  ·
                    refine ⟨4018798790147874104256209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42867187094910657112066229 4018798790147874104256209)
                    ·
                      refine ⟨3014099092610905578192157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018798790147874104256209 3014099092610905578192157)
                      ·
                        rfl

theorem cell23_5869937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_5869937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869937 prefixEnd_5869937 := by exact prefixLift 5869937
  have htrace : WordTrace (prefixWord ++ tailWord_5869937) baseStart_5869937 baseEnd_5869937 := by
    simpa [prefixWord, tailWord_5869937, baseEnd_5869937] using wordTrace_append hprefix tailTrace_5869937
  have hstable : (prefixWord ++ tailWord_5869937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869937).length < 2 ^ (prefixWord ++ tailWord_5869937).sum := by decide
  have hdescent : baseEnd_5869937 < baseStart_5869937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869938 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_5869938 : Nat := 118140960795 + 5869938 * 2 ^ 59
def prefixEnd_5869938 : Nat := 4983230072969 + 3 ^ 40 * 5869938 * 2
def baseEnd_5869938 : Nat := 1004699868697186691426551

theorem tailTrace_5869938 : CollatzResearch.WordTrace tailWord_5869938 prefixEnd_5869938 1004699868697186691426551 := by
  unfold tailWord_5869938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53523556852056151610490617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142729484938816404294641645 53523556852056151610490617)
  ·
    refine ⟨40142667639042113707867963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53523556852056151610490617 40142667639042113707867963)
    ·
      refine ⟨60214001458563170561801945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40142667639042113707867963 60214001458563170561801945)
      ·
        refine ⟨45160501093922377921351459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60214001458563170561801945 45160501093922377921351459)
        ·
          refine ⟨67740751640883566882027189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45160501093922377921351459 67740751640883566882027189)
          ·
            refine ⟨6350695466332834395190049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67740751640883566882027189 6350695466332834395190049)
            ·
              refine ⟨4763021599749625796392537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350695466332834395190049 4763021599749625796392537)
              ·
                refine ⟨3572266199812219347294403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4763021599749625796392537 3572266199812219347294403)
                ·
                  refine ⟨5358399299718329020941605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572266199812219347294403 5358399299718329020941605)
                  ·
                    refine ⟨1004699868697186691426551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358399299718329020941605 1004699868697186691426551)
                    ·
                      rfl

theorem cell23_5869938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_5869938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869938 prefixEnd_5869938 := by exact prefixLift 5869938
  have htrace : WordTrace (prefixWord ++ tailWord_5869938) baseStart_5869938 baseEnd_5869938 := by
    simpa [prefixWord, tailWord_5869938, baseEnd_5869938] using wordTrace_append hprefix tailTrace_5869938
  have hstable : (prefixWord ++ tailWord_5869938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869938).length < 2 ^ (prefixWord ++ tailWord_5869938).sum := by decide
  have hdescent : baseEnd_5869938 < baseStart_5869938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869977 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 4, 4]
def baseStart_5869977 : Nat := 118140960795 + 5869977 * 2 ^ 59
def prefixEnd_5869977 : Nat := 4983230072969 + 3 ^ 40 * 5869977 * 2
def baseEnd_5869977 : Nat := 1004706543945695140563991

theorem tailTrace_5869977 : CollatzResearch.WordTrace tailWord_5869977 prefixEnd_5869977 1004706543945695140563991 := by
  unfold tailWord_5869977
  simp only [CollatzResearch.WordTrace]
  refine ⟨214095649855083316102632185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142730433236722210735088123 214095649855083316102632185)
  ·
    refine ⟨160571737391312487076974139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214095649855083316102632185 160571737391312487076974139)
    ·
      refine ⟨240857606086968730615461209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160571737391312487076974139 240857606086968730615461209)
      ·
        refine ⟨180643204565226547961595907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240857606086968730615461209 180643204565226547961595907)
        ·
          refine ⟨270964806847839821942393861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180643204565226547961595907 270964806847839821942393861)
          ·
            refine ⟨50805901283969966614198849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270964806847839821942393861 50805901283969966614198849)
            ·
              refine ⟨38104425962977474960649137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50805901283969966614198849 38104425962977474960649137)
              ·
                refine ⟨28578319472233106220486853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38104425962977474960649137 28578319472233106220486853)
                ·
                  refine ⟨5358434901043707416341285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28578319472233106220486853 5358434901043707416341285)
                  ·
                    refine ⟨1004706543945695140563991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358434901043707416341285 1004706543945695140563991)
                    ·
                      rfl

theorem cell23_5869977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_5869977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869977 prefixEnd_5869977 := by exact prefixLift 5869977
  have htrace : WordTrace (prefixWord ++ tailWord_5869977) baseStart_5869977 baseEnd_5869977 := by
    simpa [prefixWord, tailWord_5869977, baseEnd_5869977] using wordTrace_append hprefix tailTrace_5869977
  have hstable : (prefixWord ++ tailWord_5869977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869977).length < 2 ^ (prefixWord ++ tailWord_5869977).sum := by decide
  have hdescent : baseEnd_5869977 < baseStart_5869977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869978 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3]
def baseStart_5869978 : Nat := 118140960795 + 5869978 * 2 ^ 59
def prefixEnd_5869978 : Nat := 4983230072969 + 3 ^ 40 * 5869978 * 2
def baseEnd_5869978 : Nat := 3014120145317739917779469

theorem tailTrace_5869978 : CollatzResearch.WordTrace tailWord_5869978 prefixEnd_5869978 3014120145317739917779469 := by
  unfold tailWord_5869978
  simp only [CollatzResearch.WordTrace]
  refine ⟨53523921582019923318354647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142730457552053128848945725 53523921582019923318354647)
  ·
    refine ⟨80285882373029884977531971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53523921582019923318354647 80285882373029884977531971)
    ·
      refine ⟨120428823559544827466297957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80285882373029884977531971 120428823559544827466297957)
      ·
        refine ⟨22580404417414655149930867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120428823559544827466297957 22580404417414655149930867)
        ·
          refine ⟨33870606626121982724896301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22580404417414655149930867 33870606626121982724896301)
          ·
            refine ⟨12701477484795743521836113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33870606626121982724896301 12701477484795743521836113)
            ·
              refine ⟨9526108113596807641377085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12701477484795743521836113 9526108113596807641377085)
              ·
                refine ⟨3572290542598802865516407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9526108113596807641377085 3572290542598802865516407)
                ·
                  refine ⟨5358435813898204298274611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572290542598802865516407 5358435813898204298274611)
                  ·
                    refine ⟨8037653720847306447411917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5358435813898204298274611 8037653720847306447411917)
                    ·
                      refine ⟨3014120145317739917779469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8037653720847306447411917 3014120145317739917779469)
                      ·
                        rfl

theorem cell23_5869978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_5869978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869978 prefixEnd_5869978 := by exact prefixLift 5869978
  have htrace : WordTrace (prefixWord ++ tailWord_5869978) baseStart_5869978 baseEnd_5869978 := by
    simpa [prefixWord, tailWord_5869978, baseEnd_5869978] using wordTrace_append hprefix tailTrace_5869978
  have hstable : (prefixWord ++ tailWord_5869978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869978).length < 2 ^ (prefixWord ++ tailWord_5869978).sum := by decide
  have hdescent : baseEnd_5869978 < baseStart_5869978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5869984 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4]
def baseStart_5869984 : Nat := 118140960795 + 5869984 * 2 ^ 59
def prefixEnd_5869984 : Nat := 4983230072969 + 3 ^ 40 * 5869984 * 2
def baseEnd_5869984 : Nat := 3014123226201666894304441

theorem tailTrace_5869984 : CollatzResearch.WordTrace tailWord_5869984 prefixEnd_5869984 3014123226201666894304441 := by
  unfold tailWord_5869984
  simp only [CollatzResearch.WordTrace]
  refine ⟨107047952583028978149068503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142730603444038637532091337 107047952583028978149068503)
  ·
    refine ⟨160571928874543467223602755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107047952583028978149068503 160571928874543467223602755)
    ·
      refine ⟨240857893311815200835404133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160571928874543467223602755 240857893311815200835404133)
      ·
        refine ⟨45160854995965350156638275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240857893311815200835404133 45160854995965350156638275)
        ·
          refine ⟨67741282493948025234957413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45160854995965350156638275 67741282493948025234957413)
          ·
            refine ⟨12701490467615254731554515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67741282493948025234957413 12701490467615254731554515)
            ·
              refine ⟨19052235701422882097331773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12701490467615254731554515 19052235701422882097331773)
              ·
                refine ⟨7144588388033580786499415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19052235701422882097331773 7144588388033580786499415)
                ·
                  refine ⟨10716882582050371179749123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144588388033580786499415 10716882582050371179749123)
                  ·
                    refine ⟨16075323873075556769623685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10716882582050371179749123 16075323873075556769623685)
                    ·
                      refine ⟨3014123226201666894304441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16075323873075556769623685 3014123226201666894304441)
                      ·
                        rfl

theorem cell23_5869984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_5869984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5869984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5869984 prefixEnd_5869984 := by exact prefixLift 5869984
  have htrace : WordTrace (prefixWord ++ tailWord_5869984) baseStart_5869984 baseEnd_5869984 := by
    simpa [prefixWord, tailWord_5869984, baseEnd_5869984] using wordTrace_append hprefix tailTrace_5869984
  have hstable : (prefixWord ++ tailWord_5869984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5869984).length < 2 ^ (prefixWord ++ tailWord_5869984).sum := by decide
  have hdescent : baseEnd_5869984 < baseStart_5869984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5869984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870001 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 3, 2, 2]
def baseStart_5870001 : Nat := 118140960795 + 5870001 * 2 ^ 59
def prefixEnd_5870001 : Nat := 4983230072969 + 3 ^ 40 * 5870001 * 2
def baseEnd_5870001 : Nat := 3014131955372793327791863

theorem tailTrace_5870001 : CollatzResearch.WordTrace tailWord_5870001 prefixEnd_5870001 3014131955372793327791863 := by
  unfold tailWord_5870001
  simp only [CollatzResearch.WordTrace]
  refine ⟨214096525206996368201505857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142731016804664245467670571 214096525206996368201505857)
  ·
    refine ⟨160572393905247276151129393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214096525206996368201505857 160572393905247276151129393)
    ·
      refine ⟨120429295428935457113347045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160572393905247276151129393 120429295428935457113347045)
      ·
        refine ⟨22580492892925398208752571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120429295428935457113347045 22580492892925398208752571)
        ·
          refine ⟨33870739339388097313128857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22580492892925398208752571 33870739339388097313128857)
          ·
            refine ⟨25403054504541072984846643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33870739339388097313128857 25403054504541072984846643)
            ·
              refine ⟨38104581756811609477269965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25403054504541072984846643 38104581756811609477269965)
              ·
                refine ⟨14289218158804353553976237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38104581756811609477269965 14289218158804353553976237)
                ·
                  refine ⟨5358456809551632582741089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14289218158804353553976237 5358456809551632582741089)
                  ·
                    refine ⟨4018842607163724437055817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358456809551632582741089 4018842607163724437055817)
                    ·
                      refine ⟨3014131955372793327791863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018842607163724437055817 3014131955372793327791863)
                      ·
                        rfl

theorem cell23_5870001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_5870001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870001 prefixEnd_5870001 := by exact prefixLift 5870001
  have htrace : WordTrace (prefixWord ++ tailWord_5870001) baseStart_5870001 baseEnd_5870001 := by
    simpa [prefixWord, tailWord_5870001, baseEnd_5870001] using wordTrace_append hprefix tailTrace_5870001
  have hstable : (prefixWord ++ tailWord_5870001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870001).length < 2 ^ (prefixWord ++ tailWord_5870001).sum := by decide
  have hdescent : baseEnd_5870001 < baseStart_5870001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870014 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_5870014 : Nat := 118140960795 + 5870014 * 2 ^ 59
def prefixEnd_5870014 : Nat := 4983230072969 + 3 ^ 40 * 5870014 * 2
def baseEnd_5870014 : Nat := 3014138630621301776929303

theorem tailTrace_5870014 : CollatzResearch.WordTrace tailWord_5870014 prefixEnd_5870014 3014138630621301776929303 := by
  unfold tailWord_5870014
  simp only [CollatzResearch.WordTrace]
  refine ⟨26762124919493658927716137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142731332903966180947819397 26762124919493658927716137)
  ·
    refine ⟨20071593689620244195787103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26762124919493658927716137 20071593689620244195787103)
    ·
      refine ⟨30107390534430366293680655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20071593689620244195787103 30107390534430366293680655)
      ·
        refine ⟨45161085801645549440520983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30107390534430366293680655 45161085801645549440520983)
        ·
          refine ⟨67741628702468324160781475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45161085801645549440520983 67741628702468324160781475)
          ·
            refine ⟨101612443053702486241172213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67741628702468324160781475 101612443053702486241172213)
            ·
              refine ⟨9526166536284608085109895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101612443053702486241172213 9526166536284608085109895)
              ·
                refine ⟨14289249804426912127664843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9526166536284608085109895 14289249804426912127664843)
                ·
                  refine ⟨21433874706640368191497265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14289249804426912127664843 21433874706640368191497265)
                  ·
                    refine ⟨16075406029980276143622949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21433874706640368191497265 16075406029980276143622949)
                    ·
                      refine ⟨3014138630621301776929303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16075406029980276143622949 3014138630621301776929303)
                      ·
                        rfl

theorem cell23_5870014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_5870014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870014 prefixEnd_5870014 := by exact prefixLift 5870014
  have htrace : WordTrace (prefixWord ++ tailWord_5870014) baseStart_5870014 baseEnd_5870014 := by
    simpa [prefixWord, tailWord_5870014, baseEnd_5870014] using wordTrace_append hprefix tailTrace_5870014
  have hstable : (prefixWord ++ tailWord_5870014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870014).length < 2 ^ (prefixWord ++ tailWord_5870014).sum := by decide
  have hdescent : baseEnd_5870014 < baseStart_5870014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870024 : List Nat := [2, 1, 3, 1, 3, 4, 2, 7]
def baseStart_5870024 : Nat := 118140960795 + 5870024 * 2 ^ 59
def prefixEnd_5870024 : Nat := 4983230072969 + 3 ^ 40 * 5870024 * 2
def baseEnd_5870024 : Nat := 111634954275105434733491

theorem tailTrace_5870024 : CollatzResearch.WordTrace tailWord_5870024 prefixEnd_5870024 111634954275105434733491 := by
  unfold tailWord_5870024
  simp only [CollatzResearch.WordTrace]
  refine ⟨107048682042956521564796563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142731576057275362086395417 107048682042956521564796563)
  ·
    refine ⟨160573023064434782347194845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107048682042956521564796563 160573023064434782347194845)
    ·
      refine ⟨60214883649163043380198067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160573023064434782347194845 60214883649163043380198067)
      ·
        refine ⟨90322325473744565070297101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60214883649163043380198067 90322325473744565070297101)
        ·
          refine ⟨33870872052654211901361413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90322325473744565070297101 33870872052654211901361413)
          ·
            refine ⟨6350788509872664731505265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33870872052654211901361413 6350788509872664731505265)
            ·
              refine ⟨4763091382404498548628949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350788509872664731505265 4763091382404498548628949)
              ·
                refine ⟨111634954275105434733491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4763091382404498548628949 111634954275105434733491)
                ·
                  rfl

theorem cell23_5870024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 7].length) (baseStart_5870024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870024 prefixEnd_5870024 := by exact prefixLift 5870024
  have htrace : WordTrace (prefixWord ++ tailWord_5870024) baseStart_5870024 baseEnd_5870024 := by
    simpa [prefixWord, tailWord_5870024, baseEnd_5870024] using wordTrace_append hprefix tailTrace_5870024
  have hstable : (prefixWord ++ tailWord_5870024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870024).length < 2 ^ (prefixWord ++ tailWord_5870024).sum := by decide
  have hdescent : baseEnd_5870024 < baseStart_5870024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870077 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_5870077 : Nat := 118140960795 + 5870077 * 2 ^ 59
def prefixEnd_5870077 : Nat := 4983230072969 + 3 ^ 40 * 5870077 * 2
def baseEnd_5870077 : Nat := 3014170979902535030441513

theorem tailTrace_5870077 : CollatzResearch.WordTrace tailWord_5870077 prefixEnd_5870077 3014170979902535030441513 := by
  unfold tailWord_5870077
  simp only [CollatzResearch.WordTrace]
  refine ⟨214099297154721033181272485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142732864769814022120848323 214099297154721033181272485)
  ·
    refine ⟨40143618216510193721488591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214099297154721033181272485 40143618216510193721488591)
    ·
      refine ⟨60215427324765290582232887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40143618216510193721488591 60215427324765290582232887)
      ·
        refine ⟨90323140987147935873349331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60215427324765290582232887 90323140987147935873349331)
        ·
          refine ⟨135484711480721903810023997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90323140987147935873349331 135484711480721903810023997)
          ·
            refine ⟨50806766805270713928758999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135484711480721903810023997 50806766805270713928758999)
            ·
              refine ⟨76210150207906070893138499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50806766805270713928758999 76210150207906070893138499)
              ·
                refine ⟨114315225311859106339707749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76210150207906070893138499 114315225311859106339707749)
                ·
                  refine ⟨21434104745973582438695203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114315225311859106339707749 21434104745973582438695203)
                  ·
                    refine ⟨32151157118960373658042805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21434104745973582438695203 32151157118960373658042805)
                    ·
                      refine ⟨3014170979902535030441513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32151157118960373658042805 3014170979902535030441513)
                      ·
                        rfl

theorem cell23_5870077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_5870077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870077 prefixEnd_5870077 := by exact prefixLift 5870077
  have htrace : WordTrace (prefixWord ++ tailWord_5870077) baseStart_5870077 baseEnd_5870077 := by
    simpa [prefixWord, tailWord_5870077, baseEnd_5870077] using wordTrace_append hprefix tailTrace_5870077
  have hstable : (prefixWord ++ tailWord_5870077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870077).length < 2 ^ (prefixWord ++ tailWord_5870077).sum := by decide
  have hdescent : baseEnd_5870077 < baseStart_5870077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870091 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 1, 4, 2]
def baseStart_5870091 : Nat := 118140960795 + 5870091 * 2 ^ 59
def prefixEnd_5870091 : Nat := 4983230072969 + 3 ^ 40 * 5870091 * 2
def baseEnd_5870091 : Nat := 3014178168631697975666449

theorem tailTrace_5870091 : CollatzResearch.WordTrace tailWord_5870091 prefixEnd_5870091 3014178168631697975666449 := by
  unfold tailWord_5870091
  simp only [CollatzResearch.WordTrace]
  refine ⟨214099807776670313572282127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142733205184446875714854751 214099807776670313572282127)
  ·
    refine ⟨321149711665005470358423191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214099807776670313572282127 321149711665005470358423191)
    ·
      refine ⟨481724567497508205537634787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321149711665005470358423191 481724567497508205537634787)
      ·
        refine ⟨722586851246262308306452181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481724567497508205537634787 722586851246262308306452181)
        ·
          refine ⟨16935629326084272850932473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 722586851246262308306452181 16935629326084272850932473)
          ·
            refine ⟨12701721994563204638199355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16935629326084272850932473 12701721994563204638199355)
            ·
              refine ⟨19052582991844806957299033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12701721994563204638199355 19052582991844806957299033)
              ·
                refine ⟨14289437243883605217974275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19052582991844806957299033 14289437243883605217974275)
                ·
                  refine ⟨21434155865825407826961413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14289437243883605217974275 21434155865825407826961413)
                  ·
                    refine ⟨4018904224842263967555265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21434155865825407826961413 4018904224842263967555265)
                    ·
                      refine ⟨3014178168631697975666449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018904224842263967555265 3014178168631697975666449)
                      ·
                        rfl

theorem cell23_5870091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4, 2].length) (baseStart_5870091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870091 prefixEnd_5870091 := by exact prefixLift 5870091
  have htrace : WordTrace (prefixWord ++ tailWord_5870091) baseStart_5870091 baseEnd_5870091 := by
    simpa [prefixWord, tailWord_5870091, baseEnd_5870091] using wordTrace_append hprefix tailTrace_5870091
  have hstable : (prefixWord ++ tailWord_5870091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870091).length < 2 ^ (prefixWord ++ tailWord_5870091).sum := by decide
  have hdescent : baseEnd_5870091 < baseStart_5870091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870094 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5870094 : Nat := 118140960795 + 5870094 * 2 ^ 59
def prefixEnd_5870094 : Nat := 4983230072969 + 3 ^ 40 * 5870094 * 2
def baseEnd_5870094 : Nat := 3014179709073661463928935

theorem tailTrace_5870094 : CollatzResearch.WordTrace tailWord_5870094 prefixEnd_5870094 3014179709073661463928935 := by
  unfold tailWord_5870094
  simp only [CollatzResearch.WordTrace]
  refine ⟨26762489649457430635580167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142733278130439630056427557 26762489649457430635580167)
  ·
    refine ⟨40143734474186145953370251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26762489649457430635580167 40143734474186145953370251)
    ·
      refine ⟨60215601711279218930055377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40143734474186145953370251 60215601711279218930055377)
      ·
        refine ⟨45161701283459414197541533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60215601711279218930055377 45161701283459414197541533)
        ·
          refine ⟨16935637981297280324078075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45161701283459414197541533 16935637981297280324078075)
          ·
            refine ⟨25403456971945920486117113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16935637981297280324078075 25403456971945920486117113)
            ·
              refine ⟨19052592728959440364587835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25403456971945920486117113 19052592728959440364587835)
              ·
                refine ⟨28578889093439160546881753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19052592728959440364587835 28578889093439160546881753)
                ·
                  refine ⟨21434166820079370410161315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28578889093439160546881753 21434166820079370410161315)
                  ·
                    refine ⟨32151250230119055615241973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21434166820079370410161315 32151250230119055615241973)
                    ·
                      refine ⟨3014179709073661463928935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32151250230119055615241973 3014179709073661463928935)
                      ·
                        rfl

theorem cell23_5870094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5870094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870094 prefixEnd_5870094 := by exact prefixLift 5870094
  have htrace : WordTrace (prefixWord ++ tailWord_5870094) baseStart_5870094 baseEnd_5870094 := by
    simpa [prefixWord, tailWord_5870094, baseEnd_5870094] using wordTrace_append hprefix tailTrace_5870094
  have hstable : (prefixWord ++ tailWord_5870094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870094).length < 2 ^ (prefixWord ++ tailWord_5870094).sum := by decide
  have hdescent : baseEnd_5870094 < baseStart_5870094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870107 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 3]
def baseStart_5870107 : Nat := 118140960795 + 5870107 * 2 ^ 59
def prefixEnd_5870107 : Nat := 4983230072969 + 3 ^ 40 * 5870107 * 2
def baseEnd_5870107 : Nat := 3014186384322169913066375

theorem tailTrace_5870107 : CollatzResearch.WordTrace tailWord_5870107 prefixEnd_5870107 3014186384322169913066375 := by
  unfold tailWord_5870107
  simp only [CollatzResearch.WordTrace]
  refine ⟨214100391344612348304864575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142733594229741565536576383 214100391344612348304864575)
  ·
    refine ⟨321150587016918522457296863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214100391344612348304864575 321150587016918522457296863)
    ·
      refine ⟨481725880525377783685945295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321150587016918522457296863 481725880525377783685945295)
      ·
        refine ⟨722588820788066675528917943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481725880525377783685945295 722588820788066675528917943)
        ·
          refine ⟨1083883231182100013293376915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722588820788066675528917943 1083883231182100013293376915)
          ·
            refine ⟨1625824846773150019940065373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083883231182100013293376915 1625824846773150019940065373)
            ·
              refine ⟨609684317539931257477524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1625824846773150019940065373 609684317539931257477524515)
              ·
                refine ⟨914526476309896886216286773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609684317539931257477524515 914526476309896886216286773)
                ·
                  refine ⟨85736857154052833082776885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 914526476309896886216286773 85736857154052833082776885)
                  ·
                    refine ⟨8037830358192453101510333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85736857154052833082776885 8037830358192453101510333)
                    ·
                      refine ⟨3014186384322169913066375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8037830358192453101510333 3014186384322169913066375)
                      ·
                        rfl

theorem cell23_5870107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 3].length) (baseStart_5870107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870107 prefixEnd_5870107 := by exact prefixLift 5870107
  have htrace : WordTrace (prefixWord ++ tailWord_5870107) baseStart_5870107 baseEnd_5870107 := by
    simpa [prefixWord, tailWord_5870107, baseEnd_5870107] using wordTrace_append hprefix tailTrace_5870107
  have hstable : (prefixWord ++ tailWord_5870107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870107).length < 2 ^ (prefixWord ++ tailWord_5870107).sum := by decide
  have hdescent : baseEnd_5870107 < baseStart_5870107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870108 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5870108 : Nat := 118140960795 + 5870108 * 2 ^ 59
def prefixEnd_5870108 : Nat := 4983230072969 + 3 ^ 40 * 5870108 * 2
def baseEnd_5870108 : Nat := 3014186897802824409153871

theorem tailTrace_5870108 : CollatzResearch.WordTrace tailWord_5870108 prefixEnd_5870108 3014186897802824409153871 := by
  unfold tailWord_5870108
  simp only [CollatzResearch.WordTrace]
  refine ⟨107050213908804362737825489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142733618545072483650433985 107050213908804362737825489)
  ·
    refine ⟨80287660431603272053369117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107050213908804362737825489 80287660431603272053369117)
    ·
      refine ⟨30107872661851227020013419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80287660431603272053369117 30107872661851227020013419)
      ·
        refine ⟨45161808992776840530020129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30107872661851227020013419 45161808992776840530020129)
        ·
          refine ⟨33871356744582630397515097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45161808992776840530020129 33871356744582630397515097)
          ·
            refine ⟨25403517558436972798136323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33871356744582630397515097 25403517558436972798136323)
            ·
              refine ⟨38105276337655459197204485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25403517558436972798136323 38105276337655459197204485)
              ·
                refine ⟨7144739313310398599475841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38105276337655459197204485 7144739313310398599475841)
                ·
                  refine ⟨5358554484982798949606881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7144739313310398599475841 5358554484982798949606881)
                  ·
                    refine ⟨4018915863737099212205161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358554484982798949606881 4018915863737099212205161)
                    ·
                      refine ⟨3014186897802824409153871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4018915863737099212205161 3014186897802824409153871)
                      ·
                        rfl

theorem cell23_5870108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5870108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870108 prefixEnd_5870108 := by exact prefixLift 5870108
  have htrace : WordTrace (prefixWord ++ tailWord_5870108) baseStart_5870108 baseEnd_5870108 := by
    simpa [prefixWord, tailWord_5870108, baseEnd_5870108] using wordTrace_append hprefix tailTrace_5870108
  have hstable : (prefixWord ++ tailWord_5870108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870108).length < 2 ^ (prefixWord ++ tailWord_5870108).sum := by decide
  have hdescent : baseEnd_5870108 < baseStart_5870108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870144 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 2, 5]
def baseStart_5870144 : Nat := 118140960795 + 5870144 * 2 ^ 59
def prefixEnd_5870144 : Nat := 4983230072969 + 3 ^ 40 * 5870144 * 2
def baseEnd_5870144 : Nat := 1004735127702128756101235

theorem tailTrace_5870144 : CollatzResearch.WordTrace tailWord_5870144 prefixEnd_5870144 1004735127702128756101235 := by
  unfold tailWord_5870144
  simp only [CollatzResearch.WordTrace]
  refine ⟨107050870422739151811980743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142734493896985535749307657 107050870422739151811980743)
  ·
    refine ⟨160576305634108727717971115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107050870422739151811980743 160576305634108727717971115)
    ·
      refine ⟨240864458451163091576956673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160576305634108727717971115 240864458451163091576956673)
      ·
        refine ⟨180648343838372318682717505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240864458451163091576956673 180648343838372318682717505)
        ·
          refine ⟨135486257878779239012038129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180648343838372318682717505 135486257878779239012038129)
          ·
            refine ⟨101614693409084429259028597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135486257878779239012038129 101614693409084429259028597)
            ·
              refine ⟨9526377507101665243033931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101614693409084429259028597 9526377507101665243033931)
              ·
                refine ⟨14289566260652497864550897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9526377507101665243033931 14289566260652497864550897)
                ·
                  refine ⟨10717174695489373398413173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14289566260652497864550897 10717174695489373398413173)
                  ·
                    refine ⟨1004735127702128756101235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10717174695489373398413173 1004735127702128756101235)
                    ·
                      rfl

theorem cell23_5870144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_5870144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870144 prefixEnd_5870144 := by exact prefixLift 5870144
  have htrace : WordTrace (prefixWord ++ tailWord_5870144) baseStart_5870144 baseEnd_5870144 := by
    simpa [prefixWord, tailWord_5870144, baseEnd_5870144] using wordTrace_append hprefix tailTrace_5870144
  have hstable : (prefixWord ++ tailWord_5870144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870144).length < 2 ^ (prefixWord ++ tailWord_5870144).sum := by decide
  have hdescent : baseEnd_5870144 < baseStart_5870144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_5870207 : Nat := 118140960795 + 5870207 * 2 ^ 59
def prefixEnd_5870207 : Nat := 4983230072969 + 3 ^ 40 * 5870207 * 2
def baseEnd_5870207 : Nat := 3014237732387619521815915

theorem tailTrace_5870207 : CollatzResearch.WordTrace tailWord_5870207 prefixEnd_5870207 3014237732387619521815915 := by
  unfold tailWord_5870207
  simp only [CollatzResearch.WordTrace]
  refine ⟨214104038644250065383504875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142736025762833376922336583 214104038644250065383504875)
  ·
    refine ⟨321156057966375098075257313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214104038644250065383504875 321156057966375098075257313)
    ·
      refine ⟨240867043474781323556442985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321156057966375098075257313 240867043474781323556442985)
      ·
        refine ⟨180650282606085992667332239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240867043474781323556442985 180650282606085992667332239)
        ·
          refine ⟨270975423909128989000998359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180650282606085992667332239 270975423909128989000998359)
          ·
            refine ⟨406463135863693483501497539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270975423909128989000998359 406463135863693483501497539)
            ·
              refine ⟨609694703795540225252246309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406463135863693483501497539 609694703795540225252246309)
              ·
                refine ⟨114317756961663792234796183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609694703795540225252246309 114317756961663792234796183)
                ·
                  refine ⟨171476635442495688352194275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114317756961663792234796183 171476635442495688352194275)
                  ·
                    refine ⟨257214953163743532528291413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171476635442495688352194275 257214953163743532528291413)
                    ·
                      refine ⟨3014237732387619521815915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 257214953163743532528291413 3014237732387619521815915)
                      ·
                        rfl

theorem cell23_5870207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_5870207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870207 prefixEnd_5870207 := by exact prefixLift 5870207
  have htrace : WordTrace (prefixWord ++ tailWord_5870207) baseStart_5870207 baseEnd_5870207 := by
    simpa [prefixWord, tailWord_5870207, baseEnd_5870207] using wordTrace_append hprefix tailTrace_5870207
  have hstable : (prefixWord ++ tailWord_5870207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870207).length < 2 ^ (prefixWord ++ tailWord_5870207).sum := by decide
  have hdescent : baseEnd_5870207 < baseStart_5870207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870208 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 1, 4]
def baseStart_5870208 : Nat := 118140960795 + 5870208 * 2 ^ 59
def prefixEnd_5870208 : Nat := 4983230072969 + 3 ^ 40 * 5870208 * 2
def baseEnd_5870208 : Nat := 1004746081956091339301137

theorem tailTrace_5870208 : CollatzResearch.WordTrace tailWord_5870208 prefixEnd_5870208 1004746081956091339301137 := by
  unfold tailWord_5870208
  simp only [CollatzResearch.WordTrace]
  refine ⟨107052037558623221277145639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142736050078164295036194185 107052037558623221277145639)
  ·
    refine ⟨160578056337934831915718459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107052037558623221277145639 160578056337934831915718459)
    ·
      refine ⟨240867084506902247873577689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160578056337934831915718459 240867084506902247873577689)
      ·
        refine ⟨180650313380176685905183267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240867084506902247873577689 180650313380176685905183267)
        ·
          refine ⟨270975470070265028857774901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180650313380176685905183267 270975470070265028857774901)
          ·
            refine ⟨25403950319087346455416397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270975470070265028857774901 25403950319087346455416397)
            ·
              refine ⟨9526481369657754920781149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25403950319087346455416397 9526481369657754920781149)
              ·
                refine ⟨3572430513621658095292931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9526481369657754920781149 3572430513621658095292931)
                ·
                  refine ⟨5358645770432487142939397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572430513621658095292931 5358645770432487142939397)
                  ·
                    refine ⟨1004746081956091339301137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358645770432487142939397 1004746081956091339301137)
                    ·
                      rfl

theorem cell23_5870208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 4].length) (baseStart_5870208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870208 prefixEnd_5870208 := by exact prefixLift 5870208
  have htrace : WordTrace (prefixWord ++ tailWord_5870208) baseStart_5870208 baseEnd_5870208 := by
    simpa [prefixWord, tailWord_5870208, baseEnd_5870208] using wordTrace_append hprefix tailTrace_5870208
  have hstable : (prefixWord ++ tailWord_5870208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870208).length < 2 ^ (prefixWord ++ tailWord_5870208).sum := by decide
  have hdescent : baseEnd_5870208 < baseStart_5870208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870218 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_5870218 : Nat := 118140960795 + 5870218 * 2 ^ 59
def prefixEnd_5870218 : Nat := 4983230072969 + 3 ^ 40 * 5870218 * 2
def baseEnd_5870218 : Nat := 3014243380674818978778365

theorem tailTrace_5870218 : CollatzResearch.WordTrace tailWord_5870218 prefixEnd_5870218 3014243380674818978778365 := by
  unfold tailWord_5870218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53526109961802553565538827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142736293231473476174770205 53526109961802553565538827)
  ·
    refine ⟨80289164942703830348308241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53526109961802553565538827 80289164942703830348308241)
    ·
      refine ⟨60216873707027872761231181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80289164942703830348308241 60216873707027872761231181)
      ·
        refine ⟨22581327640135452285461693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60216873707027872761231181 22581327640135452285461693)
        ·
          refine ⟨8467997865050794607048135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22581327640135452285461693 8467997865050794607048135)
          ·
            refine ⟨12701996797576191910572203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8467997865050794607048135 12701996797576191910572203)
            ·
              refine ⟨19052995196364287865858305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12701996797576191910572203 19052995196364287865858305)
              ·
                refine ⟨14289746397273215899393729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19052995196364287865858305 14289746397273215899393729)
                ·
                  refine ⟨10717309797954911924545297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14289746397273215899393729 10717309797954911924545297)
                  ·
                    refine ⟨8037982348466183943408973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10717309797954911924545297 8037982348466183943408973)
                    ·
                      refine ⟨3014243380674818978778365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8037982348466183943408973 3014243380674818978778365)
                      ·
                        rfl

theorem cell23_5870218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_5870218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870218 prefixEnd_5870218 := by exact prefixLift 5870218
  have htrace : WordTrace (prefixWord ++ tailWord_5870218) baseStart_5870218 baseEnd_5870218 := by
    simpa [prefixWord, tailWord_5870218, baseEnd_5870218] using wordTrace_append hprefix tailTrace_5870218
  have hstable : (prefixWord ++ tailWord_5870218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870218).length < 2 ^ (prefixWord ++ tailWord_5870218).sum := by decide
  have hdescent : baseEnd_5870218 < baseStart_5870218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870268 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_5870268 : Nat := 118140960795 + 5870268 * 2 ^ 59
def prefixEnd_5870268 : Nat := 4983230072969 + 3 ^ 40 * 5870268 * 2
def baseEnd_5870268 : Nat := 1004756351569181261051045

theorem tailTrace_5870268 : CollatzResearch.WordTrace tailWord_5870268 prefixEnd_5870268 1004756351569181261051045 := by
  unfold tailWord_5870268
  simp only [CollatzResearch.WordTrace]
  refine ⟨107053131748514536400737729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142737508998019381867650305 107053131748514536400737729)
  ·
    refine ⟨80289848811385902300553297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107053131748514536400737729 80289848811385902300553297)
    ·
      refine ⟨60217386608539426725414973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80289848811385902300553297 60217386608539426725414973)
      ·
        refine ⟨22581519978202285022030615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60217386608539426725414973 22581519978202285022030615)
        ·
          refine ⟨33872279967303427533045923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22581519978202285022030615 33872279967303427533045923)
          ·
            refine ⟨50808419950955141299568885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33872279967303427533045923 50808419950955141299568885)
            ·
              refine ⟨4763289370402044496834583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50808419950955141299568885 4763289370402044496834583)
              ·
                refine ⟨7144934055603066745251875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763289370402044496834583 7144934055603066745251875)
                ·
                  refine ⟨10717401083404600117877813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144934055603066745251875 10717401083404600117877813)
                  ·
                    refine ⟨1004756351569181261051045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10717401083404600117877813 1004756351569181261051045)
                    ·
                      rfl

theorem cell23_5870268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_5870268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870268 prefixEnd_5870268 := by exact prefixLift 5870268
  have htrace : WordTrace (prefixWord ++ tailWord_5870268) baseStart_5870268 baseEnd_5870268 := by
    simpa [prefixWord, tailWord_5870268, baseEnd_5870268] using wordTrace_append hprefix tailTrace_5870268
  have hstable : (prefixWord ++ tailWord_5870268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870268).length < 2 ^ (prefixWord ++ tailWord_5870268).sum := by decide
  have hdescent : baseEnd_5870268 < baseStart_5870268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870282 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_5870282 : Nat := 118140960795 + 5870282 * 2 ^ 59
def prefixEnd_5870282 : Nat := 4983230072969 + 3 ^ 40 * 5870282 * 2
def baseEnd_5870282 : Nat := 3014276243436706728378071

theorem tailTrace_5870282 : CollatzResearch.WordTrace tailWord_5870282 prefixEnd_5870282 3014276243436706728378071 := by
  unfold tailWord_5870282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53526693529744588298121275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142737849412652235461656733 53526693529744588298121275)
  ·
    refine ⟨80290040294616882447181913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53526693529744588298121275 80290040294616882447181913)
    ·
      refine ⟨60217530220962661835386435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80290040294616882447181913 60217530220962661835386435)
      ·
        refine ⟨90326295331443992753079653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60217530220962661835386435 90326295331443992753079653)
        ·
          refine ⟨16936180374645748641202435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90326295331443992753079653 16936180374645748641202435)
          ·
            refine ⟨25404270561968622961803653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16936180374645748641202435 25404270561968622961803653)
            ·
              refine ⟨4763300730369116805338185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25404270561968622961803653 4763300730369116805338185)
              ·
                refine ⟨3572475547776837604003639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4763300730369116805338185 3572475547776837604003639)
                ·
                  refine ⟨5358713321665256406005459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572475547776837604003639 5358713321665256406005459)
                  ·
                    refine ⟨8038069982497884609008189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5358713321665256406005459 8038069982497884609008189)
                    ·
                      refine ⟨3014276243436706728378071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038069982497884609008189 3014276243436706728378071)
                      ·
                        rfl

theorem cell23_5870282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_5870282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870282 prefixEnd_5870282 := by exact prefixLift 5870282
  have htrace : WordTrace (prefixWord ++ tailWord_5870282) baseStart_5870282 baseEnd_5870282 := by
    simpa [prefixWord, tailWord_5870282, baseEnd_5870282] using wordTrace_append hprefix tailTrace_5870282
  have hstable : (prefixWord ++ tailWord_5870282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870282).length < 2 ^ (prefixWord ++ tailWord_5870282).sum := by decide
  have hdescent : baseEnd_5870282 < baseStart_5870282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870305 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_5870305 : Nat := 118140960795 + 5870305 * 2 ^ 59
def prefixEnd_5870305 : Nat := 4983230072969 + 3 ^ 40 * 5870305 * 2
def baseEnd_5870305 : Nat := 3014288053491760138390465

theorem tailTrace_5870305 : CollatzResearch.WordTrace tailWord_5870305 prefixEnd_5870305 3014288053491760138390465 := by
  unfold tailWord_5870305
  simp only [CollatzResearch.WordTrace]
  refine ⟨214107612997895028120572369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142738408665263352080381579 214107612997895028120572369)
  ·
    refine ⟨160580709748421271090429277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214107612997895028120572369 160580709748421271090429277)
    ·
      refine ⟨60217766155657976658910979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160580709748421271090429277 60217766155657976658910979)
      ·
        refine ⟨90326649233486964988366469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60217766155657976658910979 90326649233486964988366469)
        ·
          refine ⟨16936246731278805935318713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90326649233486964988366469 16936246731278805935318713)
          ·
            refine ⟨12702185048459104451489035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16936246731278805935318713 12702185048459104451489035)
            ·
              refine ⟨19053277572688656677233553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702185048459104451489035 19053277572688656677233553)
              ·
                refine ⟨14289958179516492507925165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19053277572688656677233553 14289958179516492507925165)
                ·
                  refine ⟨5358734317318684690471937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14289958179516492507925165 5358734317318684690471937)
                  ·
                    refine ⟨4019050737989013517853953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358734317318684690471937 4019050737989013517853953)
                    ·
                      refine ⟨3014288053491760138390465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019050737989013517853953 3014288053491760138390465)
                      ·
                        rfl

theorem cell23_5870305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_5870305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870305 prefixEnd_5870305 := by exact prefixLift 5870305
  have htrace : WordTrace (prefixWord ++ tailWord_5870305) baseStart_5870305 baseEnd_5870305 := by
    simpa [prefixWord, tailWord_5870305, baseEnd_5870305] using wordTrace_append hprefix tailTrace_5870305
  have hstable : (prefixWord ++ tailWord_5870305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870305).length < 2 ^ (prefixWord ++ tailWord_5870305).sum := by decide
  have hdescent : baseEnd_5870305 < baseStart_5870305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870321 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_5870321 : Nat := 118140960795 + 5870321 * 2 ^ 59
def prefixEnd_5870321 : Nat := 4983230072969 + 3 ^ 40 * 5870321 * 2
def baseEnd_5870321 : Nat := 3014296269182232075790391

theorem tailTrace_5870321 : CollatzResearch.WordTrace tailWord_5870321 prefixEnd_5870321 3014296269182232075790391 := by
  unfold tailWord_5870321
  simp only [CollatzResearch.WordTrace]
  refine ⟨214108196565837062853154817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142738797710558041902103211 214108196565837062853154817)
  ·
    refine ⟨160581147424377797139866113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214108196565837062853154817 160581147424377797139866113)
    ·
      refine ⟨120435860568283347854899585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160581147424377797139866113 120435860568283347854899585)
      ·
        refine ⟨90326895426212510891174689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120435860568283347854899585 90326895426212510891174689)
        ·
          refine ⟨67745171569659383168381017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90326895426212510891174689 67745171569659383168381017)
          ·
            refine ⟨50808878677244537376285763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67745171569659383168381017 50808878677244537376285763)
            ·
              refine ⟨76213318015866806064428645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50808878677244537376285763 76213318015866806064428645)
              ·
                refine ⟨14289997127975026137080371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76213318015866806064428645 14289997127975026137080371)
                ·
                  refine ⟨21434995691962539205620557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14289997127975026137080371 21434995691962539205620557)
                  ·
                    refine ⟨8038123384485952202107709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21434995691962539205620557 8038123384485952202107709)
                    ·
                      refine ⟨3014296269182232075790391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038123384485952202107709 3014296269182232075790391)
                      ·
                        rfl

theorem cell23_5870321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_5870321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870321 prefixEnd_5870321 := by exact prefixLift 5870321
  have htrace : WordTrace (prefixWord ++ tailWord_5870321) baseStart_5870321 baseEnd_5870321 := by
    simpa [prefixWord, tailWord_5870321, baseEnd_5870321] using wordTrace_append hprefix tailTrace_5870321
  have hstable : (prefixWord ++ tailWord_5870321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870321).length < 2 ^ (prefixWord ++ tailWord_5870321).sum := by decide
  have hdescent : baseEnd_5870321 < baseStart_5870321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870322 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_5870322 : Nat := 118140960795 + 5870322 * 2 ^ 59
def prefixEnd_5870322 : Nat := 4983230072969 + 3 ^ 40 * 5870322 * 2
def baseEnd_5870322 : Nat := 3014296782662886571877887

theorem tailTrace_5870322 : CollatzResearch.WordTrace tailWord_5870322 prefixEnd_5870322 3014296782662886571877887 := by
  unfold tailWord_5870322
  simp only [CollatzResearch.WordTrace]
  refine ⟨53527058259708360005985305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142738822025888960015960813 53527058259708360005985305)
  ·
    refine ⟨40145293694781270004488979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53527058259708360005985305 40145293694781270004488979)
    ·
      refine ⟨60217940542171905006733469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40145293694781270004488979 60217940542171905006733469)
      ·
        refine ⟨22581727703314464377525051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60217940542171905006733469 22581727703314464377525051)
        ·
          refine ⟨33872591554971696566287577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22581727703314464377525051 33872591554971696566287577)
          ·
            refine ⟨25404443666228772424715683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33872591554971696566287577 25404443666228772424715683)
            ·
              refine ⟨38106665499343158637073525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25404443666228772424715683 38106665499343158637073525)
              ·
                refine ⟨3572499890563421122225643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38106665499343158637073525 3572499890563421122225643)
                ·
                  refine ⟨5358749835845131683338465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572499890563421122225643 5358749835845131683338465)
                  ·
                    refine ⟨4019062376883848762503849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358749835845131683338465 4019062376883848762503849)
                    ·
                      refine ⟨3014296782662886571877887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019062376883848762503849 3014296782662886571877887)
                      ·
                        rfl

theorem cell23_5870322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_5870322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870322 prefixEnd_5870322 := by exact prefixLift 5870322
  have htrace : WordTrace (prefixWord ++ tailWord_5870322) baseStart_5870322 baseEnd_5870322 := by
    simpa [prefixWord, tailWord_5870322, baseEnd_5870322] using wordTrace_append hprefix tailTrace_5870322
  have hstable : (prefixWord ++ tailWord_5870322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870322).length < 2 ^ (prefixWord ++ tailWord_5870322).sum := by decide
  have hdescent : baseEnd_5870322 < baseStart_5870322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870355 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 2, 1, 3]
def baseStart_5870355 : Nat := 118140960795 + 5870355 * 2 ^ 59
def prefixEnd_5870355 : Nat := 4983230072969 + 3 ^ 40 * 5870355 * 2
def baseEnd_5870355 : Nat := 3014313727524484942765235

theorem tailTrace_5870355 : CollatzResearch.WordTrace tailWord_5870355 prefixEnd_5870355 3014313727524484942765235 := by
  unfold tailWord_5870355
  simp only [CollatzResearch.WordTrace]
  refine ⟨214109436647713886659892519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142739624431809257773261679 214109436647713886659892519)
  ·
    refine ⟨321164154971570829989838779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214109436647713886659892519 321164154971570829989838779)
    ·
      refine ⟨481746232457356244984758169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321164154971570829989838779 481746232457356244984758169)
      ·
        refine ⟨361309674343017183738568627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481746232457356244984758169 361309674343017183738568627)
        ·
          refine ⟨541964511514525775607852941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361309674343017183738568627 541964511514525775607852941)
          ·
            refine ⟨203236691817947165852944853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541964511514525775607852941 203236691817947165852944853)
            ·
              refine ⟨4763359964483136699678395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 203236691817947165852944853 4763359964483136699678395)
              ·
                refine ⟨7145039946724705049517593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763359964483136699678395 7145039946724705049517593)
                ·
                  refine ⟨5358779960043528787138195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145039946724705049517593 5358779960043528787138195)
                  ·
                    refine ⟨8038169940065293180707293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5358779960043528787138195 8038169940065293180707293)
                    ·
                      refine ⟨3014313727524484942765235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038169940065293180707293 3014313727524484942765235)
                      ·
                        rfl

theorem cell23_5870355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 2, 1, 3].length) (baseStart_5870355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870355 prefixEnd_5870355 := by exact prefixLift 5870355
  have htrace : WordTrace (prefixWord ++ tailWord_5870355) baseStart_5870355 baseEnd_5870355 := by
    simpa [prefixWord, tailWord_5870355, baseEnd_5870355] using wordTrace_append hprefix tailTrace_5870355
  have hstable : (prefixWord ++ tailWord_5870355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870355).length < 2 ^ (prefixWord ++ tailWord_5870355).sum := by decide
  have hdescent : baseEnd_5870355 < baseStart_5870355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870382 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5870382 : Nat := 118140960795 + 5870382 * 2 ^ 59
def prefixEnd_5870382 : Nat := 4983230072969 + 3 ^ 40 * 5870382 * 2
def baseEnd_5870382 : Nat := 3014327591502156337127611

theorem tailTrace_5870382 : CollatzResearch.WordTrace tailWord_5870382 prefixEnd_5870382 3014327591502156337127611 := by
  unfold tailWord_5870382
  simp only [CollatzResearch.WordTrace]
  refine ⟨26763802677327008783890675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142740280945744046847416933 26763802677327008783890675)
  ·
    refine ⟨40145704015990513175836013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26763802677327008783890675 40145704015990513175836013)
    ·
      refine ⟨15054639005996442440938505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40145704015990513175836013 15054639005996442440938505)
      ·
        refine ⟨11290979254497331830703879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15054639005996442440938505 11290979254497331830703879)
        ·
          refine ⟨16936468881745997746055819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11290979254497331830703879 16936468881745997746055819)
          ·
            refine ⟨25404703322618996619083729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16936468881745997746055819 25404703322618996619083729)
            ·
              refine ⟨19053527491964247464312797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25404703322618996619083729 19053527491964247464312797)
              ·
                refine ⟨7145072809486592799117299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19053527491964247464312797 7145072809486592799117299)
                ·
                  refine ⟨10717609214229889198675949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7145072809486592799117299 10717609214229889198675949)
                  ·
                    refine ⟨4019103455336208449503481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10717609214229889198675949 4019103455336208449503481)
                    ·
                      refine ⟨3014327591502156337127611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019103455336208449503481 3014327591502156337127611)
                      ·
                        rfl

theorem cell23_5870382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5870382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870382 prefixEnd_5870382 := by exact prefixLift 5870382
  have htrace : WordTrace (prefixWord ++ tailWord_5870382) baseStart_5870382 baseEnd_5870382 := by
    simpa [prefixWord, tailWord_5870382, baseEnd_5870382] using wordTrace_append hprefix tailTrace_5870382
  have hstable : (prefixWord ++ tailWord_5870382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870382).length < 2 ^ (prefixWord ++ tailWord_5870382).sum := by decide
  have hdescent : baseEnd_5870382 < baseStart_5870382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870384 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 9]
def baseStart_5870384 : Nat := 118140960795 + 5870384 * 2 ^ 59
def prefixEnd_5870384 : Nat := 4983230072969 + 3 ^ 40 * 5870384 * 2
def baseEnd_5870384 : Nat := 334925402051496147700289

theorem tailTrace_5870384 : CollatzResearch.WordTrace tailWord_5870384 prefixEnd_5870384 334925402051496147700289 := by
  unfold tailWord_5870384
  simp only [CollatzResearch.WordTrace]
  refine ⟨107055247182304412306349103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142740329576405883075132137 107055247182304412306349103)
  ·
    refine ⟨160582870773456618459523655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107055247182304412306349103 160582870773456618459523655)
    ·
      refine ⟨240874306160184927689285483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160582870773456618459523655 240874306160184927689285483)
      ·
        refine ⟨361311459240277391533928225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240874306160184927689285483 361311459240277391533928225)
        ·
          refine ⟨270983594430208043650446169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361311459240277391533928225 270983594430208043650446169)
          ·
            refine ⟨203237695822656032737834627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270983594430208043650446169 203237695822656032737834627)
            ·
              refine ⟨304856543733984049106751941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203237695822656032737834627 304856543733984049106751941)
              ·
                refine ⟨57160601950122009207515989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304856543733984049106751941 57160601950122009207515989)
                ·
                  refine ⟨334925402051496147700289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57160601950122009207515989 334925402051496147700289)
                  ·
                    rfl

theorem cell23_5870384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_5870384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870384 prefixEnd_5870384 := by exact prefixLift 5870384
  have htrace : WordTrace (prefixWord ++ tailWord_5870384) baseStart_5870384 baseEnd_5870384 := by
    simpa [prefixWord, tailWord_5870384, baseEnd_5870384] using wordTrace_append hprefix tailTrace_5870384
  have hstable : (prefixWord ++ tailWord_5870384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870384).length < 2 ^ (prefixWord ++ tailWord_5870384).sum := by decide
  have hdescent : baseEnd_5870384 < baseStart_5870384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870412 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 2, 2, 2]
def baseStart_5870412 : Nat := 118140960795 + 5870412 * 2 ^ 59
def prefixEnd_5870412 : Nat := 4983230072969 + 3 ^ 40 * 5870412 * 2
def baseEnd_5870412 : Nat := 3014342995921791219752473

theorem tailTrace_5870412 : CollatzResearch.WordTrace tailWord_5870412 prefixEnd_5870412 3014342995921791219752473 := by
  unfold tailWord_5870412
  simp only [CollatzResearch.WordTrace]
  refine ⟨107055757804253692697358745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142741010405671590263144993 107055757804253692697358745)
  ·
    refine ⟨80291818353190269523019059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107055757804253692697358745 80291818353190269523019059)
    ·
      refine ⟨120437727529785404284528589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80291818353190269523019059 120437727529785404284528589)
      ·
        refine ⟨45164147823669526606698221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120437727529785404284528589 45164147823669526606698221)
        ·
          refine ⟨16936555433876072477511833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45164147823669526606698221 16936555433876072477511833)
          ·
            refine ⟨12702416575407054358133875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16936555433876072477511833 12702416575407054358133875)
            ·
              refine ⟨19053624863110581537200813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702416575407054358133875 19053624863110581537200813)
              ·
                refine ⟨7145109323666468076450305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19053624863110581537200813 7145109323666468076450305)
                ·
                  refine ⟨5358831992749851057337729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145109323666468076450305 5358831992749851057337729)
                  ·
                    refine ⟨4019123994562388293003297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358831992749851057337729 4019123994562388293003297)
                    ·
                      refine ⟨3014342995921791219752473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019123994562388293003297 3014342995921791219752473)
                      ·
                        rfl

theorem cell23_5870412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_5870412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870412 prefixEnd_5870412 := by exact prefixLift 5870412
  have htrace : WordTrace (prefixWord ++ tailWord_5870412) baseStart_5870412 baseEnd_5870412 := by
    simpa [prefixWord, tailWord_5870412, baseEnd_5870412] using wordTrace_append hprefix tailTrace_5870412
  have hstable : (prefixWord ++ tailWord_5870412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870412).length < 2 ^ (prefixWord ++ tailWord_5870412).sum := by decide
  have hdescent : baseEnd_5870412 < baseStart_5870412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870462 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5870462 : Nat := 118140960795 + 5870462 * 2 ^ 59
def prefixEnd_5870462 : Nat := 4983230072969 + 3 ^ 40 * 5870462 * 2
def baseEnd_5870462 : Nat := 3014368669954516024127243

theorem tailTrace_5870462 : CollatzResearch.WordTrace tailWord_5870462 prefixEnd_5870462 3014368669954516024127243 := by
  unfold tailWord_5870462
  simp only [CollatzResearch.WordTrace]
  refine ⟨26764167407290780491754705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142742226172217495956025093 26764167407290780491754705)
  ·
    refine ⟨20073125555468085368816029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26764167407290780491754705 20073125555468085368816029)
    ·
      refine ⟨7527422083300532013306011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20073125555468085368816029 7527422083300532013306011)
      ·
        refine ⟨11291133124950798019959017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7527422083300532013306011 11291133124950798019959017)
        ·
          refine ⟨8468349843713098514969263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11291133124950798019959017 8468349843713098514969263)
          ·
            refine ⟨12702524765569647772453895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468349843713098514969263 12702524765569647772453895)
            ·
              refine ⟨19053787148354471658680843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702524765569647772453895 19053787148354471658680843)
              ·
                refine ⟨28580680722531707488021265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19053787148354471658680843 28580680722531707488021265)
                ·
                  refine ⟨21435510541898780616015949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28580680722531707488021265 21435510541898780616015949)
                  ·
                    refine ⟨8038316453212042731005981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21435510541898780616015949 8038316453212042731005981)
                    ·
                      refine ⟨3014368669954516024127243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038316453212042731005981 3014368669954516024127243)
                      ·
                        rfl

theorem cell23_5870462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5870462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870462 prefixEnd_5870462 := by exact prefixLift 5870462
  have htrace : WordTrace (prefixWord ++ tailWord_5870462) baseStart_5870462 baseEnd_5870462 := by
    simpa [prefixWord, tailWord_5870462, baseEnd_5870462] using wordTrace_append hprefix tailTrace_5870462
  have hstable : (prefixWord ++ tailWord_5870462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870462).length < 2 ^ (prefixWord ++ tailWord_5870462).sum := by decide
  have hdescent : baseEnd_5870462 < baseStart_5870462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870482 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5870482 : Nat := 118140960795 + 5870482 * 2 ^ 59
def prefixEnd_5870482 : Nat := 4983230072969 + 3 ^ 40 * 5870482 * 2
def baseEnd_5870482 : Nat := 1004792979855868648625717

theorem tailTrace_5870482 : CollatzResearch.WordTrace tailWord_5870482 prefixEnd_5870482 1004792979855868648625717 := by
  unfold tailWord_5870482
  simp only [CollatzResearch.WordTrace]
  refine ⟨53528517179563446837441425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142742712478835858233177133 53528517179563446837441425)
  ·
    refine ⟨40146387884672585128081069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53528517179563446837441425 40146387884672585128081069)
    ·
      refine ⟨15054895456752219423030401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40146387884672585128081069 15054895456752219423030401)
      ·
        refine ⟨11291171592564164567272801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15054895456752219423030401 11291171592564164567272801)
        ·
          refine ⟨8468378694423123425454601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11291171592564164567272801 8468378694423123425454601)
          ·
            refine ⟨6351284020817342569090951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8468378694423123425454601 6351284020817342569090951)
            ·
              refine ⟨9526926031226013853636427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351284020817342569090951 9526926031226013853636427)
              ·
                refine ⟨14290389046839020780454641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9526926031226013853636427 14290389046839020780454641)
                ·
                  refine ⟨10717791785129265585340981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14290389046839020780454641 10717791785129265585340981)
                  ·
                    refine ⟨1004792979855868648625717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10717791785129265585340981 1004792979855868648625717)
                    ·
                      rfl

theorem cell23_5870482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5870482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870482 prefixEnd_5870482 := by exact prefixLift 5870482
  have htrace : WordTrace (prefixWord ++ tailWord_5870482) baseStart_5870482 baseEnd_5870482 := by
    simpa [prefixWord, tailWord_5870482, baseEnd_5870482] using wordTrace_append hprefix tailTrace_5870482
  have hstable : (prefixWord ++ tailWord_5870482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870482).length < 2 ^ (prefixWord ++ tailWord_5870482).sum := by decide
  have hdescent : baseEnd_5870482 < baseStart_5870482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870485 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_5870485 : Nat := 118140960795 + 5870485 * 2 ^ 59
def prefixEnd_5870485 : Nat := 4983230072969 + 3 ^ 40 * 5870485 * 2
def baseEnd_5870485 : Nat := 3014380480009569434139637

theorem tailTrace_5870485 : CollatzResearch.WordTrace tailWord_5870485 prefixEnd_5870485 3014380480009569434139637 := by
  unfold tailWord_5870485
  simp only [CollatzResearch.WordTrace]
  refine ⟨214114178137242918862124909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142742785424828612574749939 214114178137242918862124909)
  ·
    refine ⟨80292816801466094573296841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214114178137242918862124909 80292816801466094573296841)
    ·
      refine ⟨60219612601099570929972631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80292816801466094573296841 60219612601099570929972631)
      ·
        refine ⟨90329418901649356394958947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60219612601099570929972631 90329418901649356394958947)
        ·
          refine ⟨135494128352474034592438421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90329418901649356394958947 135494128352474034592438421)
          ·
            refine ⟨6351287266522220371520551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135494128352474034592438421 6351287266522220371520551)
            ·
              refine ⟨9526930899783330557280827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351287266522220371520551 9526930899783330557280827)
              ·
                refine ⟨14290396349674995835921241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9526930899783330557280827 14290396349674995835921241)
                ·
                  refine ⟨10717797262256246876940931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14290396349674995835921241 10717797262256246876940931)
                  ·
                    refine ⟨16076695893384370315411397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10717797262256246876940931 16076695893384370315411397)
                    ·
                      refine ⟨3014380480009569434139637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16076695893384370315411397 3014380480009569434139637)
                      ·
                        rfl

theorem cell23_5870485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_5870485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870485 prefixEnd_5870485 := by exact prefixLift 5870485
  have htrace : WordTrace (prefixWord ++ tailWord_5870485) baseStart_5870485 baseEnd_5870485 := by
    simpa [prefixWord, tailWord_5870485, baseEnd_5870485] using wordTrace_append hprefix tailTrace_5870485
  have hstable : (prefixWord ++ tailWord_5870485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870485).length < 2 ^ (prefixWord ++ tailWord_5870485).sum := by decide
  have hdescent : baseEnd_5870485 < baseStart_5870485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870498 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5870498 : Nat := 118140960795 + 5870498 * 2 ^ 59
def prefixEnd_5870498 : Nat := 4983230072969 + 3 ^ 40 * 5870498 * 2
def baseEnd_5870498 : Nat := 3014387155258077883277077

theorem tailTrace_5870498 : CollatzResearch.WordTrace tailWord_5870498 prefixEnd_5870498 3014387155258077883277077 := by
  unfold tailWord_5870498
  simp only [CollatzResearch.WordTrace]
  refine ⟨53528663071548955520587037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142743101524130548054898765 53528663071548955520587037)
  ·
    refine ⟨20073248651830858320220139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53528663071548955520587037 20073248651830858320220139)
    ·
      refine ⟨30109872977746287480330209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20073248651830858320220139 30109872977746287480330209)
      ·
        refine ⟨22582404733309715610247657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30109872977746287480330209 22582404733309715610247657)
        ·
          refine ⟨16936803549982286707685743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22582404733309715610247657 16936803549982286707685743)
          ·
            refine ⟨25405205324973430061528615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16936803549982286707685743 25405205324973430061528615)
            ·
              refine ⟨38107807987460145092292923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25405205324973430061528615 38107807987460145092292923)
              ·
                refine ⟨57161711981190217638439385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38107807987460145092292923 57161711981190217638439385)
                ·
                  refine ⟨42871283985892663228829539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57161711981190217638439385 42871283985892663228829539)
                  ·
                    refine ⟨64306925978838994843244309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42871283985892663228829539 64306925978838994843244309)
                    ·
                      refine ⟨3014387155258077883277077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64306925978838994843244309 3014387155258077883277077)
                      ·
                        rfl

theorem cell23_5870498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5870498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870498 prefixEnd_5870498 := by exact prefixLift 5870498
  have htrace : WordTrace (prefixWord ++ tailWord_5870498) baseStart_5870498 baseEnd_5870498 := by
    simpa [prefixWord, tailWord_5870498, baseEnd_5870498] using wordTrace_append hprefix tailTrace_5870498
  have hstable : (prefixWord ++ tailWord_5870498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870498).length < 2 ^ (prefixWord ++ tailWord_5870498).sum := by decide
  have hdescent : baseEnd_5870498 < baseStart_5870498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870535 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_5870535 : Nat := 118140960795 + 5870535 * 2 ^ 59
def prefixEnd_5870535 : Nat := 4983230072969 + 3 ^ 40 * 5870535 * 2
def baseEnd_5870535 : Nat := 3014406154042294238514407

theorem tailTrace_5870535 : CollatzResearch.WordTrace tailWord_5870535 prefixEnd_5870535 3014406154042294238514407 := by
  unfold tailWord_5870535
  simp only [CollatzResearch.WordTrace]
  refine ⟨214116001787061777401445059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142744001191374518267630039 214116001787061777401445059)
  ·
    refine ⟨321174002680592666102167589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214116001787061777401445059 321174002680592666102167589)
    ·
      refine ⟨60220125502611124894156423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321174002680592666102167589 60220125502611124894156423)
      ·
        refine ⟨90330188253916687341234635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60220125502611124894156423 90330188253916687341234635)
        ·
          refine ⟨135495282380875031011851953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90330188253916687341234635 135495282380875031011851953)
          ·
            refine ⟨101621461785656273258888965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135495282380875031011851953 101621461785656273258888965)
            ·
              refine ⟨19054024084810551236041681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101621461785656273258888965 19054024084810551236041681)
              ·
                refine ⟨14290518063607913427031261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19054024084810551236041681 14290518063607913427031261)
                ·
                  refine ⟨5358944273852967535136723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14290518063607913427031261 5358944273852967535136723)
                  ·
                    refine ⟨8038416410779451302705085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5358944273852967535136723 8038416410779451302705085)
                    ·
                      refine ⟨3014406154042294238514407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038416410779451302705085 3014406154042294238514407)
                      ·
                        rfl

theorem cell23_5870535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_5870535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870535 prefixEnd_5870535 := by exact prefixLift 5870535
  have htrace : WordTrace (prefixWord ++ tailWord_5870535) baseStart_5870535 baseEnd_5870535 := by
    simpa [prefixWord, tailWord_5870535, baseEnd_5870535] using wordTrace_append hprefix tailTrace_5870535
  have hstable : (prefixWord ++ tailWord_5870535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870535).length < 2 ^ (prefixWord ++ tailWord_5870535).sum := by decide
  have hdescent : baseEnd_5870535 < baseStart_5870535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870545 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 2, 3, 2]
def baseStart_5870545 : Nat := 118140960795 + 5870545 * 2 ^ 59
def prefixEnd_5870545 : Nat := 4983230072969 + 3 ^ 40 * 5870545 * 2
def baseEnd_5870545 : Nat := 3014411288848839199389361

theorem tailTrace_5870545 : CollatzResearch.WordTrace tailWord_5870545 prefixEnd_5870545 3014411288848839199389361 := by
  unfold tailWord_5870545
  simp only [CollatzResearch.WordTrace]
  refine ⟨214116366517025549109309089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142744244344683699406206059 214116366517025549109309089)
  ·
    refine ⟨160587274887769161831981817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214116366517025549109309089 160587274887769161831981817)
    ·
      refine ⟨120440456165826871373986363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160587274887769161831981817 120440456165826871373986363)
      ·
        refine ⟨180660684248740307060979545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120440456165826871373986363 180660684248740307060979545)
        ·
          refine ⟨135495513186555230295734659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180660684248740307060979545 135495513186555230295734659)
          ·
            refine ⟨203243269779832845443601989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135495513186555230295734659 203243269779832845443601989)
            ·
              refine ⟨38108113083718658520675373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203243269779832845443601989 38108113083718658520675373)
              ·
                refine ⟨14290542406394496945253265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38108113083718658520675373 14290542406394496945253265)
                ·
                  refine ⟨10717906804795872708939949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14290542406394496945253265 10717906804795872708939949)
                  ·
                    refine ⟨4019215051798452265852481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10717906804795872708939949 4019215051798452265852481)
                    ·
                      refine ⟨3014411288848839199389361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019215051798452265852481 3014411288848839199389361)
                      ·
                        rfl

theorem cell23_5870545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_5870545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870545 prefixEnd_5870545 := by exact prefixLift 5870545
  have htrace : WordTrace (prefixWord ++ tailWord_5870545) baseStart_5870545 baseEnd_5870545 := by
    simpa [prefixWord, tailWord_5870545, baseEnd_5870545] using wordTrace_append hprefix tailTrace_5870545
  have hstable : (prefixWord ++ tailWord_5870545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870545).length < 2 ^ (prefixWord ++ tailWord_5870545).sum := by decide
  have hdescent : baseEnd_5870545 < baseStart_5870545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870585 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 2, 4]
def baseStart_5870585 : Nat := 118140960795 + 5870585 * 2 ^ 59
def prefixEnd_5870585 : Nat := 4983230072969 + 3 ^ 40 * 5870585 * 2
def baseEnd_5870585 : Nat := 1004810609358339680963059

theorem tailTrace_5870585 : CollatzResearch.WordTrace tailWord_5870585 prefixEnd_5870585 1004810609358339680963059 := by
  unfold tailWord_5870585
  simp only [CollatzResearch.WordTrace]
  refine ⟨214117825436880635940765209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142745216957920423960510139 214117825436880635940765209)
  ·
    refine ⟨160588369077660476955573907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214117825436880635940765209 160588369077660476955573907)
    ·
      refine ⟨240882553616490715433360861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160588369077660476955573907 240882553616490715433360861)
      ·
        refine ⟨90330957606184018287510323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240882553616490715433360861 90330957606184018287510323)
        ·
          refine ⟨135496436409276027431265485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90330957606184018287510323 135496436409276027431265485)
          ·
            refine ⟨50811163653478510286724557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135496436409276027431265485 50811163653478510286724557)
            ·
              refine ⟨19054186370054441357521709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50811163653478510286724557 19054186370054441357521709)
              ·
                refine ⟨7145319888770415509070641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19054186370054441357521709 7145319888770415509070641)
                ·
                  refine ⟨5358989916577811631802981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145319888770415509070641 5358989916577811631802981)
                  ·
                    refine ⟨1004810609358339680963059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358989916577811631802981 1004810609358339680963059)
                    ·
                      rfl

theorem cell23_5870585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_5870585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870585 prefixEnd_5870585 := by exact prefixLift 5870585
  have htrace : WordTrace (prefixWord ++ tailWord_5870585) baseStart_5870585 baseEnd_5870585 := by
    simpa [prefixWord, tailWord_5870585, baseEnd_5870585] using wordTrace_append hprefix tailTrace_5870585
  have hstable : (prefixWord ++ tailWord_5870585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870585).length < 2 ^ (prefixWord ++ tailWord_5870585).sum := by decide
  have hdescent : baseEnd_5870585 < baseStart_5870585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870588 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_5870588 : Nat := 118140960795 + 5870588 * 2 ^ 59
def prefixEnd_5870588 : Nat := 4983230072969 + 3 ^ 40 * 5870588 * 2
def baseEnd_5870588 : Nat := 3014433368516982531151663

theorem tailTrace_5870588 : CollatzResearch.WordTrace tailWord_5870588 prefixEnd_5870588 3014433368516982531151663 := by
  unfold tailWord_5870588
  simp only [CollatzResearch.WordTrace]
  refine ⟨107058967427934883726562209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142745289903913178302082945 107058967427934883726562209)
  ·
    refine ⟨80294225570951162794921657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107058967427934883726562209 80294225570951162794921657)
    ·
      refine ⟨60220669178213372096191243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80294225570951162794921657 60220669178213372096191243)
      ·
        refine ⟨90331003767320058144286865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60220669178213372096191243 90331003767320058144286865)
        ·
          refine ⟨67748252825490043608215149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90331003767320058144286865 67748252825490043608215149)
          ·
            refine ⟨25405594809558766353080681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67748252825490043608215149 25405594809558766353080681)
            ·
              refine ⟨19054196107169074764810511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25405594809558766353080681 19054196107169074764810511)
              ·
                refine ⟨28581294160753612147215767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19054196107169074764810511 28581294160753612147215767)
                ·
                  refine ⟨42871941241130418220823651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28581294160753612147215767 42871941241130418220823651)
                  ·
                    refine ⟨64307911861695627331235477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42871941241130418220823651 64307911861695627331235477)
                    ·
                      refine ⟨3014433368516982531151663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64307911861695627331235477 3014433368516982531151663)
                      ·
                        rfl

theorem cell23_5870588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_5870588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870588 prefixEnd_5870588 := by exact prefixLift 5870588
  have htrace : WordTrace (prefixWord ++ tailWord_5870588) baseStart_5870588 baseEnd_5870588 := by
    simpa [prefixWord, tailWord_5870588, baseEnd_5870588] using wordTrace_append hprefix tailTrace_5870588
  have hstable : (prefixWord ++ tailWord_5870588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870588).length < 2 ^ (prefixWord ++ tailWord_5870588).sum := by decide
  have hdescent : baseEnd_5870588 < baseStart_5870588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870626 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_5870626 : Nat := 118140960795 + 5870626 * 2 ^ 59
def prefixEnd_5870626 : Nat := 4983230072969 + 3 ^ 40 * 5870626 * 2
def baseEnd_5870626 : Nat := 3014452880781853382476489

theorem tailTrace_5870626 : CollatzResearch.WordTrace tailWord_5870626 prefixEnd_5870626 3014452880781853382476489 := by
  unfold tailWord_5870626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53529830207433024985751933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142746213886488066628671821 53529830207433024985751933)
  ·
    refine ⟨20073686327787384369656975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53529830207433024985751933 20073686327787384369656975)
    ·
      refine ⟨30110529491681076554485463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20073686327787384369656975 30110529491681076554485463)
      ·
        refine ⟨45165794237521614831728195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30110529491681076554485463 45165794237521614831728195)
        ·
          refine ⟨67748691356282422247592293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45165794237521614831728195 67748691356282422247592293)
          ·
            refine ⟨12702879629302954171423555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67748691356282422247592293 12702879629302954171423555)
            ·
              refine ⟨19054319443954431257135333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702879629302954171423555 19054319443954431257135333)
              ·
                refine ⟨3572684895741455860712875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19054319443954431257135333 3572684895741455860712875)
                ·
                  refine ⟨5359027343612183791069313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572684895741455860712875 5359027343612183791069313)
                  ·
                    refine ⟨4019270507709137843301985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5359027343612183791069313 4019270507709137843301985)
                    ·
                      refine ⟨3014452880781853382476489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019270507709137843301985 3014452880781853382476489)
                      ·
                        rfl

theorem cell23_5870626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_5870626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870626 prefixEnd_5870626 := by exact prefixLift 5870626
  have htrace : WordTrace (prefixWord ++ tailWord_5870626) baseStart_5870626 baseEnd_5870626 := by
    simpa [prefixWord, tailWord_5870626, baseEnd_5870626] using wordTrace_append hprefix tailTrace_5870626
  have hstable : (prefixWord ++ tailWord_5870626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870626).length < 2 ^ (prefixWord ++ tailWord_5870626).sum := by decide
  have hdescent : baseEnd_5870626 < baseStart_5870626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870635 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 5, 3, 2]
def baseStart_5870635 : Nat := 118140960795 + 5870635 * 2 ^ 59
def prefixEnd_5870635 : Nat := 4983230072969 + 3 ^ 40 * 5870635 * 2
def baseEnd_5870635 : Nat := 3014457502107743847263947

theorem tailTrace_5870635 : CollatzResearch.WordTrace tailWord_5870635 prefixEnd_5870635 3014457502107743847263947 := by
  unfold tailWord_5870635
  simp only [CollatzResearch.WordTrace]
  refine ⟨214119649086699494480085359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142746432724466329653390239 214119649086699494480085359)
  ·
    refine ⟨321179473630049241720128039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214119649086699494480085359 321179473630049241720128039)
    ·
      refine ⟨481769210445073862580192059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321179473630049241720128039 481769210445073862580192059)
      ·
        refine ⟨722653815667610793870288089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481769210445073862580192059 722653815667610793870288089)
        ·
          refine ⟨541990361750708095402716067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722653815667610793870288089 541990361750708095402716067)
          ·
            refine ⟨812985542626062143104074101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541990361750708095402716067 812985542626062143104074101)
            ·
              refine ⟨76217394621193325916006947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 812985542626062143104074101 76217394621193325916006947)
              ·
                refine ⟨114326091931789988874010421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76217394621193325916006947 114326091931789988874010421)
                ·
                  refine ⟨10718071118605311456938477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114326091931789988874010421 10718071118605311456938477)
                  ·
                    refine ⟨4019276669476991796351929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10718071118605311456938477 4019276669476991796351929)
                    ·
                      refine ⟨3014457502107743847263947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019276669476991796351929 3014457502107743847263947)
                      ·
                        rfl

theorem cell23_5870635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3, 2].length) (baseStart_5870635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870635 prefixEnd_5870635 := by exact prefixLift 5870635
  have htrace : WordTrace (prefixWord ++ tailWord_5870635) baseStart_5870635 baseEnd_5870635 := by
    simpa [prefixWord, tailWord_5870635, baseEnd_5870635] using wordTrace_append hprefix tailTrace_5870635
  have hstable : (prefixWord ++ tailWord_5870635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870635).length < 2 ^ (prefixWord ++ tailWord_5870635).sum := by decide
  have hdescent : baseEnd_5870635 < baseStart_5870635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870642 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_5870642 : Nat := 118140960795 + 5870642 * 2 ^ 59
def prefixEnd_5870642 : Nat := 4983230072969 + 3 ^ 40 * 5870642 * 2
def baseEnd_5870642 : Nat := 3014461096472325319876415

theorem tailTrace_5870642 : CollatzResearch.WordTrace tailWord_5870642 prefixEnd_5870642 3014461096472325319876415 := by
  unfold tailWord_5870642
  simp only [CollatzResearch.WordTrace]
  refine ⟨53529976099418533668897545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142746602931782756450393453 53529976099418533668897545)
  ·
    refine ⟨40147482074563900251673159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53529976099418533668897545 40147482074563900251673159)
    ·
      refine ⟨60221223111845850377509739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40147482074563900251673159 60221223111845850377509739)
      ·
        refine ⟨90331834667768775566264609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60221223111845850377509739 90331834667768775566264609)
        ·
          refine ⟨67748876000826581674698457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90331834667768775566264609 67748876000826581674698457)
          ·
            refine ⟨50811657000619936256023843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67748876000826581674698457 50811657000619936256023843)
            ·
              refine ⟨76217485500929904384035765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50811657000619936256023843 76217485500929904384035765)
              ·
                refine ⟨7145389265712178536003353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76217485500929904384035765 7145389265712178536003353)
                ·
                  refine ⟨5359041949284133902002515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145389265712178536003353 5359041949284133902002515)
                  ·
                    refine ⟨8038562923926200853003773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359041949284133902002515 8038562923926200853003773)
                    ·
                      refine ⟨3014461096472325319876415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038562923926200853003773 3014461096472325319876415)
                      ·
                        rfl

theorem cell23_5870642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_5870642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870642 prefixEnd_5870642 := by exact prefixLift 5870642
  have htrace : WordTrace (prefixWord ++ tailWord_5870642) baseStart_5870642 baseEnd_5870642 := by
    simpa [prefixWord, tailWord_5870642, baseEnd_5870642] using wordTrace_append hprefix tailTrace_5870642
  have hstable : (prefixWord ++ tailWord_5870642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870642).length < 2 ^ (prefixWord ++ tailWord_5870642).sum := by decide
  have hdescent : baseEnd_5870642 < baseStart_5870642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870652 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_5870652 : Nat := 118140960795 + 5870652 * 2 ^ 59
def prefixEnd_5870652 : Nat := 4983230072969 + 3 ^ 40 * 5870652 * 2
def baseEnd_5870652 : Nat := 3014466231278870280751369

theorem tailTrace_5870652 : CollatzResearch.WordTrace tailWord_5870652 prefixEnd_5870652 3014466231278870280751369 := by
  unfold tailWord_5870652
  simp only [CollatzResearch.WordTrace]
  refine ⟨107060134563818953191727105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142746846085091937588969473 107060134563818953191727105)
  ·
    refine ⟨80295100922864214893795329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107060134563818953191727105 80295100922864214893795329)
    ·
      refine ⟨60221325692148161170346497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80295100922864214893795329 60221325692148161170346497)
      ·
        refine ⟨45165994269111120877759873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60221325692148161170346497 45165994269111120877759873)
        ·
          refine ⟨33874495701833340658319905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45165994269111120877759873 33874495701833340658319905)
          ·
            refine ⟨25405871776375005493739929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33874495701833340658319905 25405871776375005493739929)
            ·
              refine ⟨19054403832281254120304947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25405871776375005493739929 19054403832281254120304947)
              ·
                refine ⟨28581605748421881180457421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19054403832281254120304947 28581605748421881180457421)
                ·
                  refine ⟨10718102155658205442671533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28581605748421881180457421 10718102155658205442671533)
                  ·
                    refine ⟨4019288308371827041001825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10718102155658205442671533 4019288308371827041001825)
                    ·
                      refine ⟨3014466231278870280751369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019288308371827041001825 3014466231278870280751369)
                      ·
                        rfl

theorem cell23_5870652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_5870652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870652 prefixEnd_5870652 := by exact prefixLift 5870652
  have htrace : WordTrace (prefixWord ++ tailWord_5870652) baseStart_5870652 baseEnd_5870652 := by
    simpa [prefixWord, tailWord_5870652, baseEnd_5870652] using wordTrace_append hprefix tailTrace_5870652
  have hstable : (prefixWord ++ tailWord_5870652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870652).length < 2 ^ (prefixWord ++ tailWord_5870652).sum := by decide
  have hdescent : baseEnd_5870652 < baseStart_5870652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870665 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 3, 4, 2]
def baseStart_5870665 : Nat := 118140960795 + 5870665 * 2 ^ 59
def prefixEnd_5870665 : Nat := 4983230072969 + 3 ^ 40 * 5870665 * 2
def baseEnd_5870665 : Nat := 3014472906527378729888809

theorem tailTrace_5870665 : CollatzResearch.WordTrace tailWord_5870665 prefixEnd_5870665 3014472906527378729888809 := by
  unfold tailWord_5870665
  simp only [CollatzResearch.WordTrace]
  refine ⟨214120743276590809603677449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142747162184393873069118299 214120743276590809603677449)
  ·
    refine ⟨160590557457443107202758087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214120743276590809603677449 160590557457443107202758087)
    ·
      refine ⟨240885836186164660804137131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160590557457443107202758087 240885836186164660804137131)
      ·
        refine ⟨361328754279246991206205697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240885836186164660804137131 361328754279246991206205697)
        ·
          refine ⟨270996565709435243404654273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361328754279246991206205697 270996565709435243404654273)
          ·
            refine ⟨203247424282076432553490705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270996565709435243404654273 203247424282076432553490705)
            ·
              refine ⟨152435568211557324415118029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203247424282076432553490705 152435568211557324415118029)
              ·
                refine ⟨57163338079333996655669261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152435568211557324415118029 57163338079333996655669261)
                ·
                  refine ⟨21436251779750248745875973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57163338079333996655669261 21436251779750248745875973)
                  ·
                    refine ⟨4019297208703171639851745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21436251779750248745875973 4019297208703171639851745)
                    ·
                      refine ⟨3014472906527378729888809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019297208703171639851745 3014472906527378729888809)
                      ·
                        rfl

theorem cell23_5870665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 4, 2].length) (baseStart_5870665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870665 prefixEnd_5870665 := by exact prefixLift 5870665
  have htrace : WordTrace (prefixWord ++ tailWord_5870665) baseStart_5870665 baseEnd_5870665 := by
    simpa [prefixWord, tailWord_5870665, baseEnd_5870665] using wordTrace_append hprefix tailTrace_5870665
  have hstable : (prefixWord ++ tailWord_5870665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870665).length < 2 ^ (prefixWord ++ tailWord_5870665).sum := by decide
  have hdescent : baseEnd_5870665 < baseStart_5870665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870668 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5870668 : Nat := 118140960795 + 5870668 * 2 ^ 59
def prefixEnd_5870668 : Nat := 4983230072969 + 3 ^ 40 * 5870668 * 2
def baseEnd_5870668 : Nat := 3014474446969342218151295

theorem tailTrace_5870668 : CollatzResearch.WordTrace tailWord_5870668 prefixEnd_5870668 3014474446969342218151295 := by
  unfold tailWord_5870668
  simp only [CollatzResearch.WordTrace]
  refine ⟨107060426347789970558018329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142747235130386627410691105 107060426347789970558018329)
  ·
    refine ⟨80295319760842477918513747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107060426347789970558018329 80295319760842477918513747)
    ·
      refine ⟨120442979641263716877770621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80295319760842477918513747 120442979641263716877770621)
      ·
        refine ⟨45166117365473893829163983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120442979641263716877770621 45166117365473893829163983)
        ·
          refine ⟨67749176048210840743745975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45166117365473893829163983 67749176048210840743745975)
          ·
            refine ⟨101623764072316261115618963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67749176048210840743745975 101623764072316261115618963)
            ·
              refine ⟨152435646108474391673428445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101623764072316261115618963 152435646108474391673428445)
              ·
                refine ⟨57163367290677896877535667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152435646108474391673428445 57163367290677896877535667)
                ·
                  refine ⟨85745050936016845316303501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57163367290677896877535667 85745050936016845316303501)
                  ·
                    refine ⟨32154394101006316993613813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85745050936016845316303501 32154394101006316993613813)
                    ·
                      refine ⟨3014474446969342218151295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32154394101006316993613813 3014474446969342218151295)
                      ·
                        rfl

theorem cell23_5870668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5870668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870668 prefixEnd_5870668 := by exact prefixLift 5870668
  have htrace : WordTrace (prefixWord ++ tailWord_5870668) baseStart_5870668 baseEnd_5870668 := by
    simpa [prefixWord, tailWord_5870668, baseEnd_5870668] using wordTrace_append hprefix tailTrace_5870668
  have hstable : (prefixWord ++ tailWord_5870668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870668).length < 2 ^ (prefixWord ++ tailWord_5870668).sum := by decide
  have hdescent : baseEnd_5870668 < baseStart_5870668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870695 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_5870695 : Nat := 118140960795 + 5870695 * 2 ^ 59
def prefixEnd_5870695 : Nat := 4983230072969 + 3 ^ 40 * 5870695 * 2
def baseEnd_5870695 : Nat := 3014488310947013612513671

theorem tailTrace_5870695 : CollatzResearch.WordTrace tailWord_5870695 prefixEnd_5870695 3014488310947013612513671 := by
  unfold tailWord_5870695
  simp only [CollatzResearch.WordTrace]
  refine ⟨214121837466482124727269539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142747891644321416484846359 214121837466482124727269539)
  ·
    refine ⟨321182756199723187090904309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214121837466482124727269539 321182756199723187090904309)
    ·
      refine ⟨30110883393724048789772279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321182756199723187090904309 30110883393724048789772279)
      ·
        refine ⟨45166325090586073184658419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30110883393724048789772279 45166325090586073184658419)
        ·
          refine ⟨67749487635879109776987629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45166325090586073184658419 67749487635879109776987629)
          ·
            refine ⟨25406057863454666166370361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67749487635879109776987629 25406057863454666166370361)
            ·
              refine ⟨19054543397590999624777771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25406057863454666166370361 19054543397590999624777771)
              ·
                refine ⟨28581815096386499437166657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19054543397590999624777771 28581815096386499437166657)
                ·
                  refine ⟨21436361322289874577874993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28581815096386499437166657 21436361322289874577874993)
                  ·
                    refine ⟨16077270991717405933406245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21436361322289874577874993 16077270991717405933406245)
                    ·
                      refine ⟨3014488310947013612513671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16077270991717405933406245 3014488310947013612513671)
                      ·
                        rfl

theorem cell23_5870695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_5870695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870695 prefixEnd_5870695 := by exact prefixLift 5870695
  have htrace : WordTrace (prefixWord ++ tailWord_5870695) baseStart_5870695 baseEnd_5870695 := by
    simpa [prefixWord, tailWord_5870695, baseEnd_5870695] using wordTrace_append hprefix tailTrace_5870695
  have hstable : (prefixWord ++ tailWord_5870695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870695).length < 2 ^ (prefixWord ++ tailWord_5870695).sum := by decide
  have hdescent : baseEnd_5870695 < baseStart_5870695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870750 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5870750 : Nat := 118140960795 + 5870750 * 2 ^ 59
def prefixEnd_5870750 : Nat := 4983230072969 + 3 ^ 40 * 5870750 * 2
def baseEnd_5870750 : Nat := 3014516552383010897325919

theorem tailTrace_5870750 : CollatzResearch.WordTrace tailWord_5870750 prefixEnd_5870750 3014516552383010897325919 := by
  unfold tailWord_5870750
  simp only [CollatzResearch.WordTrace]
  refine ⟨26765480435160358640065213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142749228987521912747014469 26765480435160358640065213)
  ·
    refine ⟨10037055163185134490024455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26765480435160358640065213 10037055163185134490024455)
    ·
      refine ⟨15055582744777701735036683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10037055163185134490024455 15055582744777701735036683)
      ·
        refine ⟨22583374117166552602555025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15055582744777701735036683 22583374117166552602555025)
        ·
          refine ⟨16937530587874914451916269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22583374117166552602555025 16937530587874914451916269)
          ·
            refine ⟨6351573970453092919468601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16937530587874914451916269 6351573970453092919468601)
            ·
              refine ⟨4763680477839819689601451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6351573970453092919468601 4763680477839819689601451)
              ·
                refine ⟨7145520716759729534402177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763680477839819689601451 7145520716759729534402177)
                ·
                  refine ⟨5359140537569797150801633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145520716759729534402177 5359140537569797150801633)
                  ·
                    refine ⟨4019355403177347863101225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5359140537569797150801633 4019355403177347863101225)
                    ·
                      refine ⟨3014516552383010897325919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019355403177347863101225 3014516552383010897325919)
                      ·
                        rfl

theorem cell23_5870750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5870750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870750 prefixEnd_5870750 := by exact prefixLift 5870750
  have htrace : WordTrace (prefixWord ++ tailWord_5870750) baseStart_5870750 baseEnd_5870750 := by
    simpa [prefixWord, tailWord_5870750, baseEnd_5870750] using wordTrace_append hprefix tailTrace_5870750
  have hstable : (prefixWord ++ tailWord_5870750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870750).length < 2 ^ (prefixWord ++ tailWord_5870750).sum := by decide
  have hdescent : baseEnd_5870750 < baseStart_5870750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870792 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_5870792 : Nat := 118140960795 + 5870792 * 2 ^ 59
def prefixEnd_5870792 : Nat := 4983230072969 + 3 ^ 40 * 5870792 * 2
def baseEnd_5870792 : Nat := 3014538118570499733000725

theorem tailTrace_5870792 : CollatzResearch.WordTrace tailWord_5870792 prefixEnd_5870792 3014538118570499733000725 := by
  unfold tailWord_5870792
  simp only [CollatzResearch.WordTrace]
  refine ⟨107062687673565355146775315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142750250231420473529033753 107062687673565355146775315)
  ·
    refine ⟨160594031510348032720162973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107062687673565355146775315 160594031510348032720162973)
    ·
      refine ⟨60222761816380512270061115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160594031510348032720162973 60222761816380512270061115)
      ·
        refine ⟨90334142724570768405091673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60222761816380512270061115 90334142724570768405091673)
        ·
          refine ⟨67750607043428076303818755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90334142724570768405091673 67750607043428076303818755)
          ·
            refine ⟨101625910565142114455728133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67750607043428076303818755 101625910565142114455728133)
            ·
              refine ⟨19054858230964146460449025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101625910565142114455728133 19054858230964146460449025)
              ·
                refine ⟨14291143673223109845336769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19054858230964146460449025 14291143673223109845336769)
                ·
                  refine ⟨10718357754917332384002577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14291143673223109845336769 10718357754917332384002577)
                  ·
                    refine ⟨8038768316187999288001933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10718357754917332384002577 8038768316187999288001933)
                    ·
                      refine ⟨3014538118570499733000725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038768316187999288001933 3014538118570499733000725)
                      ·
                        rfl

theorem cell23_5870792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_5870792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870792 prefixEnd_5870792 := by exact prefixLift 5870792
  have htrace : WordTrace (prefixWord ++ tailWord_5870792) baseStart_5870792 baseEnd_5870792 := by
    simpa [prefixWord, tailWord_5870792, baseEnd_5870792] using wordTrace_append hprefix tailTrace_5870792
  have hstable : (prefixWord ++ tailWord_5870792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870792).length < 2 ^ (prefixWord ++ tailWord_5870792).sum := by decide
  have hdescent : baseEnd_5870792 < baseStart_5870792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870842 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_5870842 : Nat := 118140960795 + 5870842 * 2 ^ 59
def prefixEnd_5870842 : Nat := 4983230072969 + 3 ^ 40 * 5870842 * 2
def baseEnd_5870842 : Nat := 1004854597534408179125165

theorem tailTrace_5870842 : CollatzResearch.WordTrace tailWord_5870842 prefixEnd_5870842 1004854597534408179125165 := by
  unfold tailWord_5870842
  simp only [CollatzResearch.WordTrace]
  refine ⟨53531799749237392208217695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142751465997966379221913853 53531799749237392208217695)
  ·
    refine ⟨80297699623856088312326543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53531799749237392208217695 80297699623856088312326543)
    ·
      refine ⟨120446549435784132468489815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80297699623856088312326543 120446549435784132468489815)
      ·
        refine ⟨180669824153676198702734723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120446549435784132468489815 180669824153676198702734723)
        ·
          refine ⟨271004736230514298054102085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180669824153676198702734723 271004736230514298054102085)
          ·
            refine ⟨50813388043221430885144141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271004736230514298054102085 50813388043221430885144141)
            ·
              refine ⟨19055020516208036581929053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50813388043221430885144141 19055020516208036581929053)
              ·
                refine ⟨7145632693578013718223395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19055020516208036581929053 7145632693578013718223395)
                ·
                  refine ⟨10718449040367020577335093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7145632693578013718223395 10718449040367020577335093)
                  ·
                    refine ⟨1004854597534408179125165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10718449040367020577335093 1004854597534408179125165)
                    ·
                      rfl

theorem cell23_5870842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_5870842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870842 prefixEnd_5870842 := by exact prefixLift 5870842
  have htrace : WordTrace (prefixWord ++ tailWord_5870842) baseStart_5870842 baseEnd_5870842 := by
    simpa [prefixWord, tailWord_5870842, baseEnd_5870842] using wordTrace_append hprefix tailTrace_5870842
  have hstable : (prefixWord ++ tailWord_5870842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870842).length < 2 ^ (prefixWord ++ tailWord_5870842).sum := by decide
  have hdescent : baseEnd_5870842 < baseStart_5870842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870856 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_5870856 : Nat := 118140960795 + 5870856 * 2 ^ 59
def prefixEnd_5870856 : Nat := 4983230072969 + 3 ^ 40 * 5870856 * 2
def baseEnd_5870856 : Nat := 3014570981332387482600431

theorem tailTrace_5870856 : CollatzResearch.WordTrace tailWord_5870856 prefixEnd_5870856 3014570981332387482600431 := by
  unfold tailWord_5870856
  simp only [CollatzResearch.WordTrace]
  refine ⟨107063854809449424611940211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142751806412599232815920281 107063854809449424611940211)
  ·
    refine ⟨160595782214174136917910317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107063854809449424611940211 160595782214174136917910317)
    ·
      refine ⟨60223418330315301344216369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160595782214174136917910317 60223418330315301344216369)
      ·
        refine ⟨45167563747736476008162277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60223418330315301344216369 45167563747736476008162277)
        ·
          refine ⟨8468918202700589251530427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45167563747736476008162277 8468918202700589251530427)
          ·
            refine ⟨12703377304050883877295641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468918202700589251530427 12703377304050883877295641)
            ·
              refine ⟨9527532978038162907971731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12703377304050883877295641 9527532978038162907971731)
              ·
                refine ⟨14291299467057244361957597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9527532978038162907971731 14291299467057244361957597)
                ·
                  refine ⟨5359237300146466635734099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14291299467057244361957597 5359237300146466635734099)
                  ·
                    refine ⟨8038855950219699953601149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359237300146466635734099 8038855950219699953601149)
                    ·
                      refine ⟨3014570981332387482600431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038855950219699953601149 3014570981332387482600431)
                      ·
                        rfl

theorem cell23_5870856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_5870856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870856 prefixEnd_5870856 := by exact prefixLift 5870856
  have htrace : WordTrace (prefixWord ++ tailWord_5870856) baseStart_5870856 baseEnd_5870856 := by
    simpa [prefixWord, tailWord_5870856, baseEnd_5870856] using wordTrace_append hprefix tailTrace_5870856
  have hstable : (prefixWord ++ tailWord_5870856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870856).length < 2 ^ (prefixWord ++ tailWord_5870856).sum := by decide
  have hdescent : baseEnd_5870856 < baseStart_5870856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870872 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 1, 6]
def baseStart_5870872 : Nat := 118140960795 + 5870872 * 2 ^ 59
def prefixEnd_5870872 : Nat := 4983230072969 + 3 ^ 40 * 5870872 * 2
def baseEnd_5870872 : Nat := 1004859732340953140000119

theorem tailTrace_5870872 : CollatzResearch.WordTrace tailWord_5870872 prefixEnd_5870872 1004859732340953140000119 := by
  unfold tailWord_5870872
  simp only [CollatzResearch.WordTrace]
  refine ⟨107064146593420441978231435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142752195457893922637641913 107064146593420441978231435)
  ·
    refine ⟨160596219890130662967347153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107064146593420441978231435 160596219890130662967347153)
    ·
      refine ⟨120447164917597997225510365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160596219890130662967347153 120447164917597997225510365)
      ·
        refine ⟨45167686844099248959566387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120447164917597997225510365 45167686844099248959566387)
        ·
          refine ⟨67751530266148873439349581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45167686844099248959566387 67751530266148873439349581)
          ·
            refine ⟨25406823849805827539756093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67751530266148873439349581 25406823849805827539756093)
            ·
              refine ⟨9527558943677185327408535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25406823849805827539756093 9527558943677185327408535)
              ·
                refine ⟨14291338415515777991112803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9527558943677185327408535 14291338415515777991112803)
                ·
                  refine ⟨21437007623273666986669205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14291338415515777991112803 21437007623273666986669205)
                  ·
                    refine ⟨1004859732340953140000119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21437007623273666986669205 1004859732340953140000119)
                    ·
                      rfl

theorem cell23_5870872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_5870872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870872 prefixEnd_5870872 := by exact prefixLift 5870872
  have htrace : WordTrace (prefixWord ++ tailWord_5870872) baseStart_5870872 baseEnd_5870872 := by
    simpa [prefixWord, tailWord_5870872, baseEnd_5870872] using wordTrace_append hprefix tailTrace_5870872
  have hstable : (prefixWord ++ tailWord_5870872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870872).length < 2 ^ (prefixWord ++ tailWord_5870872).sum := by decide
  have hdescent : baseEnd_5870872 < baseStart_5870872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870890 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5870890 : Nat := 118140960795 + 5870890 * 2 ^ 59
def prefixEnd_5870890 : Nat := 4983230072969 + 3 ^ 40 * 5870890 * 2
def baseEnd_5870890 : Nat := 3014588439674640349575275

theorem tailTrace_5870890 : CollatzResearch.WordTrace tailWord_5870890 prefixEnd_5870890 3014588439674640349575275 := by
  unfold tailWord_5870890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53532237425193918257654531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142752633133850448687078749 53532237425193918257654531)
  ·
    refine ⟨80298356137790877386481797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53532237425193918257654531 80298356137790877386481797)
    ·
      refine ⟨15055941775835789509965337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80298356137790877386481797 15055941775835789509965337)
      ·
        refine ⟨11291956331876842132474003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15055941775835789509965337 11291956331876842132474003)
        ·
          refine ⟨16937934497815263198711005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11291956331876842132474003 16937934497815263198711005)
          ·
            refine ⟨6351725436680723699516627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16937934497815263198711005 6351725436680723699516627)
            ·
              refine ⟨9527588155021085549274941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351725436680723699516627 9527588155021085549274941)
              ·
                refine ⟨3572845558132907080978103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9527588155021085549274941 3572845558132907080978103)
                ·
                  refine ⟨5359268337199360621467155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572845558132907080978103 5359268337199360621467155)
                  ·
                    refine ⟨8038902505799040932200733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359268337199360621467155 8038902505799040932200733)
                    ·
                      refine ⟨3014588439674640349575275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038902505799040932200733 3014588439674640349575275)
                      ·
                        rfl

theorem cell23_5870890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5870890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870890 prefixEnd_5870890 := by exact prefixLift 5870890
  have htrace : WordTrace (prefixWord ++ tailWord_5870890) baseStart_5870890 baseEnd_5870890 := by
    simpa [prefixWord, tailWord_5870890, baseEnd_5870890] using wordTrace_append hprefix tailTrace_5870890
  have hstable : (prefixWord ++ tailWord_5870890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870890).length < 2 ^ (prefixWord ++ tailWord_5870890).sum := by decide
  have hdescent : baseEnd_5870890 < baseStart_5870890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870899 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 3]
def baseStart_5870899 : Nat := 118140960795 + 5870899 * 2 ^ 59
def prefixEnd_5870899 : Nat := 4983230072969 + 3 ^ 40 * 5870899 * 2
def baseEnd_5870899 : Nat := 3014593061000530814362733

theorem tailTrace_5870899 : CollatzResearch.WordTrace tailWord_5870899 prefixEnd_5870899 3014593061000530814362733 := by
  unfold tailWord_5870899
  simp only [CollatzResearch.WordTrace]
  refine ⟨214129277957743067567695751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142752851971828711711797167 214129277957743067567695751)
  ·
    refine ⟨321193916936614601351543627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214129277957743067567695751 321193916936614601351543627)
    ·
      refine ⟨481790875404921902027315441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321193916936614601351543627 481790875404921902027315441)
      ·
        refine ⟨361343156553691426520486581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481790875404921902027315441 361343156553691426520486581)
        ·
          refine ⟨33875920926908571236295617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 361343156553691426520486581 33875920926908571236295617)
          ·
            refine ⟨25406940695181428427221713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33875920926908571236295617 25406940695181428427221713)
            ·
              refine ⟨19055205521386071320416285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25406940695181428427221713 19055205521386071320416285)
              ·
                refine ⟨7145702070519776745156107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19055205521386071320416285 7145702070519776745156107)
                ·
                  refine ⟨10718553105779665117734161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7145702070519776745156107 10718553105779665117734161)
                  ·
                    refine ⟨8038914829334748838300621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10718553105779665117734161 8038914829334748838300621)
                    ·
                      refine ⟨3014593061000530814362733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8038914829334748838300621 3014593061000530814362733)
                      ·
                        rfl

theorem cell23_5870899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_5870899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870899 prefixEnd_5870899 := by exact prefixLift 5870899
  have htrace : WordTrace (prefixWord ++ tailWord_5870899) baseStart_5870899 baseEnd_5870899 := by
    simpa [prefixWord, tailWord_5870899, baseEnd_5870899] using wordTrace_append hprefix tailTrace_5870899
  have hstable : (prefixWord ++ tailWord_5870899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870899).length < 2 ^ (prefixWord ++ tailWord_5870899).sum := by decide
  have hdescent : baseEnd_5870899 < baseStart_5870899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870913 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5870913 : Nat := 118140960795 + 5870913 * 2 ^ 59
def prefixEnd_5870913 : Nat := 4983230072969 + 3 ^ 40 * 5870913 * 2
def baseEnd_5870913 : Nat := 3014600249729693759587669

theorem tailTrace_5870913 : CollatzResearch.WordTrace tailWord_5870913 prefixEnd_5870913 3014600249729693759587669 := by
  unfold tailWord_5870913
  simp only [CollatzResearch.WordTrace]
  refine ⟨214129788579692347958705393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142753192386461565305803595 214129788579692347958705393)
  ·
    refine ⟨160597341434769260969029045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214129788579692347958705393 160597341434769260969029045)
    ·
      refine ⟨15056000759509618215846473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160597341434769260969029045 15056000759509618215846473)
      ·
        refine ⟨11292000569632213661884855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15056000759509618215846473 11292000569632213661884855)
        ·
          refine ⟨16938000854448320492827283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11292000569632213661884855 16938000854448320492827283)
          ·
            refine ⟨25407001281672480739240925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16938000854448320492827283 25407001281672480739240925)
            ·
              refine ⟨9527625480627180277215347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25407001281672480739240925 9527625480627180277215347)
              ·
                refine ⟨14291438220940770415823021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9527625480627180277215347 14291438220940770415823021)
                ·
                  refine ⟨5359289332852788905933633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14291438220940770415823021 5359289332852788905933633)
                  ·
                    refine ⟨4019466999639591679450225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5359289332852788905933633 4019466999639591679450225)
                    ·
                      refine ⟨3014600249729693759587669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019466999639591679450225 3014600249729693759587669)
                      ·
                        rfl

theorem cell23_5870913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5870913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870913 prefixEnd_5870913 := by exact prefixLift 5870913
  have htrace : WordTrace (prefixWord ++ tailWord_5870913) baseStart_5870913 baseEnd_5870913 := by
    simpa [prefixWord, tailWord_5870913, baseEnd_5870913] using wordTrace_append hprefix tailTrace_5870913
  have hstable : (prefixWord ++ tailWord_5870913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870913).length < 2 ^ (prefixWord ++ tailWord_5870913).sum := by decide
  have hdescent : baseEnd_5870913 < baseStart_5870913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870915 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 2, 7]
def baseStart_5870915 : Nat := 118140960795 + 5870915 * 2 ^ 59
def prefixEnd_5870915 : Nat := 4983230072969 + 3 ^ 40 * 5870915 * 2
def baseEnd_5870915 : Nat := 1004867092230334250587553

theorem tailTrace_5870915 : CollatzResearch.WordTrace tailWord_5870915 prefixEnd_5870915 1004867092230334250587553 := by
  unfold tailWord_5870915
  simp only [CollatzResearch.WordTrace]
  refine ⟨214129861525685102300278199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142753241017123401533518799 214129861525685102300278199)
  ·
    refine ⟨321194792288527653450417299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214129861525685102300278199 321194792288527653450417299)
    ·
      refine ⟨481792188432791480175625949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321194792288527653450417299 481792188432791480175625949)
      ·
        refine ⟨180672070662296805065859731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481792188432791480175625949 180672070662296805065859731)
        ·
          refine ⟨271008105993445207598789597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180672070662296805065859731 271008105993445207598789597)
          ·
            refine ⟨101628039747541952849546099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271008105993445207598789597 101628039747541952849546099)
            ·
              refine ⟨152442059621312929274319149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101628039747541952849546099 152442059621312929274319149)
              ·
                refine ⟨57165772357992348477869681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152442059621312929274319149 57165772357992348477869681)
                ·
                  refine ⟨42874329268494261358402261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57165772357992348477869681 42874329268494261358402261)
                  ·
                    refine ⟨1004867092230334250587553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42874329268494261358402261 1004867092230334250587553)
                    ·
                      rfl

theorem cell23_5870915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_5870915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870915 prefixEnd_5870915 := by exact prefixLift 5870915
  have htrace : WordTrace (prefixWord ++ tailWord_5870915) baseStart_5870915 baseEnd_5870915 := by
    simpa [prefixWord, tailWord_5870915, baseEnd_5870915] using wordTrace_append hprefix tailTrace_5870915
  have hstable : (prefixWord ++ tailWord_5870915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870915).length < 2 ^ (prefixWord ++ tailWord_5870915).sum := by decide
  have hdescent : baseEnd_5870915 < baseStart_5870915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870962 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_5870962 : Nat := 118140960795 + 5870962 * 2 ^ 59
def prefixEnd_5870962 : Nat := 4983230072969 + 3 ^ 40 * 5870962 * 2
def baseEnd_5870962 : Nat := 1004875136760588022624981

theorem tailTrace_5870962 : CollatzResearch.WordTrace tailWord_5870962 prefixEnd_5870962 1004875136760588022624981 := by
  unfold tailWord_5870962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53532893939128707331809785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142754383837676552884826093 53532893939128707331809785)
  ·
    refine ⟨40149670454346530498857339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53532893939128707331809785 40149670454346530498857339)
    ·
      refine ⟨60224505681519795748286009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40149670454346530498857339 60224505681519795748286009)
      ·
        refine ⟨45168379261139846811214507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60224505681519795748286009 45168379261139846811214507)
        ·
          refine ⟨67752568891709770216821761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45168379261139846811214507 67752568891709770216821761)
          ·
            refine ⟨50814426668782327662616321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67752568891709770216821761 50814426668782327662616321)
            ·
              refine ⟨38110820001586745746962241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50814426668782327662616321 38110820001586745746962241)
              ·
                refine ⟨28583115001190059310221681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38110820001586745746962241 28583115001190059310221681)
                ·
                  refine ⟨21437336250892544482666261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28583115001190059310221681 21437336250892544482666261)
                  ·
                    refine ⟨1004875136760588022624981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21437336250892544482666261 1004875136760588022624981)
                    ·
                      rfl

theorem cell23_5870962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_5870962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870962 prefixEnd_5870962 := by exact prefixLift 5870962
  have htrace : WordTrace (prefixWord ++ tailWord_5870962) baseStart_5870962 baseEnd_5870962 := by
    simpa [prefixWord, tailWord_5870962, baseEnd_5870962] using wordTrace_append hprefix tailTrace_5870962
  have hstable : (prefixWord ++ tailWord_5870962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870962).length < 2 ^ (prefixWord ++ tailWord_5870962).sum := by decide
  have hdescent : baseEnd_5870962 < baseStart_5870962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870972 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_5870972 : Nat := 118140960795 + 5870972 * 2 ^ 59
def prefixEnd_5870972 : Nat := 4983230072969 + 3 ^ 40 * 5870972 * 2
def baseEnd_5870972 : Nat := 3014630545088309028749897

theorem tailTrace_5870972 : CollatzResearch.WordTrace tailWord_5870972 prefixEnd_5870972 3014630545088309028749897 := by
  unfold tailWord_5870972
  simp only [CollatzResearch.WordTrace]
  refine ⟨107065970243239300517551585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142754626990985734023402113 107065970243239300517551585)
  ·
    refine ⟨80299477682429475388163689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107065970243239300517551585 80299477682429475388163689)
    ·
      refine ⟨60224608261822106541122767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80299477682429475388163689 60224608261822106541122767)
      ·
        refine ⟨90336912392733159811684151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60224608261822106541122767 90336912392733159811684151)
        ·
          refine ⟨135505368589099739717526227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90336912392733159811684151 135505368589099739717526227)
          ·
            refine ⟨203258052883649609576289341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135505368589099739717526227 203258052883649609576289341)
            ·
              refine ⟨76221769831368603591108503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203258052883649609576289341 76221769831368603591108503)
              ·
                refine ⟨114332654747052905386662755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76221769831368603591108503 114332654747052905386662755)
                ·
                  refine ⟨171498982120579358079994133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114332654747052905386662755 171498982120579358079994133)
                  ·
                    refine ⟨8039014786902157409999725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 171498982120579358079994133 8039014786902157409999725)
                    ·
                      refine ⟨3014630545088309028749897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039014786902157409999725 3014630545088309028749897)
                      ·
                        rfl

theorem cell23_5870972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_5870972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5870972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5870972 prefixEnd_5870972 := by exact prefixLift 5870972
  have htrace : WordTrace (prefixWord ++ tailWord_5870972) baseStart_5870972 baseEnd_5870972 := by
    simpa [prefixWord, tailWord_5870972, baseEnd_5870972] using wordTrace_append hprefix tailTrace_5870972
  have hstable : (prefixWord ++ tailWord_5870972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870972).length < 2 ^ (prefixWord ++ tailWord_5870972).sum := by decide
  have hdescent : baseEnd_5870972 < baseStart_5870972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871032 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_5871032 : Nat := 118140960795 + 5871032 * 2 ^ 59
def prefixEnd_5871032 : Nat := 4983230072969 + 3 ^ 40 * 5871032 * 2
def baseEnd_5871032 : Nat := 3014661353927578793999621

theorem tailTrace_5871032 : CollatzResearch.WordTrace tailWord_5871032 prefixEnd_5871032 3014661353927578793999621 := by
  unfold tailWord_5871032
  simp only [CollatzResearch.WordTrace]
  refine ⟨107067064433130615641143675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142756085910840820854858233 107067064433130615641143675)
  ·
    refine ⟨160600596649695923461715513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107067064433130615641143675 160600596649695923461715513)
    ·
      refine ⟨120450447487271942596286635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160600596649695923461715513 120450447487271942596286635)
      ·
        refine ⟨180675671230907913894429953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120450447487271942596286635 180675671230907913894429953)
        ·
          refine ⟨135506753423180935420822465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180675671230907913894429953 135506753423180935420822465)
          ·
            refine ⟨101630065067385701565616849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135506753423180935420822465 101630065067385701565616849)
            ·
              refine ⟨76222548800539276174212637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101630065067385701565616849 76222548800539276174212637)
              ·
                refine ⟨28583455800202228565329739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76222548800539276174212637 28583455800202228565329739)
                ·
                  refine ⟨42875183700303342847994609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28583455800202228565329739 42875183700303342847994609)
                  ·
                    refine ⟨32156387775227507135995957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42875183700303342847994609 32156387775227507135995957)
                    ·
                      refine ⟨3014661353927578793999621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32156387775227507135995957 3014661353927578793999621)
                      ·
                        rfl

theorem cell23_5871032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_5871032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871032 prefixEnd_5871032 := by exact prefixLift 5871032
  have htrace : WordTrace (prefixWord ++ tailWord_5871032) baseStart_5871032 baseEnd_5871032 := by
    simpa [prefixWord, tailWord_5871032, baseEnd_5871032] using wordTrace_append hprefix tailTrace_5871032
  have hstable : (prefixWord ++ tailWord_5871032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871032).length < 2 ^ (prefixWord ++ tailWord_5871032).sum := by decide
  have hdescent : baseEnd_5871032 < baseStart_5871032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871060 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 5]
def baseStart_5871060 : Nat := 118140960795 + 5871060 * 2 ^ 59
def prefixEnd_5871060 : Nat := 4983230072969 + 3 ^ 40 * 5871060 * 2
def baseEnd_5871060 : Nat := 334963970153989409383277

theorem tailTrace_5871060 : CollatzResearch.WordTrace tailWord_5871060 prefixEnd_5871060 334963970153989409383277 := by
  unfold tailWord_5871060
  simp only [CollatzResearch.WordTrace]
  refine ⟨107067575055079896032153317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142756766740106528042871089 107067575055079896032153317)
  ·
    refine ⟨20075170322827480506028747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107067575055079896032153317 20075170322827480506028747)
    ·
      refine ⟨30112755484241220759043121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20075170322827480506028747 30112755484241220759043121)
      ·
        refine ⟨22584566613180915569282341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30112755484241220759043121 22584566613180915569282341)
        ·
          refine ⟨4234606239971421669240439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22584566613180915569282341 4234606239971421669240439)
          ·
            refine ⟨6351909359957132503860659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234606239971421669240439 6351909359957132503860659)
            ·
              refine ⟨9527864039935698755790989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351909359957132503860659 9527864039935698755790989)
              ·
                refine ⟨3572949014975887033421621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9527864039935698755790989 3572949014975887033421621)
                ·
                  refine ⟨334963970153989409383277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3572949014975887033421621 334963970153989409383277)
                  ·
                    rfl

theorem cell23_5871060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_5871060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871060 prefixEnd_5871060 := by exact prefixLift 5871060
  have htrace : WordTrace (prefixWord ++ tailWord_5871060) baseStart_5871060 baseEnd_5871060 := by
    simpa [prefixWord, tailWord_5871060, baseEnd_5871060] using wordTrace_append hprefix tailTrace_5871060
  have hstable : (prefixWord ++ tailWord_5871060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871060).length < 2 ^ (prefixWord ++ tailWord_5871060).sum := by decide
  have hdescent : baseEnd_5871060 < baseStart_5871060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871072 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_5871072 : Nat := 118140960795 + 5871072 * 2 ^ 59
def prefixEnd_5871072 : Nat := 4983230072969 + 3 ^ 40 * 5871072 * 2
def baseEnd_5871072 : Nat := 3014681893153758637499437

theorem tailTrace_5871072 : CollatzResearch.WordTrace tailWord_5871072 prefixEnd_5871072 3014681893153758637499437 := by
  unfold tailWord_5871072
  simp only [CollatzResearch.WordTrace]
  refine ⟨107067793893058159056871735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142757058524077545409162313 107067793893058159056871735)
  ·
    refine ⟨160601690839587238585307603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107067793893058159056871735 160601690839587238585307603)
    ·
      refine ⟨240902536259380857877961405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160601690839587238585307603 240902536259380857877961405)
      ·
        refine ⟨90338451097267821704235527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240902536259380857877961405 90338451097267821704235527)
        ·
          refine ⟨135507676645901732556353291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90338451097267821704235527 135507676645901732556353291)
          ·
            refine ⟨203261514968852598834529937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135507676645901732556353291 203261514968852598834529937)
            ·
              refine ⟨152446136226639449125897453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203261514968852598834529937 152446136226639449125897453)
              ·
                refine ⟨57167301084989793422211545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152446136226639449125897453 57167301084989793422211545)
                ·
                  refine ⟨42875475813742345066658659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57167301084989793422211545 42875475813742345066658659)
                  ·
                    refine ⟨64313213720613517599987989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42875475813742345066658659 64313213720613517599987989)
                    ·
                      refine ⟨3014681893153758637499437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64313213720613517599987989 3014681893153758637499437)
                      ·
                        rfl

theorem cell23_5871072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_5871072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871072 prefixEnd_5871072 := by exact prefixLift 5871072
  have htrace : WordTrace (prefixWord ++ tailWord_5871072) baseStart_5871072 baseEnd_5871072 := by
    simpa [prefixWord, tailWord_5871072, baseEnd_5871072] using wordTrace_append hprefix tailTrace_5871072
  have hstable : (prefixWord ++ tailWord_5871072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871072).length < 2 ^ (prefixWord ++ tailWord_5871072).sum := by decide
  have hdescent : baseEnd_5871072 < baseStart_5871072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871159 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 1, 6]
def baseStart_5871159 : Nat := 118140960795 + 5871159 * 2 ^ 59
def prefixEnd_5871159 : Nat := 4983230072969 + 3 ^ 40 * 5871159 * 2
def baseEnd_5871159 : Nat := 1004908855323566599037179

theorem tailTrace_5871159 : CollatzResearch.WordTrace tailWord_5871159 prefixEnd_5871159 1004908855323566599037179 := by
  unfold tailWord_5871159
  simp only [CollatzResearch.WordTrace]
  refine ⟨214138760936801131972160531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142759173957867421314773687 214138760936801131972160531)
  ·
    refine ⟨321208141405201697958240797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214138760936801131972160531 321208141405201697958240797)
    ·
      refine ⟨120453053026950636734340299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321208141405201697958240797 120453053026950636734340299)
      ·
        refine ⟨180679579540425955101510449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120453053026950636734340299 180679579540425955101510449)
        ·
          refine ⟨135509684655319466326132837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180679579540425955101510449 135509684655319466326132837)
          ·
            refine ⟨25408065872872399936149907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135509684655319466326132837 25408065872872399936149907)
            ·
              refine ⟨38112098809308599904224861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25408065872872399936149907 38112098809308599904224861)
              ·
                refine ⟨14292037053490724964084323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38112098809308599904224861 14292037053490724964084323)
                ·
                  refine ⟨21438055580236087446126485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14292037053490724964084323 21438055580236087446126485)
                  ·
                    refine ⟨1004908855323566599037179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21438055580236087446126485 1004908855323566599037179)
                    ·
                      rfl

theorem cell23_5871159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_5871159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871159 prefixEnd_5871159 := by exact prefixLift 5871159
  have htrace : WordTrace (prefixWord ++ tailWord_5871159) baseStart_5871159 baseEnd_5871159 := by
    simpa [prefixWord, tailWord_5871159, baseEnd_5871159] using wordTrace_append hprefix tailTrace_5871159
  have hstable : (prefixWord ++ tailWord_5871159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871159).length < 2 ^ (prefixWord ++ tailWord_5871159).sum := by decide
  have hdescent : baseEnd_5871159 < baseStart_5871159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871199 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_5871199 : Nat := 118140960795 + 5871199 * 2 ^ 59
def prefixEnd_5871199 : Nat := 4983230072969 + 3 ^ 40 * 5871199 * 2
def baseEnd_5871199 : Nat := 3014747105196879640611353

theorem tailTrace_5871199 : CollatzResearch.WordTrace tailWord_5871199 prefixEnd_5871199 3014747105196879640611353 := by
  unfold tailWord_5871199
  simp only [CollatzResearch.WordTrace]
  refine ⟨214140219856656218803616651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142760146571104145869077767 214140219856656218803616651)
  ·
    refine ⟨321210329784984328205424977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214140219856656218803616651 321210329784984328205424977)
    ·
      refine ⟨240907747338738246154068733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321210329784984328205424977 240907747338738246154068733)
      ·
        refine ⟨90340405252026842307775775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240907747338738246154068733 90340405252026842307775775)
        ·
          refine ⟨135510607878040263461663663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90340405252026842307775775 135510607878040263461663663)
          ·
            refine ⟨203265911817060395192495495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135510607878040263461663663 203265911817060395192495495)
            ·
              refine ⟨304898867725590592788743243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203265911817060395192495495 304898867725590592788743243)
              ·
                refine ⟨457348301588385889183114865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304898867725590592788743243 457348301588385889183114865)
                ·
                  refine ⟨343011226191289416887336149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457348301588385889183114865 343011226191289416887336149)
                  ·
                    refine ⟨8039325613858345708296941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 343011226191289416887336149 8039325613858345708296941)
                    ·
                      refine ⟨3014747105196879640611353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039325613858345708296941 3014747105196879640611353)
                      ·
                        rfl

theorem cell23_5871199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_5871199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871199 prefixEnd_5871199 := by exact prefixLift 5871199
  have htrace : WordTrace (prefixWord ++ tailWord_5871199) baseStart_5871199 baseEnd_5871199 := by
    simpa [prefixWord, tailWord_5871199, baseEnd_5871199] using wordTrace_append hprefix tailTrace_5871199
  have hstable : (prefixWord ++ tailWord_5871199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871199).length < 2 ^ (prefixWord ++ tailWord_5871199).sum := by decide
  have hdescent : baseEnd_5871199 < baseStart_5871199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871210 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_5871210 : Nat := 118140960795 + 5871210 * 2 ^ 59
def prefixEnd_5871210 : Nat := 4983230072969 + 3 ^ 40 * 5871210 * 2
def baseEnd_5871210 : Nat := 1004917584494693032524601

theorem tailTrace_5871210 : CollatzResearch.WordTrace tailWord_5871210 prefixEnd_5871210 1004917584494693032524601 := by
  unfold tailWord_5871210
  simp only [CollatzResearch.WordTrace]
  refine ⟨53535155264904091920566771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142760414039744245121511389 53535155264904091920566771)
  ·
    refine ⟨80302732897356137880850157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53535155264904091920566771 80302732897356137880850157)
    ·
      refine ⟨30113524836508551705318809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80302732897356137880850157 30113524836508551705318809)
      ·
        refine ⟨22585143627381413778989107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30113524836508551705318809 22585143627381413778989107)
        ·
          refine ⟨33877715441072120668483661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22585143627381413778989107 33877715441072120668483661)
          ·
            refine ⟨12704143290402045250681373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33877715441072120668483661 12704143290402045250681373)
            ·
              refine ⟨4764053733900766969005515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12704143290402045250681373 4764053733900766969005515)
              ·
                refine ⟨7146080600851150453508273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764053733900766969005515 7146080600851150453508273)
                ·
                  refine ⟨5359560450638362840131205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7146080600851150453508273 5359560450638362840131205)
                  ·
                    refine ⟨1004917584494693032524601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5359560450638362840131205 1004917584494693032524601)
                    ·
                      rfl

theorem cell23_5871210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_5871210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871210 prefixEnd_5871210 := by exact prefixLift 5871210
  have htrace : WordTrace (prefixWord ++ tailWord_5871210) baseStart_5871210 baseEnd_5871210 := by
    simpa [prefixWord, tailWord_5871210, baseEnd_5871210] using wordTrace_append hprefix tailTrace_5871210
  have hstable : (prefixWord ++ tailWord_5871210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871210).length < 2 ^ (prefixWord ++ tailWord_5871210).sum := by decide
  have hdescent : baseEnd_5871210 < baseStart_5871210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871233 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5871233 : Nat := 118140960795 + 5871233 * 2 ^ 59
def prefixEnd_5871233 : Nat := 4983230072969 + 3 ^ 40 * 5871233 * 2
def baseEnd_5871233 : Nat := 3014764563539132507586197

theorem tailTrace_5871233 : CollatzResearch.WordTrace tailWord_5871233 prefixEnd_5871233 3014764563539132507586197 := by
  unfold tailWord_5871233
  simp only [CollatzResearch.WordTrace]
  refine ⟨214141459938533042610354353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142760973292355361740236235 214141459938533042610354353)
  ·
    refine ⟨160606094953899781957765765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214141459938533042610354353 160606094953899781957765765)
    ·
      refine ⟨30113642803856209117081081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160606094953899781957765765 30113642803856209117081081)
      ·
        refine ⟨22585232102892156837810811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30113642803856209117081081 22585232102892156837810811)
        ·
          refine ⟨33877848154338235256716217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22585232102892156837810811 33877848154338235256716217)
          ·
            refine ⟨25408386115753676442537163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33877848154338235256716217 25408386115753676442537163)
            ·
              refine ⟨38112579173630514663805745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25408386115753676442537163 38112579173630514663805745)
              ·
                refine ⟨28584434380222885997854309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38112579173630514663805745 28584434380222885997854309)
                ·
                  refine ⟨5359581446291791124597683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28584434380222885997854309 5359581446291791124597683)
                  ·
                    refine ⟨8039372169437686686896525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359581446291791124597683 8039372169437686686896525)
                    ·
                      refine ⟨3014764563539132507586197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039372169437686686896525 3014764563539132507586197)
                      ·
                        rfl

theorem cell23_5871233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5871233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871233 prefixEnd_5871233 := by exact prefixLift 5871233
  have htrace : WordTrace (prefixWord ++ tailWord_5871233) baseStart_5871233 baseEnd_5871233 := by
    simpa [prefixWord, tailWord_5871233, baseEnd_5871233] using wordTrace_append hprefix tailTrace_5871233
  have hstable : (prefixWord ++ tailWord_5871233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871233).length < 2 ^ (prefixWord ++ tailWord_5871233).sum := by decide
  have hdescent : baseEnd_5871233 < baseStart_5871233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871243 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 1, 3, 2]
def baseStart_5871243 : Nat := 118140960795 + 5871243 * 2 ^ 59
def prefixEnd_5871243 : Nat := 4983230072969 + 3 ^ 40 * 5871243 * 2
def baseEnd_5871243 : Nat := 3014769698345677468461151

theorem tailTrace_5871243 : CollatzResearch.WordTrace tailWord_5871243 prefixEnd_5871243 3014769698345677468461151 := by
  unfold tailWord_5871243
  simp only [CollatzResearch.WordTrace]
  refine ⟨214141824668496814318218383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142761216445664542878812255 214141824668496814318218383)
  ·
    refine ⟨321212737002745221477327575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214141824668496814318218383 321212737002745221477327575)
    ·
      refine ⟨481819105504117832215991363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321212737002745221477327575 481819105504117832215991363)
      ·
        refine ⟨722728658256176748323987045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481819105504117832215991363 722728658256176748323987045)
        ·
          refine ⟨135511623423033140310747571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 722728658256176748323987045 135511623423033140310747571)
          ·
            refine ⟨203267435134549710466121357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135511623423033140310747571 203267435134549710466121357)
            ·
              refine ⟨76225288175456141424795509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203267435134549710466121357 76225288175456141424795509)
              ·
                refine ⟨7146120766449013258574579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76225288175456141424795509 7146120766449013258574579)
                ·
                  refine ⟨10719181149673519887861869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7146120766449013258574579 10719181149673519887861869)
                  ·
                    refine ⟨4019692931127569957948201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10719181149673519887861869 4019692931127569957948201)
                    ·
                      refine ⟨3014769698345677468461151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019692931127569957948201 3014769698345677468461151)
                      ·
                        rfl

theorem cell23_5871243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 3, 2].length) (baseStart_5871243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871243 prefixEnd_5871243 := by exact prefixLift 5871243
  have htrace : WordTrace (prefixWord ++ tailWord_5871243) baseStart_5871243 baseEnd_5871243 := by
    simpa [prefixWord, tailWord_5871243, baseEnd_5871243] using wordTrace_append hprefix tailTrace_5871243
  have hstable : (prefixWord ++ tailWord_5871243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871243).length < 2 ^ (prefixWord ++ tailWord_5871243).sum := by decide
  have hdescent : baseEnd_5871243 < baseStart_5871243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871249 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_5871249 : Nat := 118140960795 + 5871249 * 2 ^ 59
def prefixEnd_5871249 : Nat := 4983230072969 + 3 ^ 40 * 5871249 * 2
def baseEnd_5871249 : Nat := 1004924259743201481662041

theorem tailTrace_5871249 : CollatzResearch.WordTrace tailWord_5871249 prefixEnd_5871249 1004924259743201481662041 := by
  unfold tailWord_5871249
  simp only [CollatzResearch.WordTrace]
  refine ⟨214142043506475077342936801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142761362337650051561957867 214142043506475077342936801)
  ·
    refine ⟨160606532629856308007202601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214142043506475077342936801 160606532629856308007202601)
    ·
      refine ⟨120454899472392231005401951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160606532629856308007202601 120454899472392231005401951)
      ·
        refine ⟨180682349208588346508102927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120454899472392231005401951 180682349208588346508102927)
        ·
          refine ⟨271023523812882519762154391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180682349208588346508102927 271023523812882519762154391)
          ·
            refine ⟨406535285719323779643231587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271023523812882519762154391 406535285719323779643231587)
            ·
              refine ⟨609802928578985669464847381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406535285719323779643231587 609802928578985669464847381)
              ·
                refine ⟨28584512277139953256164721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 609802928578985669464847381 28584512277139953256164721)
                ·
                  refine ⟨21438384207854964942123541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28584512277139953256164721 21438384207854964942123541)
                  ·
                    refine ⟨1004924259743201481662041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21438384207854964942123541 1004924259743201481662041)
                    ·
                      rfl

theorem cell23_5871249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_5871249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871249 prefixEnd_5871249 := by exact prefixLift 5871249
  have htrace : WordTrace (prefixWord ++ tailWord_5871249) baseStart_5871249 baseEnd_5871249 := by
    simpa [prefixWord, tailWord_5871249, baseEnd_5871249] using wordTrace_append hprefix tailTrace_5871249
  have hstable : (prefixWord ++ tailWord_5871249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871249).length < 2 ^ (prefixWord ++ tailWord_5871249).sum := by decide
  have hdescent : baseEnd_5871249 < baseStart_5871249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871279 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 9]
def baseStart_5871279 : Nat := 118140960795 + 5871279 * 2 ^ 59
def prefixEnd_5871279 : Nat := 4983230072969 + 3 ^ 40 * 5871279 * 2
def baseEnd_5871279 : Nat := 334976464849915480845665

theorem tailTrace_5871279 : CollatzResearch.WordTrace tailWord_5871279 prefixEnd_5871279 334976464849915480845665 := by
  unfold tailWord_5871279
  simp only [CollatzResearch.WordTrace]
  refine ⟨214143137696366392466528891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142762091797577594977685927 214143137696366392466528891)
  ·
    refine ⟨321214706544549588699793337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214143137696366392466528891 321214706544549588699793337)
    ·
      refine ⟨240911029908412191524845003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321214706544549588699793337 240911029908412191524845003)
      ·
        refine ⟨361366544862618287287267505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240911029908412191524845003 361366544862618287287267505)
        ·
          refine ⟨271024908646963715465450629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361366544862618287287267505 271024908646963715465450629)
          ·
            refine ⟨50817170371305696649771993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271024908646963715465450629 50817170371305696649771993)
            ·
              refine ⟨38112877778479272487328995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50817170371305696649771993 38112877778479272487328995)
              ·
                refine ⟨57169316667718908730993493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38112877778479272487328995 57169316667718908730993493)
                ·
                  refine ⟨334976464849915480845665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57169316667718908730993493 334976464849915480845665)
                  ·
                    rfl

theorem cell23_5871279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 9].length) (baseStart_5871279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871279 prefixEnd_5871279 := by exact prefixLift 5871279
  have htrace : WordTrace (prefixWord ++ tailWord_5871279) baseStart_5871279 baseEnd_5871279 := by
    simpa [prefixWord, tailWord_5871279, baseEnd_5871279] using wordTrace_append hprefix tailTrace_5871279
  have hstable : (prefixWord ++ tailWord_5871279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871279).length < 2 ^ (prefixWord ++ tailWord_5871279).sum := by decide
  have hdescent : baseEnd_5871279 < baseStart_5871279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871313 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 5]
def baseStart_5871313 : Nat := 118140960795 + 5871313 * 2 ^ 59
def prefixEnd_5871313 : Nat := 4983230072969 + 3 ^ 40 * 5871313 * 2
def baseEnd_5871313 : Nat := 334978404665721354953981

theorem tailTrace_5871313 : CollatzResearch.WordTrace tailWord_5871313 prefixEnd_5871313 334978404665721354953981 := by
  unfold tailWord_5871313
  simp only [CollatzResearch.WordTrace]
  refine ⟨214144377778243216273266593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142762918518828810848844395 214144377778243216273266593)
  ·
    refine ⟨160608283333682412204949945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214144377778243216273266593 160608283333682412204949945)
    ·
      refine ⟨120456212500261809153712459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160608283333682412204949945 120456212500261809153712459)
      ·
        refine ⟨180684318750392713730568689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120456212500261809153712459 180684318750392713730568689)
        ·
          refine ⟨135513239062794535297926517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180684318750392713730568689 135513239062794535297926517)
          ·
            refine ⟨12704366162136987684180611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135513239062794535297926517 12704366162136987684180611)
            ·
              refine ⟨19056549243205481526270917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12704366162136987684180611 19056549243205481526270917)
              ·
                refine ⟨3573102983101027786175797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19056549243205481526270917 3573102983101027786175797)
                ·
                  refine ⟨334978404665721354953981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3573102983101027786175797 334978404665721354953981)
                  ·
                    rfl

theorem cell23_5871313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 5].length) (baseStart_5871313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871313 prefixEnd_5871313 := by exact prefixLift 5871313
  have htrace : WordTrace (prefixWord ++ tailWord_5871313) baseStart_5871313 baseEnd_5871313 := by
    simpa [prefixWord, tailWord_5871313, baseEnd_5871313] using wordTrace_append hprefix tailTrace_5871313
  have hstable : (prefixWord ++ tailWord_5871313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871313).length < 2 ^ (prefixWord ++ tailWord_5871313).sum := by decide
  have hdescent : baseEnd_5871313 < baseStart_5871313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871333 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5871333 : Nat := 118140960795 + 5871333 * 2 ^ 59
def prefixEnd_5871333 : Nat := 4983230072969 + 3 ^ 40 * 5871333 * 2
def baseEnd_5871333 : Nat := 3014815911604582116335737

theorem tailTrace_5871333 : CollatzResearch.WordTrace tailWord_5871333 prefixEnd_5871333 3014815911604582116335737 := by
  unfold tailWord_5871333
  simp only [CollatzResearch.WordTrace]
  refine ⟨214145107238170759688994653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142763404825447173125996435 214145107238170759688994653)
  ·
    refine ⟨80304415214314034883372995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214145107238170759688994653 80304415214314034883372995)
    ·
      refine ⟨120456622821471052325059493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80304415214314034883372995 120456622821471052325059493)
      ·
        refine ⟨22585616779025822310948655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120456622821471052325059493 22585616779025822310948655)
        ·
          refine ⟨33878425168538733466422983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22585616779025822310948655 33878425168538733466422983)
          ·
            refine ⟨50817637752808100199634475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33878425168538733466422983 50817637752808100199634475)
            ·
              refine ⟨76226456629212150299451713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50817637752808100199634475 76226456629212150299451713)
              ·
                refine ⟨57169842471909112724588785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76226456629212150299451713 57169842471909112724588785)
                ·
                  refine ⟨42877381853931834543441589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57169842471909112724588785 42877381853931834543441589)
                  ·
                    refine ⟨4019754548806109488447649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42877381853931834543441589 4019754548806109488447649)
                    ·
                      refine ⟨3014815911604582116335737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019754548806109488447649 3014815911604582116335737)
                      ·
                        rfl

theorem cell23_5871333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5871333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871333 prefixEnd_5871333 := by exact prefixLift 5871333
  have htrace : WordTrace (prefixWord ++ tailWord_5871333) baseStart_5871333 baseEnd_5871333 := by
    simpa [prefixWord, tailWord_5871333, baseEnd_5871333] using wordTrace_append hprefix tailTrace_5871333
  have hstable : (prefixWord ++ tailWord_5871333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871333).length < 2 ^ (prefixWord ++ tailWord_5871333).sum := by decide
  have hdescent : baseEnd_5871333 < baseStart_5871333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871363 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 2, 4, 2]
def baseStart_5871363 : Nat := 118140960795 + 5871363 * 2 ^ 59
def prefixEnd_5871363 : Nat := 4983230072969 + 3 ^ 40 * 5871363 * 2
def baseEnd_5871363 : Nat := 3014831316024216998960599

theorem tailTrace_5871363 : CollatzResearch.WordTrace tailWord_5871363 prefixEnd_5871363 3014831316024216998960599 := by
  unfold tailWord_5871363
  simp only [CollatzResearch.WordTrace]
  refine ⟨214146201428062074812586743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142764134285374716541724495 214146201428062074812586743)
  ·
    refine ⟨321219302142093112218880115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214146201428062074812586743 321219302142093112218880115)
    ·
      refine ⟨481828953213139668328320173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321219302142093112218880115 481828953213139668328320173)
      ·
        refine ⟨180685857454927375623120065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481828953213139668328320173 180685857454927375623120065)
        ·
          refine ⟨135514393091195531717340049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180685857454927375623120065 135514393091195531717340049)
          ·
            refine ⟨101635794818396648788005037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135514393091195531717340049 101635794818396648788005037)
            ·
              refine ⟨38113423056898743295501889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101635794818396648788005037 38113423056898743295501889)
              ·
                refine ⟨28585067292674057471626417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38113423056898743295501889 28585067292674057471626417)
                ·
                  refine ⟨21438800469505543103719813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28585067292674057471626417 21438800469505543103719813)
                  ·
                    refine ⟨4019775088032289331947465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21438800469505543103719813 4019775088032289331947465)
                    ·
                      refine ⟨3014831316024216998960599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019775088032289331947465 3014831316024216998960599)
                      ·
                        rfl

theorem cell23_5871363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_5871363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871363 prefixEnd_5871363 := by exact prefixLift 5871363
  have htrace : WordTrace (prefixWord ++ tailWord_5871363) baseStart_5871363 baseEnd_5871363 := by
    simpa [prefixWord, tailWord_5871363, baseEnd_5871363] using wordTrace_append hprefix tailTrace_5871363
  have hstable : (prefixWord ++ tailWord_5871363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871363).length < 2 ^ (prefixWord ++ tailWord_5871363).sum := by decide
  have hdescent : baseEnd_5871363 < baseStart_5871363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871383 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5871383 : Nat := 118140960795 + 5871383 * 2 ^ 59
def prefixEnd_5871383 : Nat := 4983230072969 + 3 ^ 40 * 5871383 * 2
def baseEnd_5871383 : Nat := 3014841585637306920710507

theorem tailTrace_5871383 : CollatzResearch.WordTrace tailWord_5871383 prefixEnd_5871383 3014841585637306920710507 := by
  unfold tailWord_5871383
  simp only [CollatzResearch.WordTrace]
  refine ⟨214146930887989618228314803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142764620591993078818876535 214146930887989618228314803)
  ·
    refine ⟨321220396331984427342472205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214146930887989618228314803 321220396331984427342472205)
    ·
      refine ⟨120457648624494160253427077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321220396331984427342472205 120457648624494160253427077)
      ·
        refine ⟨22585809117092655047517577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120457648624494160253427077 22585809117092655047517577)
        ·
          refine ⟨16939356837819491285638183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22585809117092655047517577 16939356837819491285638183)
          ·
            refine ⟨25409035256729236928457275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16939356837819491285638183 25409035256729236928457275)
            ·
              refine ⟨38113552885093855392685913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25409035256729236928457275 38113552885093855392685913)
              ·
                refine ⟨28585164663820391544514435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38113552885093855392685913 28585164663820391544514435)
                ·
                  refine ⟨42877746995730587316771653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28585164663820391544514435 42877746995730587316771653)
                  ·
                    refine ⟨8039577561699485121894685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42877746995730587316771653 8039577561699485121894685)
                    ·
                      refine ⟨3014841585637306920710507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039577561699485121894685 3014841585637306920710507)
                      ·
                        rfl

theorem cell23_5871383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5871383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871383 prefixEnd_5871383 := by exact prefixLift 5871383
  have htrace : WordTrace (prefixWord ++ tailWord_5871383) baseStart_5871383 baseEnd_5871383 := by
    simpa [prefixWord, tailWord_5871383, baseEnd_5871383] using wordTrace_append hprefix tailTrace_5871383
  have hstable : (prefixWord ++ tailWord_5871383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871383).length < 2 ^ (prefixWord ++ tailWord_5871383).sum := by decide
  have hdescent : baseEnd_5871383 < baseStart_5871383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871417 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5871417 : Nat := 118140960795 + 5871417 * 2 ^ 59
def prefixEnd_5871417 : Nat := 4983230072969 + 3 ^ 40 * 5871417 * 2
def baseEnd_5871417 : Nat := 3014859043979559787685351

theorem tailTrace_5871417 : CollatzResearch.WordTrace tailWord_5871417 prefixEnd_5871417 3014859043979559787685351 := by
  unfold tailWord_5871417
  simp only [CollatzResearch.WordTrace]
  refine ⟨214148170969866442035052505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142765447313244294690035003 214148170969866442035052505)
  ·
    refine ⟨160611128227399831526289379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214148170969866442035052505 160611128227399831526289379)
    ·
      refine ⟨240916692341099747289434069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160611128227399831526289379 240916692341099747289434069)
      ·
        refine ⟨5646484976744525327096111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 240916692341099747289434069 5646484976744525327096111)
        ·
          refine ⟨8469727465116787990644167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646484976744525327096111 8469727465116787990644167)
          ·
            refine ⟨12704591197675181985966251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8469727465116787990644167 12704591197675181985966251)
            ·
              refine ⟨19056886796512772978949377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12704591197675181985966251 19056886796512772978949377)
              ·
                refine ⟨14292665097384579734212033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19056886796512772978949377 14292665097384579734212033)
                ·
                  refine ⟨10719498823038434800659025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14292665097384579734212033 10719498823038434800659025)
                  ·
                    refine ⟨8039624117278826100494269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10719498823038434800659025 8039624117278826100494269)
                    ·
                      refine ⟨3014859043979559787685351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039624117278826100494269 3014859043979559787685351)
                      ·
                        rfl

theorem cell23_5871417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5871417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871417 prefixEnd_5871417 := by exact prefixLift 5871417
  have htrace : WordTrace (prefixWord ++ tailWord_5871417) baseStart_5871417 baseEnd_5871417 := by
    simpa [prefixWord, tailWord_5871417, baseEnd_5871417] using wordTrace_append hprefix tailTrace_5871417
  have hstable : (prefixWord ++ tailWord_5871417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871417).length < 2 ^ (prefixWord ++ tailWord_5871417).sum := by decide
  have hdescent : baseEnd_5871417 < baseStart_5871417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871437 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 6]
def baseStart_5871437 : Nat := 118140960795 + 5871437 * 2 ^ 59
def prefixEnd_5871437 : Nat := 4983230072969 + 3 ^ 40 * 5871437 * 2
def baseEnd_5871437 : Nat := 334985479288072189937251

theorem tailTrace_5871437 : CollatzResearch.WordTrace tailWord_5871437 prefixEnd_5871437 334985479288072189937251 := by
  unfold tailWord_5871437
  simp only [CollatzResearch.WordTrace]
  refine ⟨214148900429793985450780565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142765933619862656967187043 214148900429793985450780565)
  ·
    refine ⟨10038229707646593068005339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214148900429793985450780565 10038229707646593068005339)
    ·
      refine ⟨15057344561469889602008009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10038229707646593068005339 15057344561469889602008009)
      ·
        refine ⟨11293008421102417201506007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15057344561469889602008009 11293008421102417201506007)
        ·
          refine ⟨16939512631653625802259011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293008421102417201506007 16939512631653625802259011)
          ·
            refine ⟨25409268947480438703388517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16939512631653625802259011 25409268947480438703388517)
            ·
              refine ⟨4764237927652582256885347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25409268947480438703388517 4764237927652582256885347)
              ·
                refine ⟨7146356891478873385328021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764237927652582256885347 7146356891478873385328021)
                ·
                  refine ⟨334985479288072189937251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7146356891478873385328021 334985479288072189937251)
                  ·
                    rfl

theorem cell23_5871437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_5871437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871437 prefixEnd_5871437 := by exact prefixLift 5871437
  have htrace : WordTrace (prefixWord ++ tailWord_5871437) baseStart_5871437 baseEnd_5871437 := by
    simpa [prefixWord, tailWord_5871437, baseEnd_5871437] using wordTrace_append hprefix tailTrace_5871437
  have hstable : (prefixWord ++ tailWord_5871437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871437).length < 2 ^ (prefixWord ++ tailWord_5871437).sum := by decide
  have hdescent : baseEnd_5871437 < baseStart_5871437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871463 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 1, 6]
def baseStart_5871463 : Nat := 118140960795 + 5871463 * 2 ^ 59
def prefixEnd_5871463 : Nat := 4983230072969 + 3 ^ 40 * 5871463 * 2
def baseEnd_5871463 : Nat := 1004960888029888869236713

theorem tailTrace_5871463 : CollatzResearch.WordTrace tailWord_5871463 prefixEnd_5871463 1004960888029888869236713 := by
  unfold tailWord_5871463
  simp only [CollatzResearch.WordTrace]
  refine ⟨214149848727699791891227043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142766565818466527927484695 214149848727699791891227043)
  ·
    refine ⟨321224773091549687836840565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214149848727699791891227043 321224773091549687836840565)
    ·
      refine ⟨30114822477332783234703803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321224773091549687836840565 30114822477332783234703803)
      ·
        refine ⟨45172233715999174852055705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30114822477332783234703803 45172233715999174852055705)
        ·
          refine ⟨33879175286999381139041779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45172233715999174852055705 33879175286999381139041779)
          ·
            refine ⟨50818762930499071708562669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33879175286999381139041779 50818762930499071708562669)
            ·
              refine ⟨19057036098937151890711001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50818762930499071708562669 19057036098937151890711001)
              ·
                refine ⟨14292777074202863918033251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19057036098937151890711001 14292777074202863918033251)
                ·
                  refine ⟨21439165611304295877049877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14292777074202863918033251 21439165611304295877049877)
                  ·
                    refine ⟨1004960888029888869236713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21439165611304295877049877 1004960888029888869236713)
                    ·
                      rfl

theorem cell23_5871463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_5871463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871463 prefixEnd_5871463 := by exact prefixLift 5871463
  have htrace : WordTrace (prefixWord ++ tailWord_5871463) baseStart_5871463 baseEnd_5871463 := by
    simpa [prefixWord, tailWord_5871463, baseEnd_5871463] using wordTrace_append hprefix tailTrace_5871463
  have hstable : (prefixWord ++ tailWord_5871463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871463).length < 2 ^ (prefixWord ++ tailWord_5871463).sum := by decide
  have hdescent : baseEnd_5871463 < baseStart_5871463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871518 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_5871518 : Nat := 118140960795 + 5871518 * 2 ^ 59
def prefixEnd_5871518 : Nat := 4983230072969 + 3 ^ 40 * 5871518 * 2
def baseEnd_5871518 : Nat := 1004970301841887964174129

theorem tailTrace_5871518 : CollatzResearch.WordTrace tailWord_5871518 prefixEnd_5871518 1004970301841887964174129 := by
  unfold tailWord_5871518
  simp only [CollatzResearch.WordTrace]
  refine ⟨26768981842812567035559901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142767903161667024189652805 26768981842812567035559901)
  ·
    refine ⟨10038368191054712638334963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26768981842812567035559901 10038368191054712638334963)
    ·
      refine ⟨15057552286582068957502445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10038368191054712638334963 15057552286582068957502445)
      ·
        refine ⟨5646582107468275859063417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15057552286582068957502445 5646582107468275859063417)
        ·
          refine ⟨4234936580601206894297563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5646582107468275859063417 4234936580601206894297563)
          ·
            refine ⟨6352404870901810341446345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234936580601206894297563 6352404870901810341446345)
            ·
              refine ⟨4764303653176357756084759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6352404870901810341446345 4764303653176357756084759)
              ·
                refine ⟨7146455479764536634127139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764303653176357756084759 7146455479764536634127139)
                ·
                  refine ⟨10719683219646804951190709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7146455479764536634127139 10719683219646804951190709)
                  ·
                    refine ⟨1004970301841887964174129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10719683219646804951190709 1004970301841887964174129)
                    ·
                      rfl

theorem cell23_5871518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_5871518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871518 prefixEnd_5871518 := by exact prefixLift 5871518
  have htrace : WordTrace (prefixWord ++ tailWord_5871518) baseStart_5871518 baseEnd_5871518 := by
    simpa [prefixWord, tailWord_5871518, baseEnd_5871518] using wordTrace_append hprefix tailTrace_5871518
  have hstable : (prefixWord ++ tailWord_5871518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871518).length < 2 ^ (prefixWord ++ tailWord_5871518).sum := by decide
  have hdescent : baseEnd_5871518 < baseStart_5871518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871520 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 4, 1, 3]
def baseStart_5871520 : Nat := 118140960795 + 5871520 * 2 ^ 59
def prefixEnd_5871520 : Nat := 4983230072969 + 3 ^ 40 * 5871520 * 2
def baseEnd_5871520 : Nat := 3014911932486972884697377

theorem tailTrace_5871520 : CollatzResearch.WordTrace tailWord_5871520 prefixEnd_5871520 3014911932486972884697377 := by
  unfold tailWord_5871520
  simp only [CollatzResearch.WordTrace]
  refine ⟨107075963844246645313026007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142767951792328860417368009 107075963844246645313026007)
  ·
    refine ⟨160613945766369967969539011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107075963844246645313026007 160613945766369967969539011)
    ·
      refine ⟨240920918649554951954308517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160613945766369967969539011 240920918649554951954308517)
      ·
        refine ⟨45172672246791553491432847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240920918649554951954308517 45172672246791553491432847)
        ·
          refine ⟨67759008370187330237149271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45172672246791553491432847 67759008370187330237149271)
          ·
            refine ⟨101638512555280995355723907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67759008370187330237149271 101638512555280995355723907)
            ·
              refine ⟨152457768832921493033585861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101638512555280995355723907 152457768832921493033585861)
              ·
                refine ⟨28585831656172779943797349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152457768832921493033585861 28585831656172779943797349)
                ·
                  refine ⟨5359843435532396239462003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28585831656172779943797349 5359843435532396239462003)
                  ·
                    refine ⟨8039765153298594359193005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359843435532396239462003 8039765153298594359193005)
                    ·
                      refine ⟨3014911932486972884697377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039765153298594359193005 3014911932486972884697377)
                      ·
                        rfl

theorem cell23_5871520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_5871520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871520 prefixEnd_5871520 := by exact prefixLift 5871520
  have htrace : WordTrace (prefixWord ++ tailWord_5871520) baseStart_5871520 baseEnd_5871520 := by
    simpa [prefixWord, tailWord_5871520, baseEnd_5871520] using wordTrace_append hprefix tailTrace_5871520
  have hstable : (prefixWord ++ tailWord_5871520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871520).length < 2 ^ (prefixWord ++ tailWord_5871520).sum := by decide
  have hdescent : baseEnd_5871520 < baseStart_5871520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871521 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5871521 : Nat := 118140960795 + 5871521 * 2 ^ 59
def prefixEnd_5871521 : Nat := 4983230072969 + 3 ^ 40 * 5871521 * 2
def baseEnd_5871521 : Nat := 3014912445967627380784873

theorem tailTrace_5871521 : CollatzResearch.WordTrace tailWord_5871521 prefixEnd_5871521 3014912445967627380784873 := by
  unfold tailWord_5871521
  simp only [CollatzResearch.WordTrace]
  refine ⟨214151964161489667796838417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142767976107659778531225611 214151964161489667796838417)
  ·
    refine ⟨160613973121117250847628813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214151964161489667796838417 160613973121117250847628813)
    ·
      refine ⟨60230239920418969067860805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160613973121117250847628813 60230239920418969067860805)
      ·
        refine ⟨11293169985078556700223901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60230239920418969067860805 11293169985078556700223901)
        ·
          refine ⟨4234938744404458762583963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11293169985078556700223901 4234938744404458762583963)
          ·
            refine ⟨6352408116606688143875945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234938744404458762583963 6352408116606688143875945)
            ·
              refine ⟨4764306087455016107906959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6352408116606688143875945 4764306087455016107906959)
              ·
                refine ⟨7146459131182524161860439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764306087455016107906959 7146459131182524161860439)
                ·
                  refine ⟨10719688696773786242790659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7146459131182524161860439 10719688696773786242790659)
                  ·
                    refine ⟨16079533045160679364185989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10719688696773786242790659 16079533045160679364185989)
                    ·
                      refine ⟨3014912445967627380784873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16079533045160679364185989 3014912445967627380784873)
                      ·
                        rfl

theorem cell23_5871521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5871521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871521 prefixEnd_5871521 := by exact prefixLift 5871521
  have htrace : WordTrace (prefixWord ++ tailWord_5871521) baseStart_5871521 baseEnd_5871521 := by
    simpa [prefixWord, tailWord_5871521, baseEnd_5871521] using wordTrace_append hprefix tailTrace_5871521
  have hstable : (prefixWord ++ tailWord_5871521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871521).length < 2 ^ (prefixWord ++ tailWord_5871521).sum := by decide
  have hdescent : baseEnd_5871521 < baseStart_5871521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871524 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_5871524 : Nat := 118140960795 + 5871524 * 2 ^ 59
def prefixEnd_5871524 : Nat := 4983230072969 + 3 ^ 40 * 5871524 * 2
def baseEnd_5871524 : Nat := 3014913986409590869047359

theorem tailTrace_5871524 : CollatzResearch.WordTrace tailWord_5871524 prefixEnd_5871524 3014913986409590869047359 := by
  unfold tailWord_5871524
  simp only [CollatzResearch.WordTrace]
  refine ⟨107076036790239399654598813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142768049053652532872798417 107076036790239399654598813)
  ·
    refine ⟨40153513796339774870474555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107076036790239399654598813 40153513796339774870474555)
    ·
      refine ⟨60230270694509662305711833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40153513796339774870474555 60230270694509662305711833)
      ·
        refine ⟨45172703020882246729283875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60230270694509662305711833 45172703020882246729283875)
        ·
          refine ⟨67759054531323370093925813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45172703020882246729283875 67759054531323370093925813)
          ·
            refine ⟨6352411362311565946305545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67759054531323370093925813 6352411362311565946305545)
            ·
              refine ⟨4764308521733674459729159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6352411362311565946305545 4764308521733674459729159)
              ·
                refine ⟨7146462782600511689593739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764308521733674459729159 7146462782600511689593739)
                ·
                  refine ⟨10719694173900767534390609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7146462782600511689593739 10719694173900767534390609)
                  ·
                    refine ⟨8039770630425575650792957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10719694173900767534390609 8039770630425575650792957)
                    ·
                      refine ⟨3014913986409590869047359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039770630425575650792957 3014913986409590869047359)
                      ·
                        rfl

theorem cell23_5871524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_5871524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871524 prefixEnd_5871524 := by exact prefixLift 5871524
  have htrace : WordTrace (prefixWord ++ tailWord_5871524) baseStart_5871524 baseEnd_5871524 := by
    simpa [prefixWord, tailWord_5871524, baseEnd_5871524] using wordTrace_append hprefix tailTrace_5871524
  have hstable : (prefixWord ++ tailWord_5871524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871524).length < 2 ^ (prefixWord ++ tailWord_5871524).sum := by decide
  have hdescent : baseEnd_5871524 < baseStart_5871524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871537 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_5871537 : Nat := 118140960795 + 5871537 * 2 ^ 59
def prefixEnd_5871537 : Nat := 4983230072969 + 3 ^ 40 * 5871537 * 2
def baseEnd_5871537 : Nat := 3014920661658099318184799

theorem tailTrace_5871537 : CollatzResearch.WordTrace tailWord_5871537 prefixEnd_5871537 3014920661658099318184799 := by
  unfold tailWord_5871537
  simp only [CollatzResearch.WordTrace]
  refine ⟨214152547729431702529420865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142768365152954468352947243 214152547729431702529420865)
  ·
    refine ⟨160614410797073776897065649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214152547729431702529420865 160614410797073776897065649)
    ·
      refine ⟨120460808097805332672799237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160614410797073776897065649 120460808097805332672799237)
      ·
        refine ⟨22586401518338499876149857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120460808097805332672799237 22586401518338499876149857)
        ·
          refine ⟨16939801138753874907112393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22586401518338499876149857 16939801138753874907112393)
          ·
            refine ⟨12704850854065406180334295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16939801138753874907112393 12704850854065406180334295)
            ·
              refine ⟨19057276281098109270501443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12704850854065406180334295 19057276281098109270501443)
              ·
                refine ⟨28585914421647163905752165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19057276281098109270501443 28585914421647163905752165)
                ·
                  refine ⟨5359858954058843232328531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28585914421647163905752165 5359858954058843232328531)
                  ·
                    refine ⟨8039788431088264848492797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359858954058843232328531 8039788431088264848492797)
                    ·
                      refine ⟨3014920661658099318184799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8039788431088264848492797 3014920661658099318184799)
                      ·
                        rfl

theorem cell23_5871537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_5871537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871537 prefixEnd_5871537 := by exact prefixLift 5871537
  have htrace : WordTrace (prefixWord ++ tailWord_5871537) baseStart_5871537 baseEnd_5871537 := by
    simpa [prefixWord, tailWord_5871537, baseEnd_5871537] using wordTrace_append hprefix tailTrace_5871537
  have hstable : (prefixWord ++ tailWord_5871537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871537).length < 2 ^ (prefixWord ++ tailWord_5871537).sum := by decide
  have hdescent : baseEnd_5871537 < baseStart_5871537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871563 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5]
def baseStart_5871563 : Nat := 118140960795 + 5871563 * 2 ^ 59
def prefixEnd_5871563 : Nat := 4983230072969 + 3 ^ 40 * 5871563 * 2
def baseEnd_5871563 : Nat := 3014934012155116216459679

theorem tailTrace_5871563 : CollatzResearch.WordTrace tailWord_5871563 prefixEnd_5871563 3014934012155116216459679 := by
  unfold tailWord_5871563
  simp only [CollatzResearch.WordTrace]
  refine ⟨214153496027337508969867343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142768997351558339313244895 214153496027337508969867343)
  ·
    refine ⟨321230244041006263454801015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214153496027337508969867343 321230244041006263454801015)
    ·
      refine ⟨481845366061509395182201523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321230244041006263454801015 481845366061509395182201523)
      ·
        refine ⟨722768049092264092773302285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481845366061509395182201523 722768049092264092773302285)
        ·
          refine ⟨271038018409599034789988357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722768049092264092773302285 271038018409599034789988357)
          ·
            refine ⟨50819628451799819023122817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271038018409599034789988357 50819628451799819023122817)
            ·
              refine ⟨38114721338849864267342113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50819628451799819023122817 38114721338849864267342113)
              ·
                refine ⟨28586041004137398200506585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38114721338849864267342113 28586041004137398200506585)
                ·
                  refine ⟨21439530753103048650379939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28586041004137398200506585 21439530753103048650379939)
                  ·
                    refine ⟨32159296129654572975569909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21439530753103048650379939 32159296129654572975569909)
                    ·
                      refine ⟨3014934012155116216459679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32159296129654572975569909 3014934012155116216459679)
                      ·
                        rfl

theorem cell23_5871563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_5871563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871563 prefixEnd_5871563 := by exact prefixLift 5871563
  have htrace : WordTrace (prefixWord ++ tailWord_5871563) baseStart_5871563 baseEnd_5871563 := by
    simpa [prefixWord, tailWord_5871563, baseEnd_5871563] using wordTrace_append hprefix tailTrace_5871563
  have hstable : (prefixWord ++ tailWord_5871563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871563).length < 2 ^ (prefixWord ++ tailWord_5871563).sum := by decide
  have hdescent : baseEnd_5871563 < baseStart_5871563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871564 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 1, 3, 2]
def baseStart_5871564 : Nat := 118140960795 + 5871564 * 2 ^ 59
def prefixEnd_5871564 : Nat := 4983230072969 + 3 ^ 40 * 5871564 * 2
def baseEnd_5871564 : Nat := 3014934525635770712547175

theorem tailTrace_5871564 : CollatzResearch.WordTrace tailWord_5871564 prefixEnd_5871564 3014934525635770712547175 := by
  unfold tailWord_5871564
  simp only [CollatzResearch.WordTrace]
  refine ⟨107076766250166943070326873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142769021666889257427102497 107076766250166943070326873)
  ·
    refine ⟨80307574687625207302745155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107076766250166943070326873 80307574687625207302745155)
    ·
      refine ⟨120461362031437810954117733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80307574687625207302745155 120461362031437810954117733)
      ·
        refine ⟨22586505380894589553897075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120461362031437810954117733 22586505380894589553897075)
        ·
          refine ⟨33879758071341884330845613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22586505380894589553897075 33879758071341884330845613)
          ·
            refine ⟨12704909276753206624067105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33879758071341884330845613 12704909276753206624067105)
            ·
              refine ⟨9528681957564904968050329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12704909276753206624067105 9528681957564904968050329)
              ·
                refine ⟨7146511468173678726037747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9528681957564904968050329 7146511468173678726037747)
                ·
                  refine ⟨10719767202260518089056621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7146511468173678726037747 10719767202260518089056621)
                  ·
                    refine ⟨4019912700847694283396233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10719767202260518089056621 4019912700847694283396233)
                    ·
                      refine ⟨3014934525635770712547175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019912700847694283396233 3014934525635770712547175)
                      ·
                        rfl

theorem cell23_5871564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_5871564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871564 prefixEnd_5871564 := by exact prefixLift 5871564
  have htrace : WordTrace (prefixWord ++ tailWord_5871564) baseStart_5871564 baseEnd_5871564 := by
    simpa [prefixWord, tailWord_5871564, baseEnd_5871564] using wordTrace_append hprefix tailTrace_5871564
  have hstable : (prefixWord ++ tailWord_5871564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871564).length < 2 ^ (prefixWord ++ tailWord_5871564).sum := by decide
  have hdescent : baseEnd_5871564 < baseStart_5871564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871594 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_5871594 : Nat := 118140960795 + 5871594 * 2 ^ 59
def prefixEnd_5871594 : Nat := 4983230072969 + 3 ^ 40 * 5871594 * 2
def baseEnd_5871594 : Nat := 3014949930055405595172037

theorem tailTrace_5871594 : CollatzResearch.WordTrace tailWord_5871594 prefixEnd_5871594 3014949930055405595172037 := by
  unfold tailWord_5871594
  simp only [CollatzResearch.WordTrace]
  refine ⟨53538656672556300316061459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142769751126816800842830557 53538656672556300316061459)
  ·
    refine ⟨80307985008834450474092189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53538656672556300316061459 80307985008834450474092189)
    ·
      refine ⟨30115494378312918927784571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80307985008834450474092189 30115494378312918927784571)
      ·
        refine ⟨45173241567469378391676857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30115494378312918927784571 45173241567469378391676857)
        ·
          refine ⟨33879931175602033793757643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45173241567469378391676857 33879931175602033793757643)
          ·
            refine ⟨50819896763403050690636465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33879931175602033793757643 50819896763403050690636465)
            ·
              refine ⟨38114922572552288017977349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50819896763403050690636465 38114922572552288017977349)
              ·
                refine ⟨7146547982353554003370753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38114922572552288017977349 7146547982353554003370753)
                ·
                  refine ⟨5359910986765165502528065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7146547982353554003370753 5359910986765165502528065)
                  ·
                    refine ⟨4019933240073874126896049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5359910986765165502528065 4019933240073874126896049)
                    ·
                      refine ⟨3014949930055405595172037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4019933240073874126896049 3014949930055405595172037)
                      ·
                        rfl

theorem cell23_5871594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_5871594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871594 prefixEnd_5871594 := by exact prefixLift 5871594
  have htrace : WordTrace (prefixWord ++ tailWord_5871594) baseStart_5871594 baseEnd_5871594 := by
    simpa [prefixWord, tailWord_5871594, baseEnd_5871594] using wordTrace_append hprefix tailTrace_5871594
  have hstable : (prefixWord ++ tailWord_5871594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871594).length < 2 ^ (prefixWord ++ tailWord_5871594).sum := by decide
  have hdescent : baseEnd_5871594 < baseStart_5871594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871600 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 5]
def baseStart_5871600 : Nat := 118140960795 + 5871600 * 2 ^ 59
def prefixEnd_5871600 : Nat := 4983230072969 + 3 ^ 40 * 5871600 * 2
def baseEnd_5871600 : Nat := 334994778993259174633001

theorem tailTrace_5871600 : CollatzResearch.WordTrace tailWord_5871600 prefixEnd_5871600 334994778993259174633001 := by
  unfold tailWord_5871600
  simp only [CollatzResearch.WordTrace]
  refine ⟨107077422764101732144482127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142769897018802309525976169 107077422764101732144482127)
  ·
    refine ⟨160616134146152598216723191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107077422764101732144482127 160616134146152598216723191)
    ·
      refine ⟨240924201219228897325084787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160616134146152598216723191 240924201219228897325084787)
      ·
        refine ⟨361386301828843345987627181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240924201219228897325084787 361386301828843345987627181)
        ·
          refine ⟨135519863185816254745360193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361386301828843345987627181 135519863185816254745360193)
          ·
            refine ⟨101639897389362191059020145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135519863185816254745360193 101639897389362191059020145)
            ·
              refine ⟨76229923042021643294265109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101639897389362191059020145 76229923042021643294265109)
              ·
                refine ⟨3573277642594764529418677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76229923042021643294265109 3573277642594764529418677)
                ·
                  refine ⟨334994778993259174633001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3573277642594764529418677 334994778993259174633001)
                  ·
                    rfl

theorem cell23_5871600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 5].length) (baseStart_5871600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871600 prefixEnd_5871600 := by exact prefixLift 5871600
  have htrace : WordTrace (prefixWord ++ tailWord_5871600) baseStart_5871600 baseEnd_5871600 := by
    simpa [prefixWord, tailWord_5871600, baseEnd_5871600] using wordTrace_append hprefix tailTrace_5871600
  have hstable : (prefixWord ++ tailWord_5871600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871600).length < 2 ^ (prefixWord ++ tailWord_5871600).sum := by decide
  have hdescent : baseEnd_5871600 < baseStart_5871600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871613 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_5871613 : Nat := 118140960795 + 5871613 * 2 ^ 59
def prefixEnd_5871613 : Nat := 4983230072969 + 3 ^ 40 * 5871613 * 2
def baseEnd_5871613 : Nat := 1004986562062613673611483

theorem tailTrace_5871613 : CollatzResearch.WordTrace tailWord_5871613 prefixEnd_5871613 1004986562062613673611483 := by
  unfold tailWord_5871613
  simp only [CollatzResearch.WordTrace]
  refine ⟨214155319677156367509187493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142770213118104245006124995 214155319677156367509187493)
  ·
    refine ⟨40154122439466818907972655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214155319677156367509187493 40154122439466818907972655)
    ·
      refine ⟨60231183659200228361958983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40154122439466818907972655 60231183659200228361958983)
      ·
        refine ⟨90346775488800342542938475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60231183659200228361958983 90346775488800342542938475)
        ·
          refine ⟨135520163233200513814407713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90346775488800342542938475 135520163233200513814407713)
          ·
            refine ⟨101640122424900385360805785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135520163233200513814407713 101640122424900385360805785)
            ·
              refine ⟨76230091818675289020604339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101640122424900385360805785 76230091818675289020604339)
              ·
                refine ⟨114345137728012933530906509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76230091818675289020604339 114345137728012933530906509)
                ·
                  refine ⟨42879426648004850074089941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114345137728012933530906509 42879426648004850074089941)
                  ·
                    refine ⟨1004986562062613673611483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42879426648004850074089941 1004986562062613673611483)
                    ·
                      rfl

theorem cell23_5871613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_5871613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871613 prefixEnd_5871613 := by exact prefixLift 5871613
  have htrace : WordTrace (prefixWord ++ tailWord_5871613) baseStart_5871613 baseEnd_5871613 := by
    simpa [prefixWord, tailWord_5871613, baseEnd_5871613] using wordTrace_append hprefix tailTrace_5871613
  have hstable : (prefixWord ++ tailWord_5871613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871613).length < 2 ^ (prefixWord ++ tailWord_5871613).sum := by decide
  have hdescent : baseEnd_5871613 < baseStart_5871613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871663 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_5871663 : Nat := 118140960795 + 5871663 * 2 ^ 59
def prefixEnd_5871663 : Nat := 4983230072969 + 3 ^ 40 * 5871663 * 2
def baseEnd_5871663 : Nat := 3014985360220565825209219

theorem tailTrace_5871663 : CollatzResearch.WordTrace tailWord_5871663 prefixEnd_5871663 3014985360220565825209219 := by
  unfold tailWord_5871663
  simp only [CollatzResearch.WordTrace]
  refine ⟨214157143326975226048507643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142771428884650150699005095 214157143326975226048507643)
  ·
    refine ⟨321235714990462839072761465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214157143326975226048507643 321235714990462839072761465)
    ·
      refine ⟨240926786242847129304571099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321235714990462839072761465 240926786242847129304571099)
      ·
        refine ⟨361390179364270693956856649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240926786242847129304571099 361390179364270693956856649)
        ·
          refine ⟨271042634523203020467642487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361390179364270693956856649 271042634523203020467642487)
          ·
            refine ⟨406563951784804530701463731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271042634523203020467642487 406563951784804530701463731)
            ·
              refine ⟨609845927677206796052195597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406563951784804530701463731 609845927677206796052195597)
              ·
                refine ⟨228692222878952548519573349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609845927677206796052195597 228692222878952548519573349)
                ·
                  refine ⟨42879791789803602847420003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228692222878952548519573349 42879791789803602847420003)
                  ·
                    refine ⟨64319687684705404271130005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42879791789803602847420003 64319687684705404271130005)
                    ·
                      refine ⟨3014985360220565825209219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64319687684705404271130005 3014985360220565825209219)
                      ·
                        rfl

theorem cell23_5871663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_5871663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871663 prefixEnd_5871663 := by exact prefixLift 5871663
  have htrace : WordTrace (prefixWord ++ tailWord_5871663) baseStart_5871663 baseEnd_5871663 := by
    simpa [prefixWord, tailWord_5871663, baseEnd_5871663] using wordTrace_append hprefix tailTrace_5871663
  have hstable : (prefixWord ++ tailWord_5871663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871663).length < 2 ^ (prefixWord ++ tailWord_5871663).sum := by decide
  have hdescent : baseEnd_5871663 < baseStart_5871663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871677 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_5871677 : Nat := 118140960795 + 5871677 * 2 ^ 59
def prefixEnd_5871677 : Nat := 4983230072969 + 3 ^ 40 * 5871677 * 2
def baseEnd_5871677 : Nat := 1004997516316576256811385

theorem tailTrace_5871677 : CollatzResearch.WordTrace tailWord_5871677 prefixEnd_5871677 1004997516316576256811385 := by
  unfold tailWord_5871677
  simp only [CollatzResearch.WordTrace]
  refine ⟨214157653948924506439517285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142771769299283004293011523 214157653948924506439517285)
  ·
    refine ⟨40154560115423344957409491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214157653948924506439517285 40154560115423344957409491)
    ·
      refine ⟨60231840173135017436114237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40154560115423344957409491 60231840173135017436114237)
      ·
        refine ⟨22586940064925631538542839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60231840173135017436114237 22586940064925631538542839)
        ·
          refine ⟨33880410097388447307814259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22586940064925631538542839 33880410097388447307814259)
          ·
            refine ⟨50820615146082670961721389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33880410097388447307814259 50820615146082670961721389)
            ·
              refine ⟨19057730679781001610645521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50820615146082670961721389 19057730679781001610645521)
              ·
                refine ⟨14293298009835751207984141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19057730679781001610645521 14293298009835751207984141)
                ·
                  refine ⟨5359986753688406702994053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14293298009835751207984141 5359986753688406702994053)
                  ·
                    refine ⟨1004997516316576256811385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5359986753688406702994053 1004997516316576256811385)
                    ·
                      rfl

theorem cell23_5871677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_5871677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871677 prefixEnd_5871677 := by exact prefixLift 5871677
  have htrace : WordTrace (prefixWord ++ tailWord_5871677) baseStart_5871677 baseEnd_5871677 := by
    simpa [prefixWord, tailWord_5871677, baseEnd_5871677] using wordTrace_append hprefix tailTrace_5871677
  have hstable : (prefixWord ++ tailWord_5871677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871677).length < 2 ^ (prefixWord ++ tailWord_5871677).sum := by decide
  have hdescent : baseEnd_5871677 < baseStart_5871677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871694 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_5871694 : Nat := 118140960795 + 5871694 * 2 ^ 59
def prefixEnd_5871694 : Nat := 4983230072969 + 3 ^ 40 * 5871694 * 2
def baseEnd_5871694 : Nat := 1005000426040285067973859

theorem tailTrace_5871694 : CollatzResearch.WordTrace tailWord_5871694 prefixEnd_5871694 1005000426040285067973859 := by
  unfold tailWord_5871694
  simp only [CollatzResearch.WordTrace]
  refine ⟨26769784248732864792860767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142772182659908612228590757 26769784248732864792860767)
  ·
    refine ⟨40154676373099297189291151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26769784248732864792860767 40154676373099297189291151)
    ·
      refine ⟨60232014559648945783936727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40154676373099297189291151 60232014559648945783936727)
      ·
        refine ⟨90348021839473418675905091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60232014559648945783936727 90348021839473418675905091)
        ·
          refine ⟨135522032759210128013857637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90348021839473418675905091 135522032759210128013857637)
          ·
            refine ⟨25410381142351899002598307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135522032759210128013857637 25410381142351899002598307)
            ·
              refine ⟨38115571713527848503897461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25410381142351899002598307 38115571713527848503897461)
              ·
                refine ⟨3573334848143235797240387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38115571713527848503897461 3573334848143235797240387)
                ·
                  refine ⟨5360002272214853695860581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573334848143235797240387 5360002272214853695860581)
                  ·
                    refine ⟨1005000426040285067973859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360002272214853695860581 1005000426040285067973859)
                    ·
                      rfl

theorem cell23_5871694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_5871694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871694 prefixEnd_5871694 := by exact prefixLift 5871694
  have htrace : WordTrace (prefixWord ++ tailWord_5871694) baseStart_5871694 baseEnd_5871694 := by
    simpa [prefixWord, tailWord_5871694, baseEnd_5871694] using wordTrace_append hprefix tailTrace_5871694
  have hstable : (prefixWord ++ tailWord_5871694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871694).length < 2 ^ (prefixWord ++ tailWord_5871694).sum := by decide
  have hdescent : baseEnd_5871694 < baseStart_5871694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871727 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 1, 5, 2]
def baseStart_5871727 : Nat := 118140960795 + 5871727 * 2 ^ 59
def prefixEnd_5871727 : Nat := 4983230072969 + 3 ^ 40 * 5871727 * 2
def baseEnd_5871727 : Nat := 3015018222982453574808925

theorem tailTrace_5871727 : CollatzResearch.WordTrace tailWord_5871727 prefixEnd_5871727 3015018222982453574808925 := by
  unfold tailWord_5871727
  simp only [CollatzResearch.WordTrace]
  refine ⟨214159477598743364978837435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142772985065828909985891623 214159477598743364978837435)
  ·
    refine ⟨321239216398115047468256153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214159477598743364978837435 321239216398115047468256153)
    ·
      refine ⟨240929412298586285601192115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321239216398115047468256153 240929412298586285601192115)
      ·
        refine ⟨361394118447879428401788173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240929412298586285601192115 361394118447879428401788173)
        ·
          refine ⟨135522794417954785650670565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361394118447879428401788173 135522794417954785650670565)
          ·
            refine ⟨25410523953366522309500731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135522794417954785650670565 25410523953366522309500731)
            ·
              refine ⟨38115785930049783464251097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25410523953366522309500731 38115785930049783464251097)
              ·
                refine ⟨28586839447537337598188323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38115785930049783464251097 28586839447537337598188323)
                ·
                  refine ⟨42880259171306006397282485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28586839447537337598188323 42880259171306006397282485)
                  ·
                    refine ⟨4020024297309938099745233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42880259171306006397282485 4020024297309938099745233)
                    ·
                      refine ⟨3015018222982453574808925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020024297309938099745233 3015018222982453574808925)
                      ·
                        rfl

theorem cell23_5871727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5, 2].length) (baseStart_5871727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871727 prefixEnd_5871727 := by exact prefixLift 5871727
  have htrace : WordTrace (prefixWord ++ tailWord_5871727) baseStart_5871727 baseEnd_5871727 := by
    simpa [prefixWord, tailWord_5871727, baseEnd_5871727] using wordTrace_append hprefix tailTrace_5871727
  have hstable : (prefixWord ++ tailWord_5871727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871727).length < 2 ^ (prefixWord ++ tailWord_5871727).sum := by decide
  have hdescent : baseEnd_5871727 < baseStart_5871727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871737 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 1, 5]
def baseStart_5871737 : Nat := 118140960795 + 5871737 * 2 ^ 59
def prefixEnd_5871737 : Nat := 4983230072969 + 3 ^ 40 * 5871737 * 2
def baseEnd_5871737 : Nat := 1005007785929666178561293

theorem tailTrace_5871737 : CollatzResearch.WordTrace tailWord_5871737 prefixEnd_5871737 1005007785929666178561293 := by
  unfold tailWord_5871737
  simp only [CollatzResearch.WordTrace]
  refine ⟨214159842328707136686701465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142773228219138091124467643 214159842328707136686701465)
  ·
    refine ⟨160619881746530352515026099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214159842328707136686701465 160619881746530352515026099)
    ·
      refine ⟨240929822619795528772539149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160619881746530352515026099 240929822619795528772539149)
      ·
        refine ⟨90348683482423323289702181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240929822619795528772539149 90348683482423323289702181)
        ·
          refine ⟨16940378152954373116819159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90348683482423323289702181 16940378152954373116819159)
          ·
            refine ⟨25410567229431559675228739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940378152954373116819159 25410567229431559675228739)
            ·
              refine ⟨38115850844147339512843109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25410567229431559675228739 38115850844147339512843109)
              ·
                refine ⟨7146722033277626158658083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38115850844147339512843109 7146722033277626158658083)
                ·
                  refine ⟨10720083049916439237987125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7146722033277626158658083 10720083049916439237987125)
                  ·
                    refine ⟨1005007785929666178561293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10720083049916439237987125 1005007785929666178561293)
                    ·
                      rfl

theorem cell23_5871737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_5871737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871737 prefixEnd_5871737 := by exact prefixLift 5871737
  have htrace : WordTrace (prefixWord ++ tailWord_5871737) baseStart_5871737 baseEnd_5871737 := by
    simpa [prefixWord, tailWord_5871737, baseEnd_5871737] using wordTrace_append hprefix tailTrace_5871737
  have hstable : (prefixWord ++ tailWord_5871737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871737).length < 2 ^ (prefixWord ++ tailWord_5871737).sum := by decide
  have hdescent : baseEnd_5871737 < baseStart_5871737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871751 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_5871751 : Nat := 118140960795 + 5871751 * 2 ^ 59
def prefixEnd_5871751 : Nat := 4983230072969 + 3 ^ 40 * 5871751 * 2
def baseEnd_5871751 : Nat := 3015030546518161480908815

theorem tailTrace_5871751 : CollatzResearch.WordTrace tailWord_5871751 prefixEnd_5871751 3015030546518161480908815 := by
  unfold tailWord_5871751
  simp only [CollatzResearch.WordTrace]
  refine ⟨214160352950656417077711107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142773568633770944718474071 214160352950656417077711107)
  ·
    refine ⟨321240529425984625616566661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214160352950656417077711107 321240529425984625616566661)
    ·
      refine ⟨60232599267372117303106249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321240529425984625616566661 60232599267372117303106249)
      ·
        refine ⟨45174449450529087977329687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60232599267372117303106249 45174449450529087977329687)
        ·
          refine ⟨67761674175793631965994531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45174449450529087977329687 67761674175793631965994531)
          ·
            refine ⟨101642511263690447948991797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67761674175793631965994531 101642511263690447948991797)
            ·
              refine ⟨9528985430970979495217981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101642511263690447948991797 9528985430970979495217981)
              ·
                refine ⟨3573369536614117310706743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9528985430970979495217981 3573369536614117310706743)
                ·
                  refine ⟨5360054304921175966060115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573369536614117310706743 5360054304921175966060115)
                  ·
                    refine ⟨8040081457381763949090173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5360054304921175966060115 8040081457381763949090173)
                    ·
                      refine ⟨3015030546518161480908815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8040081457381763949090173 3015030546518161480908815)
                      ·
                        rfl

theorem cell23_5871751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_5871751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871751 prefixEnd_5871751 := by exact prefixLift 5871751
  have htrace : WordTrace (prefixWord ++ tailWord_5871751) baseStart_5871751 baseEnd_5871751 := by
    simpa [prefixWord, tailWord_5871751, baseEnd_5871751] using wordTrace_append hprefix tailTrace_5871751
  have hstable : (prefixWord ++ tailWord_5871751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871751).length < 2 ^ (prefixWord ++ tailWord_5871751).sum := by decide
  have hdescent : baseEnd_5871751 < baseStart_5871751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871768 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 3, 1, 3]
def baseStart_5871768 : Nat := 118140960795 + 5871768 * 2 ^ 59
def prefixEnd_5871768 : Nat := 4983230072969 + 3 ^ 40 * 5871768 * 2
def baseEnd_5871768 : Nat := 3015039275689287914396237

theorem tailTrace_5871768 : CollatzResearch.WordTrace tailWord_5871768 prefixEnd_5871768 3015039275689287914396237 := by
  unfold tailWord_5871768
  simp only [CollatzResearch.WordTrace]
  refine ⟨107080486495797414490539979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142773981994396552654053305 107080486495797414490539979)
  ·
    refine ⟨160620729743696121735809969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107080486495797414490539979 160620729743696121735809969)
    ·
      refine ⟨120465547307772091301857477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160620729743696121735809969 120465547307772091301857477)
      ·
        refine ⟨22587290120207267119098277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120465547307772091301857477 22587290120207267119098277)
        ·
          refine ⟨4235116897538862584830927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22587290120207267119098277 4235116897538862584830927)
          ·
            refine ⟨6352675346308293877246391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235116897538862584830927 6352675346308293877246391)
            ·
              refine ⟨9529013019462440815869587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352675346308293877246391 9529013019462440815869587)
              ·
                refine ⟨14293519529193661223804381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529013019462440815869587 14293519529193661223804381)
                ·
                  refine ⟨5360069823447622958926643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14293519529193661223804381 5360069823447622958926643)
                  ·
                    refine ⟨8040104735171434438389965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5360069823447622958926643 8040104735171434438389965)
                    ·
                      refine ⟨3015039275689287914396237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8040104735171434438389965 3015039275689287914396237)
                      ·
                        rfl

theorem cell23_5871768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_5871768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871768 prefixEnd_5871768 := by exact prefixLift 5871768
  have htrace : WordTrace (prefixWord ++ tailWord_5871768) baseStart_5871768 baseEnd_5871768 := by
    simpa [prefixWord, tailWord_5871768, baseEnd_5871768] using wordTrace_append hprefix tailTrace_5871768
  have hstable : (prefixWord ++ tailWord_5871768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871768).length < 2 ^ (prefixWord ++ tailWord_5871768).sum := by decide
  have hdescent : baseEnd_5871768 < baseStart_5871768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871777 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5871777 : Nat := 118140960795 + 5871777 * 2 ^ 59
def prefixEnd_5871777 : Nat := 4983230072969 + 3 ^ 40 * 5871777 * 2
def baseEnd_5871777 : Nat := 3015043897015178379183695

theorem tailTrace_5871777 : CollatzResearch.WordTrace tailWord_5871777 prefixEnd_5871777 3015043897015178379183695 := by
  unfold tailWord_5871777
  simp only [CollatzResearch.WordTrace]
  refine ⟨214161301248562223518157585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142774200832374815678771723 214161301248562223518157585)
  ·
    refine ⟨160620975936421667638618189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214161301248562223518157585 160620975936421667638618189)
    ·
      refine ⟨60232865976158125364481821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160620975936421667638618189 60232865976158125364481821)
      ·
        refine ⟨22587324741059297011680683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60232865976158125364481821 22587324741059297011680683)
        ·
          refine ⟨33880987111588945517521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22587324741059297011680683 33880987111588945517521025)
          ·
            refine ⟨25410740333691709138140769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33880987111588945517521025 25410740333691709138140769)
            ·
              refine ⟨19058055250268781853605577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25410740333691709138140769 19058055250268781853605577)
              ·
                refine ⟨14293541437701586390204183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19058055250268781853605577 14293541437701586390204183)
                ·
                  refine ⟨21440312156552379585306275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14293541437701586390204183 21440312156552379585306275)
                  ·
                    refine ⟨32160468234828569377959413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21440312156552379585306275 32160468234828569377959413)
                    ·
                      refine ⟨3015043897015178379183695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32160468234828569377959413 3015043897015178379183695)
                      ·
                        rfl

theorem cell23_5871777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5871777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871777 prefixEnd_5871777 := by exact prefixLift 5871777
  have htrace : WordTrace (prefixWord ++ tailWord_5871777) baseStart_5871777 baseEnd_5871777 := by
    simpa [prefixWord, tailWord_5871777, baseEnd_5871777] using wordTrace_append hprefix tailTrace_5871777
  have hstable : (prefixWord ++ tailWord_5871777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871777).length < 2 ^ (prefixWord ++ tailWord_5871777).sum := by decide
  have hdescent : baseEnd_5871777 < baseStart_5871777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871804 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5871804 : Nat := 118140960795 + 5871804 * 2 ^ 59
def prefixEnd_5871804 : Nat := 4983230072969 + 3 ^ 40 * 5871804 * 2
def baseEnd_5871804 : Nat := 3015057760992849773546071

theorem tailTrace_5871804 : CollatzResearch.WordTrace tailWord_5871804 prefixEnd_5871804 3015057760992849773546071 := by
  unfold tailWord_5871804
  simp only [CollatzResearch.WordTrace]
  refine ⟨107081143009732203564695233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142774857346309604752926977 107081143009732203564695233)
  ·
    refine ⟨80310857257299152673521425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107081143009732203564695233 80310857257299152673521425)
    ·
      refine ⟨60233142942974364505141069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80310857257299152673521425 60233142942974364505141069)
      ·
        refine ⟨22587428603615386689427901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60233142942974364505141069 22587428603615386689427901)
        ·
          refine ⟨8470285726355770008535463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22587428603615386689427901 8470285726355770008535463)
          ·
            refine ⟨12705428589533655012803195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470285726355770008535463 12705428589533655012803195)
            ·
              refine ⟨19058142884300482519204793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12705428589533655012803195 19058142884300482519204793)
              ·
                refine ⟨14293607163225361889403595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19058142884300482519204793 14293607163225361889403595)
                ·
                  refine ⟨21440410744838042834105393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14293607163225361889403595 21440410744838042834105393)
                  ·
                    refine ⟨16080308058628532125579045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21440410744838042834105393 16080308058628532125579045)
                    ·
                      refine ⟨3015057760992849773546071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16080308058628532125579045 3015057760992849773546071)
                      ·
                        rfl

theorem cell23_5871804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5871804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871804 prefixEnd_5871804 := by exact prefixLift 5871804
  have htrace : WordTrace (prefixWord ++ tailWord_5871804) baseStart_5871804 baseEnd_5871804 := by
    simpa [prefixWord, tailWord_5871804, baseEnd_5871804] using wordTrace_append hprefix tailTrace_5871804
  have hstable : (prefixWord ++ tailWord_5871804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871804).length < 2 ^ (prefixWord ++ tailWord_5871804).sum := by decide
  have hdescent : baseEnd_5871804 < baseStart_5871804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871834 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2]
def baseStart_5871834 : Nat := 118140960795 + 5871834 * 2 ^ 59
def prefixEnd_5871834 : Nat := 4983230072969 + 3 ^ 40 * 5871834 * 2
def baseEnd_5871834 : Nat := 3015073165412484656170933

theorem tailTrace_5871834 : CollatzResearch.WordTrace tailWord_5871834 prefixEnd_5871834 3015073165412484656170933 := by
  unfold tailWord_5871834
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540845052338930563245639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142775586806237148168655037 53540845052338930563245639)
  ·
    refine ⟨80311267578508395844868459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53540845052338930563245639 80311267578508395844868459)
    ·
      refine ⟨120466901367762593767302689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80311267578508395844868459 120466901367762593767302689)
      ·
        refine ⟨90350176025821945325477017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120466901367762593767302689 90350176025821945325477017)
        ·
          refine ⟨67762632019366458994107763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90350176025821945325477017 67762632019366458994107763)
          ·
            refine ⟨101643948029049688491161645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67762632019366458994107763 101643948029049688491161645)
            ·
              refine ⟨38116480510893633184185617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101643948029049688491161645 38116480510893633184185617)
              ·
                refine ⟨28587360383170224888139213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38116480510893633184185617 28587360383170224888139213)
                ·
                  refine ⟨10720260143688834333052205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28587360383170224888139213 10720260143688834333052205)
                  ·
                    refine ⟨4020097553883312874894577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10720260143688834333052205 4020097553883312874894577)
                    ·
                      refine ⟨3015073165412484656170933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020097553883312874894577 3015073165412484656170933)
                      ·
                        rfl

theorem cell23_5871834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_5871834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871834 prefixEnd_5871834 := by exact prefixLift 5871834
  have htrace : WordTrace (prefixWord ++ tailWord_5871834) baseStart_5871834 baseEnd_5871834 := by
    simpa [prefixWord, tailWord_5871834, baseEnd_5871834] using wordTrace_append hprefix tailTrace_5871834
  have hstable : (prefixWord ++ tailWord_5871834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871834).length < 2 ^ (prefixWord ++ tailWord_5871834).sum := by decide
  have hdescent : baseEnd_5871834 < baseStart_5871834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871842 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5871842 : Nat := 118140960795 + 5871842 * 2 ^ 59
def prefixEnd_5871842 : Nat := 4983230072969 + 3 ^ 40 * 5871842 * 2
def baseEnd_5871842 : Nat := 3015077273257720624870897

theorem tailTrace_5871842 : CollatzResearch.WordTrace tailWord_5871842 prefixEnd_5871842 3015077273257720624870897 := by
  unfold tailWord_5871842
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540917998331684904818445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142775781328884493079515853 53540917998331684904818445)
  ·
    refine ⟨20077844249374381839306917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53540917998331684904818445 20077844249374381839306917)
    ·
      refine ⟨3764595796757696594870047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20077844249374381839306917 3764595796757696594870047)
      ·
        refine ⟨5646893695136544892305071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764595796757696594870047 5646893695136544892305071)
        ·
          refine ⟨8470340542704817338457607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646893695136544892305071 8470340542704817338457607)
          ·
            refine ⟨12705510814057226007686411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470340542704817338457607 12705510814057226007686411)
            ·
              refine ⟨19058266221085839011529617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12705510814057226007686411 19058266221085839011529617)
              ·
                refine ⟨14293699665814379258647213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19058266221085839011529617 14293699665814379258647213)
                ·
                  refine ⟨5360137374680392221992705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14293699665814379258647213 5360137374680392221992705)
                  ·
                    refine ⟨4020103031010294166494529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5360137374680392221992705 4020103031010294166494529)
                    ·
                      refine ⟨3015077273257720624870897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020103031010294166494529 3015077273257720624870897)
                      ·
                        rfl

theorem cell23_5871842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5871842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871842 prefixEnd_5871842 := by exact prefixLift 5871842
  have htrace : WordTrace (prefixWord ++ tailWord_5871842) baseStart_5871842 baseEnd_5871842 := by
    simpa [prefixWord, tailWord_5871842, baseEnd_5871842] using wordTrace_append hprefix tailTrace_5871842
  have hstable : (prefixWord ++ tailWord_5871842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871842).length < 2 ^ (prefixWord ++ tailWord_5871842).sum := by decide
  have hdescent : baseEnd_5871842 < baseStart_5871842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871868 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_5871868 : Nat := 118140960795 + 5871868 * 2 ^ 59
def prefixEnd_5871868 : Nat := 4983230072969 + 3 ^ 40 * 5871868 * 2
def baseEnd_5871868 : Nat := 3015090623754737523145777

theorem tailTrace_5871868 : CollatzResearch.WordTrace tailWord_5871868 prefixEnd_5871868 3015090623754737523145777 := by
  unfold tailWord_5871868
  simp only [CollatzResearch.WordTrace]
  refine ⟨107082310145616273029860129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142776413527488364039813505 107082310145616273029860129)
  ·
    refine ⟨80311732609212204772395097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107082310145616273029860129 80311732609212204772395097)
    ·
      refine ⟨60233799456909153579296323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80311732609212204772395097 60233799456909153579296323)
      ·
        refine ⟨90350699185363730368944485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60233799456909153579296323 90350699185363730368944485)
        ·
          refine ⟨16940756097255699444177091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90350699185363730368944485 16940756097255699444177091)
          ·
            refine ⟨25411134145883549166265637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940756097255699444177091 25411134145883549166265637)
            ·
              refine ⟨4764587652353165468674807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25411134145883549166265637 4764587652353165468674807)
              ·
                refine ⟨7146881478529748203012211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764587652353165468674807 7146881478529748203012211)
                ·
                  refine ⟨10720322217794622304518317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7146881478529748203012211 10720322217794622304518317)
                  ·
                    refine ⟨4020120831672983364194369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10720322217794622304518317 4020120831672983364194369)
                    ·
                      refine ⟨3015090623754737523145777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020120831672983364194369 3015090623754737523145777)
                      ·
                        rfl

theorem cell23_5871868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_5871868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871868 prefixEnd_5871868 := by exact prefixLift 5871868
  have htrace : WordTrace (prefixWord ++ tailWord_5871868) baseStart_5871868 baseEnd_5871868 := by
    simpa [prefixWord, tailWord_5871868, baseEnd_5871868] using wordTrace_append hprefix tailTrace_5871868
  have hstable : (prefixWord ++ tailWord_5871868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871868).length < 2 ^ (prefixWord ++ tailWord_5871868).sum := by decide
  have hdescent : baseEnd_5871868 < baseStart_5871868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871874 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5871874 : Nat := 118140960795 + 5871874 * 2 ^ 59
def prefixEnd_5871874 : Nat := 4983230072969 + 3 ^ 40 * 5871874 * 2
def baseEnd_5871874 : Nat := 1005031234879554833223583

theorem tailTrace_5871874 : CollatzResearch.WordTrace tailWord_5871874 prefixEnd_5871874 1005031234879554833223583 := by
  unfold tailWord_5871874
  simp only [CollatzResearch.WordTrace]
  refine ⟨53541209782302702271109669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142776559419473872722959117 53541209782302702271109669)
  ·
    refine ⟨10038976834181756675833063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53541209782302702271109669 10038976834181756675833063)
    ·
      refine ⟨15058465251272635013749595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10038976834181756675833063 15058465251272635013749595)
      ·
        refine ⟨22587697876908952520624393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15058465251272635013749595 22587697876908952520624393)
        ·
          refine ⟨16940773407681714390468295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22587697876908952520624393 16940773407681714390468295)
          ·
            refine ⟨25411160111522571585702443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940773407681714390468295 25411160111522571585702443)
            ·
              refine ⟨38116740167283857378553665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25411160111522571585702443 38116740167283857378553665)
              ·
                refine ⟨28587555125462893033915249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38116740167283857378553665 28587555125462893033915249)
                ·
                  refine ⟨21440666344097169775436437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28587555125462893033915249 21440666344097169775436437)
                  ·
                    refine ⟨1005031234879554833223583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21440666344097169775436437 1005031234879554833223583)
                    ·
                      rfl

theorem cell23_5871874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5871874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871874 prefixEnd_5871874 := by exact prefixLift 5871874
  have htrace : WordTrace (prefixWord ++ tailWord_5871874) baseStart_5871874 baseEnd_5871874 := by
    simpa [prefixWord, tailWord_5871874, baseEnd_5871874] using wordTrace_append hprefix tailTrace_5871874
  have hstable : (prefixWord ++ tailWord_5871874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871874).length < 2 ^ (prefixWord ++ tailWord_5871874).sum := by decide
  have hdescent : baseEnd_5871874 < baseStart_5871874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871881 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 4, 2, 2]
def baseStart_5871881 : Nat := 118140960795 + 5871881 * 2 ^ 59
def prefixEnd_5871881 : Nat := 4983230072969 + 3 ^ 40 * 5871881 * 2
def baseEnd_5871881 : Nat := 3015097299003245972283217

theorem tailTrace_5871881 : CollatzResearch.WordTrace tailWord_5871881 prefixEnd_5871881 3015097299003245972283217 := by
  unfold tailWord_5871881
  simp only [CollatzResearch.WordTrace]
  refine ⟨214165094440185449279943497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142776729626790299519962331 214165094440185449279943497)
  ·
    refine ⟨160623820830139086959957623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214165094440185449279943497 160623820830139086959957623)
    ·
      refine ⟨240935731245208630439936435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160623820830139086959957623 240935731245208630439936435)
      ·
        refine ⟨361403596867812945659904653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240935731245208630439936435 361403596867812945659904653)
        ·
          refine ⟨135526348825429854622464245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361403596867812945659904653 135526348825429854622464245)
          ·
            refine ⟨12705595202384048870856023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135526348825429854622464245 12705595202384048870856023)
            ·
              refine ⟨19058392803576073306284035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12705595202384048870856023 19058392803576073306284035)
              ·
                refine ⟨28587589205364109959426053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19058392803576073306284035 28587589205364109959426053)
                ·
                  refine ⟨5360172976005770617392385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28587589205364109959426053 5360172976005770617392385)
                  ·
                    refine ⟨4020129732004327963044289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5360172976005770617392385 4020129732004327963044289)
                    ·
                      refine ⟨3015097299003245972283217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020129732004327963044289 3015097299003245972283217)
                      ·
                        rfl

theorem cell23_5871881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 2, 2].length) (baseStart_5871881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871881 prefixEnd_5871881 := by exact prefixLift 5871881
  have htrace : WordTrace (prefixWord ++ tailWord_5871881) baseStart_5871881 baseEnd_5871881 := by
    simpa [prefixWord, tailWord_5871881, baseEnd_5871881] using wordTrace_append hprefix tailTrace_5871881
  have hstable : (prefixWord ++ tailWord_5871881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871881).length < 2 ^ (prefixWord ++ tailWord_5871881).sum := by decide
  have hdescent : baseEnd_5871881 < baseStart_5871881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871898 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2]
def baseStart_5871898 : Nat := 118140960795 + 5871898 * 2 ^ 59
def prefixEnd_5871898 : Nat := 4983230072969 + 3 ^ 40 * 5871898 * 2
def baseEnd_5871898 : Nat := 3015106028174372405770639

theorem tailTrace_5871898 : CollatzResearch.WordTrace tailWord_5871898 prefixEnd_5871898 3015106028174372405770639 := by
  unfold tailWord_5871898
  simp only [CollatzResearch.WordTrace]
  refine ⟨53541428620280965295828087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142777142987415907455541565 53541428620280965295828087)
  ·
    refine ⟨80312142930421447943742131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53541428620280965295828087 80312142930421447943742131)
    ·
      refine ⟨120468214395632171915613197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80312142930421447943742131 120468214395632171915613197)
      ·
        refine ⟨45175580398362064468354949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120468214395632171915613197 45175580398362064468354949)
        ·
          refine ⟨8470421324692887087816553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45175580398362064468354949 8470421324692887087816553)
          ·
            refine ⟨6352815993519665315862415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8470421324692887087816553 6352815993519665315862415)
            ·
              refine ⟨9529223990279497973793623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352815993519665315862415 9529223990279497973793623)
              ·
                refine ⟨14293835985419246960690435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529223990279497973793623 14293835985419246960690435)
                ·
                  refine ⟨21440753978128870441035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14293835985419246960690435 21440753978128870441035653)
                  ·
                    refine ⟨4020141370899163207694185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21440753978128870441035653 4020141370899163207694185)
                    ·
                      refine ⟨3015106028174372405770639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020141370899163207694185 3015106028174372405770639)
                      ·
                        rfl

theorem cell23_5871898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_5871898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871898 prefixEnd_5871898 := by exact prefixLift 5871898
  have htrace : WordTrace (prefixWord ++ tailWord_5871898) baseStart_5871898 baseEnd_5871898 := by
    simpa [prefixWord, tailWord_5871898, baseEnd_5871898] using wordTrace_append hprefix tailTrace_5871898
  have hstable : (prefixWord ++ tailWord_5871898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871898).length < 2 ^ (prefixWord ++ tailWord_5871898).sum := by decide
  have hdescent : baseEnd_5871898 < baseStart_5871898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871934 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5871934 : Nat := 118140960795 + 5871934 * 2 ^ 59
def prefixEnd_5871934 : Nat := 4983230072969 + 3 ^ 40 * 5871934 * 2
def baseEnd_5871934 : Nat := 1005041504492644754973491

theorem tailTrace_5871934 : CollatzResearch.WordTrace tailWord_5871934 prefixEnd_5871934 1005041504492644754973491 := by
  unfold tailWord_5871934
  simp only [CollatzResearch.WordTrace]
  refine ⟨26770878438624179916452857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142778018339328959554415237 26770878438624179916452857)
  ·
    refine ⟨20078158828968134937339643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26770878438624179916452857 20078158828968134937339643)
    ·
      refine ⟨30117238243452202406009465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20078158828968134937339643 30117238243452202406009465)
      ·
        refine ⟨22587928682589151804507099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30117238243452202406009465 22587928682589151804507099)
        ·
          refine ⟨33881893023883727706760649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22587928682589151804507099 33881893023883727706760649)
          ·
            refine ⟨25411419767912795780070487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33881893023883727706760649 25411419767912795780070487)
            ·
              refine ⟨38117129651869193670105731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25411419767912795780070487 38117129651869193670105731)
              ·
                refine ⟨57175694477803790505158597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38117129651869193670105731 57175694477803790505158597)
                ·
                  refine ⟨10720442714588210719717237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57175694477803790505158597 10720442714588210719717237)
                  ·
                    refine ⟨1005041504492644754973491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10720442714588210719717237 1005041504492644754973491)
                    ·
                      rfl

theorem cell23_5871934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5871934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871934 prefixEnd_5871934 := by exact prefixLift 5871934
  have htrace : WordTrace (prefixWord ++ tailWord_5871934) baseStart_5871934 baseEnd_5871934 := by
    simpa [prefixWord, tailWord_5871934, baseEnd_5871934] using wordTrace_append hprefix tailTrace_5871934
  have hstable : (prefixWord ++ tailWord_5871934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871934).length < 2 ^ (prefixWord ++ tailWord_5871934).sum := by decide
  have hdescent : baseEnd_5871934 < baseStart_5871934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5871967 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_5871967 : Nat := 118140960795 + 5871967 * 2 ^ 59
def prefixEnd_5871967 : Nat := 4983230072969 + 3 ^ 40 * 5871967 * 2
def baseEnd_5871967 : Nat := 3015141458339532635807821

theorem tailTrace_5871967 : CollatzResearch.WordTrace tailWord_5871967 prefixEnd_5871967 3015141458339532635807821 := by
  unfold tailWord_5871967
  simp only [CollatzResearch.WordTrace]
  refine ⟨214168231117873885967574155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142778820745249257311716103 214168231117873885967574155)
  ·
    refine ⟨321252346676810828951361233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214168231117873885967574155 321252346676810828951361233)
    ·
      refine ⟨240939260007608121713520925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321252346676810828951361233 240939260007608121713520925)
      ·
        refine ⟨90352222502853045642570347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240939260007608121713520925 90352222502853045642570347)
        ·
          refine ⟨135528333754279568463855521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90352222502853045642570347 135528333754279568463855521)
          ·
            refine ⟨101646250315709676347891641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135528333754279568463855521 101646250315709676347891641)
            ·
              refine ⟨76234687736782257260918731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101646250315709676347891641 76234687736782257260918731)
              ·
                refine ⟨114352031605173385891378097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76234687736782257260918731 114352031605173385891378097)
                ·
                  refine ⟨85764023703880039418533573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114352031605173385891378097 85764023703880039418533573)
                  ·
                    refine ⟨16080754444477507390975045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85764023703880039418533573 16080754444477507390975045)
                    ·
                      refine ⟨3015141458339532635807821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16080754444477507390975045 3015141458339532635807821)
                      ·
                        rfl

theorem cell23_5871967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_5871967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5871967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5871967 prefixEnd_5871967 := by exact prefixLift 5871967
  have htrace : WordTrace (prefixWord ++ tailWord_5871967) baseStart_5871967 baseEnd_5871967 := by
    simpa [prefixWord, tailWord_5871967, baseEnd_5871967] using wordTrace_append hprefix tailTrace_5871967
  have hstable : (prefixWord ++ tailWord_5871967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5871967).length < 2 ^ (prefixWord ++ tailWord_5871967).sum := by decide
  have hdescent : baseEnd_5871967 < baseStart_5871967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5871967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872031 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 1, 5, 2]
def baseStart_5872031 : Nat := 118140960795 + 5872031 * 2 ^ 59
def prefixEnd_5872031 : Nat := 4983230072969 + 3 ^ 40 * 5872031 * 2
def baseEnd_5872031 : Nat := 3015174321101420385407527

theorem tailTrace_5872031 : CollatzResearch.WordTrace tailWord_5872031 prefixEnd_5872031 3015174321101420385407527 := by
  unfold tailWord_5872031
  simp only [CollatzResearch.WordTrace]
  refine ⟨214170565389642024897903947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142780376926428016598602631 214170565389642024897903947)
  ·
    refine ⟨321255848084463037346855921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214170565389642024897903947 321255848084463037346855921)
    ·
      refine ⟨240941886063347278010141941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321255848084463037346855921 240941886063347278010141941)
      ·
        refine ⟨22588301818438807313450807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240941886063347278010141941 22588301818438807313450807)
        ·
          refine ⟨33882452727658210970176211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22588301818438807313450807 33882452727658210970176211)
          ·
            refine ⟨50823679091487316455264317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33882452727658210970176211 50823679091487316455264317)
            ·
              refine ⟨19058879659307743670724119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50823679091487316455264317 19058879659307743670724119)
              ·
                refine ⟨28588319488961615506086179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19058879659307743670724119 28588319488961615506086179)
                ·
                  refine ⟨42882479233442423259129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28588319488961615506086179 42882479233442423259129269)
                  ·
                    refine ⟨4020232428135227180543369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42882479233442423259129269 4020232428135227180543369)
                    ·
                      refine ⟨3015174321101420385407527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020232428135227180543369 3015174321101420385407527)
                      ·
                        rfl

theorem cell23_5872031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_5872031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872031 prefixEnd_5872031 := by exact prefixLift 5872031
  have htrace : WordTrace (prefixWord ++ tailWord_5872031) baseStart_5872031 baseEnd_5872031 := by
    simpa [prefixWord, tailWord_5872031, baseEnd_5872031] using wordTrace_append hprefix tailTrace_5872031
  have hstable : (prefixWord ++ tailWord_5872031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872031).length < 2 ^ (prefixWord ++ tailWord_5872031).sum := by decide
  have hdescent : baseEnd_5872031 < baseStart_5872031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872045 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 6]
def baseStart_5872045 : Nat := 118140960795 + 5872045 * 2 ^ 59
def prefixEnd_5872045 : Nat := 4983230072969 + 3 ^ 40 * 5872045 * 2
def baseEnd_5872045 : Nat := 335020167758953703403607

theorem tailTrace_5872045 : CollatzResearch.WordTrace tailWord_5872045 prefixEnd_5872045 335020167758953703403607 := by
  unfold tailWord_5872045
  simp only [CollatzResearch.WordTrace]
  refine ⟨214171076011591305288913589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142780717341060870192609059 214171076011591305288913589)
  ·
    refine ⟨20078538376086684870835649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214171076011591305288913589 20078538376086684870835649)
    ·
      refine ⟨15058903782065013653126737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20078538376086684870835649 15058903782065013653126737)
      ·
        refine ⟨11294177836548760239845053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15058903782065013653126737 11294177836548760239845053)
        ·
          refine ⟨4235316688705785089941895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11294177836548760239845053 4235316688705785089941895)
          ·
            refine ⟨6352975033058677634912843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235316688705785089941895 6352975033058677634912843)
            ·
              refine ⟨9529462549588016452369265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352975033058677634912843 9529462549588016452369265)
              ·
                refine ⟨7147096912191012339276949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9529462549588016452369265 7147096912191012339276949)
                ·
                  refine ⟨335020167758953703403607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7147096912191012339276949 335020167758953703403607)
                  ·
                    rfl

theorem cell23_5872045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_5872045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872045 prefixEnd_5872045 := by exact prefixLift 5872045
  have htrace : WordTrace (prefixWord ++ tailWord_5872045) baseStart_5872045 baseEnd_5872045 := by
    simpa [prefixWord, tailWord_5872045, baseEnd_5872045] using wordTrace_append hprefix tailTrace_5872045
  have hstable : (prefixWord ++ tailWord_5872045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872045).length < 2 ^ (prefixWord ++ tailWord_5872045).sum := by decide
  have hdescent : baseEnd_5872045 < baseStart_5872045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872067 : List Nat := [1, 1, 1, 3, 1, 1, 3, 12]
def baseStart_5872067 : Nat := 118140960795 + 5872067 * 2 ^ 59
def prefixEnd_5872067 : Nat := 4983230072969 + 3 ^ 40 * 5872067 * 2
def baseEnd_5872067 : Nat := 111673807644628972020643

theorem tailTrace_5872067 : CollatzResearch.WordTrace tailWord_5872067 prefixEnd_5872067 111673807644628972020643 := by
  unfold tailWord_5872067
  simp only [CollatzResearch.WordTrace]
  refine ⟨214171878417511603046214455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142781252278341068697476303 214171878417511603046214455)
  ·
    refine ⟨321257817626267404569321683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214171878417511603046214455 321257817626267404569321683)
    ·
      refine ⟨481886726439401106853982525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321257817626267404569321683 481886726439401106853982525)
      ·
        refine ⟨180707522414775415070243447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481886726439401106853982525 180707522414775415070243447)
        ·
          refine ⟨271061283622163122605365171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180707522414775415070243447 271061283622163122605365171)
          ·
            refine ⟨406591925433244683908047757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271061283622163122605365171 406591925433244683908047757)
            ·
              refine ⟨152471972037466756465517909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406591925433244683908047757 152471972037466756465517909)
              ·
                refine ⟨111673807644628972020643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 152471972037466756465517909 111673807644628972020643)
                ·
                  rfl

theorem cell23_5872067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 12].length) (baseStart_5872067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872067 prefixEnd_5872067 := by exact prefixLift 5872067
  have htrace : WordTrace (prefixWord ++ tailWord_5872067) baseStart_5872067 baseEnd_5872067 := by
    simpa [prefixWord, tailWord_5872067, baseEnd_5872067] using wordTrace_append hprefix tailTrace_5872067
  have hstable : (prefixWord ++ tailWord_5872067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872067).length < 2 ^ (prefixWord ++ tailWord_5872067).sum := by decide
  have hdescent : baseEnd_5872067 < baseStart_5872067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872071 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 1, 6]
def baseStart_5872071 : Nat := 118140960795 + 5872071 * 2 ^ 59
def prefixEnd_5872071 : Nat := 4983230072969 + 3 ^ 40 * 5872071 * 2
def baseEnd_5872071 : Nat := 1005064953442533409635781

theorem tailTrace_5872071 : CollatzResearch.WordTrace tailWord_5872071 prefixEnd_5872071 1005064953442533409635781 := by
  unfold tailWord_5872071
  simp only [CollatzResearch.WordTrace]
  refine ⟨214172024309497111729360067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142781349539664741152906711 214172024309497111729360067)
  ·
    refine ⟨321258036464245667594040101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214172024309497111729360067 321258036464245667594040101)
    ·
      refine ⟨60235881837046062673882519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321258036464245667594040101 60235881837046062673882519)
      ·
        refine ⟨90353822755569094010823779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60235881837046062673882519 90353822755569094010823779)
        ·
          refine ⟨135530734133353641016235669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90353822755569094010823779 135530734133353641016235669)
          ·
            refine ⟨6353003162500951922636047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135530734133353641016235669 6353003162500951922636047)
            ·
              refine ⟨9529504743751427883954071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353003162500951922636047 9529504743751427883954071)
              ·
                refine ⟨14294257115627141825931107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529504743751427883954071 14294257115627141825931107)
                ·
                  refine ⟨21441385673440712738896661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14294257115627141825931107 21441385673440712738896661)
                  ·
                    refine ⟨1005064953442533409635781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21441385673440712738896661 1005064953442533409635781)
                    ·
                      rfl

theorem cell23_5872071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_5872071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872071 prefixEnd_5872071 := by exact prefixLift 5872071
  have htrace : WordTrace (prefixWord ++ tailWord_5872071) baseStart_5872071 baseEnd_5872071 := by
    simpa [prefixWord, tailWord_5872071, baseEnd_5872071] using wordTrace_append hprefix tailTrace_5872071
  have hstable : (prefixWord ++ tailWord_5872071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872071).length < 2 ^ (prefixWord ++ tailWord_5872071).sum := by decide
  have hdescent : baseEnd_5872071 < baseStart_5872071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872074 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_5872074 : Nat := 118140960795 + 5872074 * 2 ^ 59
def prefixEnd_5872074 : Nat := 4983230072969 + 3 ^ 40 * 5872074 * 2
def baseEnd_5872074 : Nat := 3015196400769563717169829

theorem tailTrace_5872074 : CollatzResearch.WordTrace tailWord_5872074 prefixEnd_5872074 3015196400769563717169829 := by
  unfold tailWord_5872074
  simp only [CollatzResearch.WordTrace]
  refine ⟨53543033432121560810429819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142781422485657495494479517 53543033432121560810429819)
  ·
    refine ⟨80314550148182341215644729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53543033432121560810429819 80314550148182341215644729)
    ·
      refine ⟨60235912611136755911733547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80314550148182341215644729 60235912611136755911733547)
      ·
        refine ⟨90353868916705133867600321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60235912611136755911733547 90353868916705133867600321)
        ·
          refine ⟨67765401687528850400700241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90353868916705133867600321 67765401687528850400700241)
          ·
            refine ⟨50824051265646637800525181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67765401687528850400700241 50824051265646637800525181)
            ·
              refine ⟨19059019224617489175196943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50824051265646637800525181 19059019224617489175196943)
              ·
                refine ⟨28588528836926233762795415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19059019224617489175196943 28588528836926233762795415)
                ·
                  refine ⟨42882793255389350644193123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28588528836926233762795415 42882793255389350644193123)
                  ·
                    refine ⟨64324189883084025966289685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42882793255389350644193123 64324189883084025966289685)
                    ·
                      refine ⟨3015196400769563717169829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64324189883084025966289685 3015196400769563717169829)
                      ·
                        rfl

theorem cell23_5872074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_5872074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872074 prefixEnd_5872074 := by exact prefixLift 5872074
  have htrace : WordTrace (prefixWord ++ tailWord_5872074) baseStart_5872074 baseEnd_5872074 := by
    simpa [prefixWord, tailWord_5872074, baseEnd_5872074] using wordTrace_append hprefix tailTrace_5872074
  have hstable : (prefixWord ++ tailWord_5872074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872074).length < 2 ^ (prefixWord ++ tailWord_5872074).sum := by decide
  have hdescent : baseEnd_5872074 < baseStart_5872074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872101 : List Nat := [1, 3, 1, 5, 2, 2, 9]
def baseStart_5872101 : Nat := 118140960795 + 5872101 * 2 ^ 59
def prefixEnd_5872101 : Nat := 4983230072969 + 3 ^ 40 * 5872101 * 2
def baseEnd_5872101 : Nat := 37224818083299198907805

theorem tailTrace_5872101 : CollatzResearch.WordTrace tailWord_5872101 prefixEnd_5872101 37224818083299198907805 := by
  unfold tailWord_5872101
  simp only [CollatzResearch.WordTrace]
  refine ⟨214173118499388426852952157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142782078999592284568634771 214173118499388426852952157)
  ·
    refine ⟨80314919437270660069857059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214173118499388426852952157 80314919437270660069857059)
    ·
      refine ⟨120472379155905990104785589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80314919437270660069857059 120472379155905990104785589)
      ·
        refine ⟨11294285545866186572323649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120472379155905990104785589 11294285545866186572323649)
        ·
          refine ⟨8470714159399639929242737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11294285545866186572323649 8470714159399639929242737)
          ·
            refine ⟨6353035619549729946932053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8470714159399639929242737 6353035619549729946932053)
            ·
              refine ⟨37224818083299198907805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6353035619549729946932053 37224818083299198907805)
              ·
                rfl

theorem cell23_5872101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 9].length) (baseStart_5872101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872101 prefixEnd_5872101 := by exact prefixLift 5872101
  have htrace : WordTrace (prefixWord ++ tailWord_5872101) baseStart_5872101 baseEnd_5872101 := by
    simpa [prefixWord, tailWord_5872101, baseEnd_5872101] using wordTrace_append hprefix tailTrace_5872101
  have hstable : (prefixWord ++ tailWord_5872101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872101).length < 2 ^ (prefixWord ++ tailWord_5872101).sum := by decide
  have hdescent : baseEnd_5872101 < baseStart_5872101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872112 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 1, 2, 2]
def baseStart_5872112 : Nat := 118140960795 + 5872112 * 2 ^ 59
def prefixEnd_5872112 : Nat := 4983230072969 + 3 ^ 40 * 5872112 * 2
def baseEnd_5872112 : Nat := 3015215913034434568494655

theorem tailTrace_5872112 : CollatzResearch.WordTrace tailWord_5872112 prefixEnd_5872112 3015215913034434568494655 := by
  unfold tailWord_5872112
  simp only [CollatzResearch.WordTrace]
  refine ⟨107086759851174287865801295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142782346468232383821068393 107086759851174287865801295)
  ·
    refine ⟨160630139776761431798701943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107086759851174287865801295 160630139776761431798701943)
    ·
      refine ⟨240945209665142147698052915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160630139776761431798701943 240945209665142147698052915)
      ·
        refine ⟨361417814497713221547079373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240945209665142147698052915 361417814497713221547079373)
        ·
          refine ⟨135531680436642458080154765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361417814497713221547079373 135531680436642458080154765)
          ·
            refine ⟨50824380163740921780058037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135531680436642458080154765 50824380163740921780058037)
            ·
              refine ⟨4764785640350711416880441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50824380163740921780058037 4764785640350711416880441)
              ·
                refine ⟨3573589230263033562660331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764785640350711416880441 3573589230263033562660331)
                ·
                  refine ⟨5360383845394550343990497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573589230263033562660331 5360383845394550343990497)
                  ·
                    refine ⟨4020287884045912757992873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5360383845394550343990497 4020287884045912757992873)
                    ·
                      refine ⟨3015215913034434568494655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020287884045912757992873 3015215913034434568494655)
                      ·
                        rfl

theorem cell23_5872112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 2, 2].length) (baseStart_5872112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872112 prefixEnd_5872112 := by exact prefixLift 5872112
  have htrace : WordTrace (prefixWord ++ tailWord_5872112) baseStart_5872112 baseEnd_5872112 := by
    simpa [prefixWord, tailWord_5872112, baseEnd_5872112] using wordTrace_append hprefix tailTrace_5872112
  have hstable : (prefixWord ++ tailWord_5872112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872112).length < 2 ^ (prefixWord ++ tailWord_5872112).sum := by decide
  have hdescent : baseEnd_5872112 < baseStart_5872112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872138 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_5872138 : Nat := 118140960795 + 5872138 * 2 ^ 59
def prefixEnd_5872138 : Nat := 4983230072969 + 3 ^ 40 * 5872138 * 2
def baseEnd_5872138 : Nat := 3015229263531451466769535

theorem tailTrace_5872138 : CollatzResearch.WordTrace tailWord_5872138 prefixEnd_5872138 3015229263531451466769535 := by
  unfold tailWord_5872138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53543617000063595543012267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142782978666836254781366045 53543617000063595543012267)
  ·
    refine ⟨80315425500095393314518401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53543617000063595543012267 80315425500095393314518401)
    ·
      refine ⟨60236569125071544985888801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80315425500095393314518401 60236569125071544985888801)
      ·
        refine ⟨45177426843803658739416601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60236569125071544985888801 45177426843803658739416601)
        ·
          refine ⟨33883070132852744054562451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45177426843803658739416601 33883070132852744054562451)
          ·
            refine ⟨50824605199279116081843677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33883070132852744054562451 50824605199279116081843677)
            ·
              refine ⟨19059226949729668530691379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50824605199279116081843677 19059226949729668530691379)
              ·
                refine ⟨28588840424594502796037069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19059226949729668530691379 28588840424594502796037069)
                ·
                  refine ⟨10720815159222938548513901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28588840424594502796037069 10720815159222938548513901)
                  ·
                    refine ⟨4020305684708601955692713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10720815159222938548513901 4020305684708601955692713)
                    ·
                      refine ⟨3015229263531451466769535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020305684708601955692713 3015229263531451466769535)
                      ·
                        rfl

theorem cell23_5872138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_5872138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872138 prefixEnd_5872138 := by exact prefixLift 5872138
  have htrace : WordTrace (prefixWord ++ tailWord_5872138) baseStart_5872138 baseEnd_5872138 := by
    simpa [prefixWord, tailWord_5872138, baseEnd_5872138] using wordTrace_append hprefix tailTrace_5872138
  have hstable : (prefixWord ++ tailWord_5872138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872138).length < 2 ^ (prefixWord ++ tailWord_5872138).sum := by decide
  have hdescent : baseEnd_5872138 < baseStart_5872138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872181 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_5872181 : Nat := 118140960795 + 5872181 * 2 ^ 59
def prefixEnd_5872181 : Nat := 4983230072969 + 3 ^ 40 * 5872181 * 2
def baseEnd_5872181 : Nat := 3015251343199594798531837

theorem tailTrace_5872181 : CollatzResearch.WordTrace tailWord_5872181 prefixEnd_5872181 3015251343199594798531837 := by
  unfold tailWord_5872181
  simp only [CollatzResearch.WordTrace]
  refine ⟨214176036339098600515864397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142784024226065733677242931 214176036339098600515864397)
  ·
    refine ⟨80316013627161975193449149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214176036339098600515864397 80316013627161975193449149)
    ·
      refine ⟨30118505110185740697543431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80316013627161975193449149 30118505110185740697543431)
      ·
        refine ⟨45177757665278611046315147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30118505110185740697543431 45177757665278611046315147)
        ·
          refine ⟨67766636497917916569472721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45177757665278611046315147 67766636497917916569472721)
          ·
            refine ⟨50824977373438437427104541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67766636497917916569472721 50824977373438437427104541)
            ·
              refine ⟨19059366515039414035164203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50824977373438437427104541 19059366515039414035164203)
              ·
                refine ⟨28589049772559121052746305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19059366515039414035164203 28589049772559121052746305)
                ·
                  refine ⟨21441787329419340789559729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28589049772559121052746305 21441787329419340789559729)
                  ·
                    refine ⟨16081340497064505592169797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21441787329419340789559729 16081340497064505592169797)
                    ·
                      refine ⟨3015251343199594798531837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16081340497064505592169797 3015251343199594798531837)
                      ·
                        rfl

theorem cell23_5872181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_5872181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872181 prefixEnd_5872181 := by exact prefixLift 5872181
  have htrace : WordTrace (prefixWord ++ tailWord_5872181) baseStart_5872181 baseEnd_5872181 := by
    simpa [prefixWord, tailWord_5872181, baseEnd_5872181] using wordTrace_append hprefix tailTrace_5872181
  have hstable : (prefixWord ++ tailWord_5872181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872181).length < 2 ^ (prefixWord ++ tailWord_5872181).sum := by decide
  have hdescent : baseEnd_5872181 < baseStart_5872181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872185 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5872185 : Nat := 118140960795 + 5872185 * 2 ^ 59
def prefixEnd_5872185 : Nat := 4983230072969 + 3 ^ 40 * 5872185 * 2
def baseEnd_5872185 : Nat := 3015253397122212782881819

theorem tailTrace_5872185 : CollatzResearch.WordTrace tailWord_5872185 prefixEnd_5872185 3015253397122212782881819 := by
  unfold tailWord_5872185
  simp only [CollatzResearch.WordTrace]
  refine ⟨214176182231084109199010009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142784121487389406132673339 214176182231084109199010009)
  ·
    refine ⟨160632136673313081899257507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214176182231084109199010009 160632136673313081899257507)
    ·
      refine ⟨240948205009969622848886261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160632136673313081899257507 240948205009969622848886261)
      ·
        refine ⟨22588894219684652142083087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240948205009969622848886261 22588894219684652142083087)
        ·
          refine ⟨33883341329526978213124631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22588894219684652142083087 33883341329526978213124631)
          ·
            refine ⟨50825011994290467319686947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33883341329526978213124631 50825011994290467319686947)
            ·
              refine ⟨76237517991435700979530421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50825011994290467319686947 76237517991435700979530421)
              ·
                refine ⟨7147267311697096966830977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76237517991435700979530421 7147267311697096966830977)
                ·
                  refine ⟨5360450483772822725123233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7147267311697096966830977 5360450483772822725123233)
                  ·
                    refine ⟨4020337862829617043842425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5360450483772822725123233 4020337862829617043842425)
                    ·
                      refine ⟨3015253397122212782881819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020337862829617043842425 3015253397122212782881819)
                      ·
                        rfl

theorem cell23_5872185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5872185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872185 prefixEnd_5872185 := by exact prefixLift 5872185
  have htrace : WordTrace (prefixWord ++ tailWord_5872185) baseStart_5872185 baseEnd_5872185 := by
    simpa [prefixWord, tailWord_5872185, baseEnd_5872185] using wordTrace_append hprefix tailTrace_5872185
  have hstable : (prefixWord ++ tailWord_5872185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872185).length < 2 ^ (prefixWord ++ tailWord_5872185).sum := by decide
  have hdescent : baseEnd_5872185 < baseStart_5872185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872251 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 5, 4]
def baseStart_5872251 : Nat := 118140960795 + 5872251 * 2 ^ 59
def prefixEnd_5872251 : Nat := 4983230072969 + 3 ^ 40 * 5872251 * 2
def baseEnd_5872251 : Nat := 1005095762281803174885505

theorem tailTrace_5872251 : CollatzResearch.WordTrace tailWord_5872251 prefixEnd_5872251 1005095762281803174885505 := by
  unfold tailWord_5872251
  simp only [CollatzResearch.WordTrace]
  refine ⟨214178589448845002470912607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142785726299230001647275071 214178589448845002470912607)
  ·
    refine ⟨321267884173267503706368911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214178589448845002470912607 321267884173267503706368911)
    ·
      refine ⟨481901826259901255559553367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321267884173267503706368911 481901826259901255559553367)
      ·
        refine ⟨722852739389851883339330051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481901826259901255559553367 722852739389851883339330051)
        ·
          refine ⟨1084279109084777825008995077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722852739389851883339330051 1084279109084777825008995077)
          ·
            refine ⟨203302332953395842189186577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1084279109084777825008995077 203302332953395842189186577)
            ·
              refine ⟨152476749715046881641889933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203302332953395842189186577 152476749715046881641889933)
              ·
                refine ⟨57178781143142580615708725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152476749715046881641889933 57178781143142580615708725)
                ·
                  refine ⟨5360510732169616932722693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57178781143142580615708725 5360510732169616932722693)
                  ·
                    refine ⟨1005095762281803174885505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360510732169616932722693 1005095762281803174885505)
                    ·
                      rfl

theorem cell23_5872251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 4].length) (baseStart_5872251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872251 prefixEnd_5872251 := by exact prefixLift 5872251
  have htrace : WordTrace (prefixWord ++ tailWord_5872251) baseStart_5872251 baseEnd_5872251 := by
    simpa [prefixWord, tailWord_5872251, baseEnd_5872251] using wordTrace_append hprefix tailTrace_5872251
  have hstable : (prefixWord ++ tailWord_5872251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872251).length < 2 ^ (prefixWord ++ tailWord_5872251).sum := by decide
  have hdescent : baseEnd_5872251 < baseStart_5872251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872281 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 6]
def baseStart_5872281 : Nat := 118140960795 + 5872281 * 2 ^ 59
def prefixEnd_5872281 : Nat := 4983230072969 + 3 ^ 40 * 5872281 * 2
def baseEnd_5872281 : Nat := 335033632362782711920153

theorem tailTrace_5872281 : CollatzResearch.WordTrace tailWord_5872281 prefixEnd_5872281 335033632362782711920153 := by
  unfold tailWord_5872281
  simp only [CollatzResearch.WordTrace]
  refine ⟨214179683638736317594504697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142786455759157545063003131 214179683638736317594504697)
  ·
    refine ⟨160634762729052238195878523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214179683638736317594504697 160634762729052238195878523)
    ·
      refine ⟨240952144093578357293817785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160634762729052238195878523 240952144093578357293817785)
      ·
        refine ⟨180714108070183767970363339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240952144093578357293817785 180714108070183767970363339)
        ·
          refine ⟨271071162105275651955545009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180714108070183767970363339 271071162105275651955545009)
          ·
            refine ⟨203303371578956738966658757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271071162105275651955545009 203303371578956738966658757)
            ·
              refine ⟨38119382171054388556248517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203303371578956738966658757 38119382171054388556248517)
              ·
                refine ⟨7147384157072697854296597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38119382171054388556248517 7147384157072697854296597)
                ·
                  refine ⟨335033632362782711920153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7147384157072697854296597 335033632362782711920153)
                  ·
                    rfl

theorem cell23_5872281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_5872281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872281 prefixEnd_5872281 := by exact prefixLift 5872281
  have htrace : WordTrace (prefixWord ++ tailWord_5872281) baseStart_5872281 baseEnd_5872281 := by
    simpa [prefixWord, tailWord_5872281, baseEnd_5872281] using wordTrace_append hprefix tailTrace_5872281
  have hstable : (prefixWord ++ tailWord_5872281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872281).length < 2 ^ (prefixWord ++ tailWord_5872281).sum := by decide
  have hdescent : baseEnd_5872281 < baseStart_5872281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872285 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5872285 : Nat := 118140960795 + 5872285 * 2 ^ 59
def prefixEnd_5872285 : Nat := 4983230072969 + 3 ^ 40 * 5872285 * 2
def baseEnd_5872285 : Nat := 1005101581729220797210453

theorem tailTrace_5872285 : CollatzResearch.WordTrace tailWord_5872285 prefixEnd_5872285 1005101581729220797210453 := by
  unfold tailWord_5872285
  simp only [CollatzResearch.WordTrace]
  refine ⟨214179829530721826277650309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142786553020481217518433539 214179829530721826277650309)
  ·
    refine ⟨40158718037010342427059433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214179829530721826277650309 40158718037010342427059433)
    ·
      refine ⟨30119038527757756820294575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40158718037010342427059433 30119038527757756820294575)
      ·
        refine ⟨45178557791636635230441863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30119038527757756820294575 45178557791636635230441863)
        ·
          refine ⟨67767836687454952845662795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45178557791636635230441863 67767836687454952845662795)
          ·
            refine ⟨101651755031182429268494193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67767836687454952845662795 101651755031182429268494193)
            ·
              refine ⟨76238816273386821951370645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101651755031182429268494193 76238816273386821951370645)
              ·
                refine ⟨3573694512815007278970499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76238816273386821951370645 3573694512815007278970499)
                ·
                  refine ⟨5360541769222510918455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573694512815007278970499 5360541769222510918455749)
                  ·
                    refine ⟨1005101581729220797210453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360541769222510918455749 1005101581729220797210453)
                    ·
                      rfl

theorem cell23_5872285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5872285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872285 prefixEnd_5872285 := by exact prefixLift 5872285
  have htrace : WordTrace (prefixWord ++ tailWord_5872285) baseStart_5872285 baseEnd_5872285 := by
    simpa [prefixWord, tailWord_5872285, baseEnd_5872285] using wordTrace_append hprefix tailTrace_5872285
  have hstable : (prefixWord ++ tailWord_5872285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872285).length < 2 ^ (prefixWord ++ tailWord_5872285).sum := by decide
  have hdescent : baseEnd_5872285 < baseStart_5872285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872291 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 3]
def baseStart_5872291 : Nat := 118140960795 + 5872291 * 2 ^ 59
def prefixEnd_5872291 : Nat := 4983230072969 + 3 ^ 40 * 5872291 * 2
def baseEnd_5872291 : Nat := 3015307826071589368156331

theorem tailTrace_5872291 : CollatzResearch.WordTrace tailWord_5872291 prefixEnd_5872291 3015307826071589368156331 := by
  unfold tailWord_5872291
  simp only [CollatzResearch.WordTrace]
  refine ⟨214180048368700089302368727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142786698912466726201579151 214180048368700089302368727)
  ·
    refine ⟨321270072553050133953553091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214180048368700089302368727 321270072553050133953553091)
    ·
      refine ⟨481905108829575200930329637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321270072553050133953553091 481905108829575200930329637)
      ·
        refine ⟨90357207905545350174436807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 481905108829575200930329637 90357207905545350174436807)
        ·
          refine ⟨135535811858318025261655211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90357207905545350174436807 135535811858318025261655211)
          ·
            refine ⟨203303717787477037892482817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135535811858318025261655211 203303717787477037892482817)
            ·
              refine ⟨152477788340607778419362113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203303717787477037892482817 152477788340607778419362113)
              ·
                refine ⟨114358341255455833814521585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152477788340607778419362113 114358341255455833814521585)
                ·
                  refine ⟨85768755941591875360891189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114358341255455833814521585 85768755941591875360891189)
                  ·
                    refine ⟨8040820869524238315083549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85768755941591875360891189 8040820869524238315083549)
                    ·
                      refine ⟨3015307826071589368156331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8040820869524238315083549 3015307826071589368156331)
                      ·
                        rfl

theorem cell23_5872291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_5872291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872291 prefixEnd_5872291 := by exact prefixLift 5872291
  have htrace : WordTrace (prefixWord ++ tailWord_5872291) baseStart_5872291 baseEnd_5872291 := by
    simpa [prefixWord, tailWord_5872291, baseEnd_5872291] using wordTrace_append hprefix tailTrace_5872291
  have hstable : (prefixWord ++ tailWord_5872291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872291).length < 2 ^ (prefixWord ++ tailWord_5872291).sum := by decide
  have hdescent : baseEnd_5872291 < baseStart_5872291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872361 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_5872361 : Nat := 118140960795 + 5872361 * 2 ^ 59
def prefixEnd_5872361 : Nat := 4983230072969 + 3 ^ 40 * 5872361 * 2
def baseEnd_5872361 : Nat := 3015343769717404094281009

theorem tailTrace_5872361 : CollatzResearch.WordTrace tailWord_5872361 prefixEnd_5872361 3015343769717404094281009 := by
  unfold tailWord_5872361
  simp only [CollatzResearch.WordTrace]
  refine ⟨214182601478446491257416937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142788400985630994171611291 214182601478446491257416937)
  ·
    refine ⟨160636951108834868443062703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214182601478446491257416937 160636951108834868443062703)
    ·
      refine ⟨240955426663252302664594055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160636951108834868443062703 240955426663252302664594055)
      ·
        refine ⟨361433139994878453996891083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240955426663252302664594055 361433139994878453996891083)
        ·
          refine ⟨542149709992317680995336625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361433139994878453996891083 542149709992317680995336625)
          ·
            refine ⟨406612282494238260746502469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542149709992317680995336625 406612282494238260746502469)
            ·
              refine ⟨76239802967669673889969213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406612282494238260746502469 76239802967669673889969213)
              ·
                refine ⟨28589926112876127708738455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76239802967669673889969213 28589926112876127708738455)
                ·
                  refine ⟨42884889169314191563107683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28589926112876127708738455 42884889169314191563107683)
                  ·
                    refine ⟨64327333753971287344661525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42884889169314191563107683 64327333753971287344661525)
                    ·
                      refine ⟨3015343769717404094281009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64327333753971287344661525 3015343769717404094281009)
                      ·
                        rfl

theorem cell23_5872361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_5872361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872361 prefixEnd_5872361 := by exact prefixLift 5872361
  have htrace : WordTrace (prefixWord ++ tailWord_5872361) baseStart_5872361 baseEnd_5872361 := by
    simpa [prefixWord, tailWord_5872361, baseEnd_5872361] using wordTrace_append hprefix tailTrace_5872361
  have hstable : (prefixWord ++ tailWord_5872361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872361).length < 2 ^ (prefixWord ++ tailWord_5872361).sum := by decide
  have hdescent : baseEnd_5872361 < baseStart_5872361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872365 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_5872365 : Nat := 118140960795 + 5872365 * 2 ^ 59
def prefixEnd_5872365 : Nat := 4983230072969 + 3 ^ 40 * 5872365 * 2
def baseEnd_5872365 : Nat := 3015345823640022078630991

theorem tailTrace_5872365 : CollatzResearch.WordTrace tailWord_5872365 prefixEnd_5872365 3015345823640022078630991 := by
  unfold tailWord_5872365
  simp only [CollatzResearch.WordTrace]
  refine ⟨214182747370431999940562549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142788498246954666627041699 214182747370431999940562549)
  ·
    refine ⟨20079632565977999994427739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214182747370431999940562549 20079632565977999994427739)
    ·
      refine ⟨30119448848966999991641609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20079632565977999994427739 30119448848966999991641609)
      ·
        refine ⟨22589586636725249993731207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30119448848966999991641609 22589586636725249993731207)
        ·
          refine ⟨33884379955087874990596811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22589586636725249993731207 33884379955087874990596811)
          ·
            refine ⟨50826569932631812485895217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33884379955087874990596811 50826569932631812485895217)
            ·
              refine ⟨38119927449473859364421413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50826569932631812485895217 38119927449473859364421413)
              ·
                refine ⟨7147486396776348630829015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38119927449473859364421413 7147486396776348630829015)
                ·
                  refine ⟨10721229595164522946243523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147486396776348630829015 10721229595164522946243523)
                  ·
                    refine ⟨16081844392746784419365285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10721229595164522946243523 16081844392746784419365285)
                    ·
                      refine ⟨3015345823640022078630991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16081844392746784419365285 3015345823640022078630991)
                      ·
                        rfl

theorem cell23_5872365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_5872365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872365 prefixEnd_5872365 := by exact prefixLift 5872365
  have htrace : WordTrace (prefixWord ++ tailWord_5872365) baseStart_5872365 baseEnd_5872365 := by
    simpa [prefixWord, tailWord_5872365, baseEnd_5872365] using wordTrace_append hprefix tailTrace_5872365
  have hstable : (prefixWord ++ tailWord_5872365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872365).length < 2 ^ (prefixWord ++ tailWord_5872365).sum := by decide
  have hdescent : baseEnd_5872365 < baseStart_5872365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872368 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_5872368 : Nat := 118140960795 + 5872368 * 2 ^ 59
def prefixEnd_5872368 : Nat := 4983230072969 + 3 ^ 40 * 5872368 * 2
def baseEnd_5872368 : Nat := 3015347364081985566893477

theorem tailTrace_5872368 : CollatzResearch.WordTrace tailWord_5872368 prefixEnd_5872368 3015347364081985566893477 := by
  unfold tailWord_5872368
  simp only [CollatzResearch.WordTrace]
  refine ⟨107091428394710565726460879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142788571192947420968614505 107091428394710565726460879)
  ·
    refine ⟨160637142592065848589691319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107091428394710565726460879 160637142592065848589691319)
    ·
      refine ⟨240955713888098772884536979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160637142592065848589691319 240955713888098772884536979)
      ·
        refine ⟨361433570832148159326805469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240955713888098772884536979 361433570832148159326805469)
        ·
          refine ⟨135537589062055559747552051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361433570832148159326805469 135537589062055559747552051)
          ·
            refine ⟨203306383593083339621328077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135537589062055559747552051 203306383593083339621328077)
            ·
              refine ⟨76239893847406252357998029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203306383593083339621328077 76239893847406252357998029)
              ·
                refine ⟨28589960192777344634249261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76239893847406252357998029 28589960192777344634249261)
                ·
                  refine ⟨10721235072291504237843473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28589960192777344634249261 10721235072291504237843473)
                  ·
                    refine ⟨8040926304218628178382605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10721235072291504237843473 8040926304218628178382605)
                    ·
                      refine ⟨3015347364081985566893477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8040926304218628178382605 3015347364081985566893477)
                      ·
                        rfl

theorem cell23_5872368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_5872368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872368 prefixEnd_5872368 := by exact prefixLift 5872368
  have htrace : WordTrace (prefixWord ++ tailWord_5872368) baseStart_5872368 baseEnd_5872368 := by
    simpa [prefixWord, tailWord_5872368, baseEnd_5872368] using wordTrace_append hprefix tailTrace_5872368
  have hstable : (prefixWord ++ tailWord_5872368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872368).length < 2 ^ (prefixWord ++ tailWord_5872368).sum := by decide
  have hdescent : baseEnd_5872368 < baseStart_5872368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872378 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_5872378 : Nat := 118140960795 + 5872378 * 2 ^ 59
def prefixEnd_5872378 : Nat := 4983230072969 + 3 ^ 40 * 5872378 * 2
def baseEnd_5872378 : Nat := 3015352498888530527768431

theorem tailTrace_5872378 : CollatzResearch.WordTrace tailWord_5872378 prefixEnd_5872378 3015352498888530527768431 := by
  unfold tailWord_5872378
  simp only [CollatzResearch.WordTrace]
  refine ⟨53545805379846225790196447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142788814346256602107190525 53545805379846225790196447)
  ·
    refine ⟨80318708069769338685294671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53545805379846225790196447 80318708069769338685294671)
    ·
      refine ⟨120478062104654008027942007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80318708069769338685294671 120478062104654008027942007)
      ·
        refine ⟨180717093156981012041913011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120478062104654008027942007 180717093156981012041913011)
        ·
          refine ⟨271075639735471518062869517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180717093156981012041913011 271075639735471518062869517)
          ·
            refine ⟨101653364900801819273576069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271075639735471518062869517 101653364900801819273576069)
            ·
              refine ⟨19060005918900341113795513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101653364900801819273576069 19060005918900341113795513)
              ·
                refine ⟨14295004439175255835346635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19060005918900341113795513 14295004439175255835346635)
                ·
                  refine ⟨21442506658762883753019953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14295004439175255835346635 21442506658762883753019953)
                  ·
                    refine ⟨16081879994072162814764965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21442506658762883753019953 16081879994072162814764965)
                    ·
                      refine ⟨3015352498888530527768431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16081879994072162814764965 3015352498888530527768431)
                      ·
                        rfl

theorem cell23_5872378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_5872378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872378 prefixEnd_5872378 := by exact prefixLift 5872378
  have htrace : WordTrace (prefixWord ++ tailWord_5872378) baseStart_5872378 baseEnd_5872378 := by
    simpa [prefixWord, tailWord_5872378, baseEnd_5872378] using wordTrace_append hprefix tailTrace_5872378
  have hstable : (prefixWord ++ tailWord_5872378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872378).length < 2 ^ (prefixWord ++ tailWord_5872378).sum := by decide
  have hdescent : baseEnd_5872378 < baseStart_5872378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872382 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5872382 : Nat := 118140960795 + 5872382 * 2 ^ 59
def prefixEnd_5872382 : Nat := 4983230072969 + 3 ^ 40 * 5872382 * 2
def baseEnd_5872382 : Nat := 3015354552811148512118413

theorem tailTrace_5872382 : CollatzResearch.WordTrace tailWord_5872382 prefixEnd_5872382 3015354552811148512118413 := by
  unfold tailWord_5872382
  simp only [CollatzResearch.WordTrace]
  refine ⟨26772920926421301480491425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142788911607580274562620933 26772920926421301480491425)
  ·
    refine ⟨20079690694815976110368569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26772920926421301480491425 20079690694815976110368569)
    ·
      refine ⟨15059768021111982082776427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20079690694815976110368569 15059768021111982082776427)
      ·
        refine ⟨22589652031667973124164641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15059768021111982082776427 22589652031667973124164641)
        ·
          refine ⟨16942239023750979843123481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22589652031667973124164641 16942239023750979843123481)
          ·
            refine ⟨12706679267813234882342611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16942239023750979843123481 12706679267813234882342611)
            ·
              refine ⟨19060018901719852323513917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12706679267813234882342611 19060018901719852323513917)
              ·
                refine ⟨7147507088144944621317719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19060018901719852323513917 7147507088144944621317719)
                ·
                  refine ⟨10721260632217416931976579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147507088144944621317719 10721260632217416931976579)
                  ·
                    refine ⟨16081890948326125397964869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10721260632217416931976579 16081890948326125397964869)
                    ·
                      refine ⟨3015354552811148512118413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16081890948326125397964869 3015354552811148512118413)
                      ·
                        rfl

theorem cell23_5872382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5872382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872382 prefixEnd_5872382 := by exact prefixLift 5872382
  have htrace : WordTrace (prefixWord ++ tailWord_5872382) baseStart_5872382 baseEnd_5872382 := by
    simpa [prefixWord, tailWord_5872382, baseEnd_5872382] using wordTrace_append hprefix tailTrace_5872382
  have hstable : (prefixWord ++ tailWord_5872382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872382).length < 2 ^ (prefixWord ++ tailWord_5872382).sum := by decide
  have hdescent : baseEnd_5872382 < baseStart_5872382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872392 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 2, 4]
def baseStart_5872392 : Nat := 118140960795 + 5872392 * 2 ^ 59
def prefixEnd_5872392 : Nat := 4983230072969 + 3 ^ 40 * 5872392 * 2
def baseEnd_5872392 : Nat := 1005119895872564490997789

theorem tailTrace_5872392 : CollatzResearch.WordTrace tailWord_5872392 prefixEnd_5872392 1005119895872564490997789 := by
  unfold tailWord_5872392
  simp only [CollatzResearch.WordTrace]
  refine ⟨107091866070667091775897715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142789154760889455701196953 107091866070667091775897715)
  ·
    refine ⟨160637799106000637663846573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107091866070667091775897715 160637799106000637663846573)
    ·
      refine ⟨60239174664750239123942465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160637799106000637663846573 60239174664750239123942465)
      ·
        refine ⟨45179380998562679342956849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60239174664750239123942465 45179380998562679342956849)
        ·
          refine ⟨33884535748922009507217637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45179380998562679342956849 33884535748922009507217637)
          ·
            refine ⟨6353350452922876782603307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33884535748922009507217637 6353350452922876782603307)
            ·
              refine ⟨9530025679384315173904961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353350452922876782603307 9530025679384315173904961)
              ·
                refine ⟨7147519259538236380428721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9530025679384315173904961 7147519259538236380428721)
                ·
                  refine ⟨5360639444653677285321541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7147519259538236380428721 5360639444653677285321541)
                  ·
                    refine ⟨1005119895872564490997789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360639444653677285321541 1005119895872564490997789)
                    ·
                      rfl

theorem cell23_5872392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_5872392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872392 prefixEnd_5872392 := by exact prefixLift 5872392
  have htrace : WordTrace (prefixWord ++ tailWord_5872392) baseStart_5872392 baseEnd_5872392 := by
    simpa [prefixWord, tailWord_5872392, baseEnd_5872392] using wordTrace_append hprefix tailTrace_5872392
  have hstable : (prefixWord ++ tailWord_5872392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872392).length < 2 ^ (prefixWord ++ tailWord_5872392).sum := by decide
  have hdescent : baseEnd_5872392 < baseStart_5872392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872401 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_5872401 : Nat := 118140960795 + 5872401 * 2 ^ 59
def prefixEnd_5872401 : Nat := 4983230072969 + 3 ^ 40 * 5872401 * 2
def baseEnd_5872401 : Nat := 1005121436314527979260275

theorem tailTrace_5872401 : CollatzResearch.WordTrace tailWord_5872401 prefixEnd_5872401 1005121436314527979260275 := by
  unfold tailWord_5872401
  simp only [CollatzResearch.WordTrace]
  refine ⟨214184060398301578088873057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142789373598867718725915371 214184060398301578088873057)
  ·
    refine ⟨160638045298726183566654793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214184060398301578088873057 160638045298726183566654793)
    ·
      refine ⟨120478533974044637674991095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160638045298726183566654793 120478533974044637674991095)
      ·
        refine ⟨180717800961066956512486643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120478533974044637674991095 180717800961066956512486643)
        ·
          refine ⟨271076701441600434768729965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180717800961066956512486643 271076701441600434768729965)
          ·
            refine ⟨101653763040600163038273737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271076701441600434768729965 101653763040600163038273737)
            ·
              refine ⟨76240322280450122278705303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101653763040600163038273737 76240322280450122278705303)
              ·
                refine ⟨114360483420675183418057955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76240322280450122278705303 114360483420675183418057955)
                ·
                  refine ⟨171540725131012775127086933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114360483420675183418057955 171540725131012775127086933)
                  ·
                    refine ⟨1005121436314527979260275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171540725131012775127086933 1005121436314527979260275)
                    ·
                      rfl

theorem cell23_5872401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_5872401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872401 prefixEnd_5872401 := by exact prefixLift 5872401
  have htrace : WordTrace (prefixWord ++ tailWord_5872401) baseStart_5872401 baseEnd_5872401 := by
    simpa [prefixWord, tailWord_5872401, baseEnd_5872401] using wordTrace_append hprefix tailTrace_5872401
  have hstable : (prefixWord ++ tailWord_5872401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872401).length < 2 ^ (prefixWord ++ tailWord_5872401).sum := by decide
  have hdescent : baseEnd_5872401 < baseStart_5872401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872402 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5872402 : Nat := 118140960795 + 5872402 * 2 ^ 59
def prefixEnd_5872402 : Nat := 4983230072969 + 3 ^ 40 * 5872402 * 2
def baseEnd_5872402 : Nat := 3015364822424238433868321

theorem tailTrace_5872402 : CollatzResearch.WordTrace tailWord_5872402 prefixEnd_5872402 3015364822424238433868321 := by
  unfold tailWord_5872402
  simp only [CollatzResearch.WordTrace]
  refine ⟨53546024217824488814914865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142789397914198636839772973 53546024217824488814914865)
  ·
    refine ⟨40159518163368366611186149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53546024217824488814914865 40159518163368366611186149)
    ·
      refine ⟨7529909655631568739597403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40159518163368366611186149 7529909655631568739597403)
      ·
        refine ⟨11294864483447353109396105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529909655631568739597403 11294864483447353109396105)
        ·
          refine ⟨8471148362585514832047079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11294864483447353109396105 8471148362585514832047079)
          ·
            refine ⟨12706722543878272248070619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8471148362585514832047079 12706722543878272248070619)
            ·
              refine ⟨19060083815817408372105929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12706722543878272248070619 19060083815817408372105929)
              ·
                refine ⟨14295062861863056279079447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19060083815817408372105929 14295062861863056279079447)
                ·
                  refine ⟨21442594292794584418619171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14295062861863056279079447 21442594292794584418619171)
                  ·
                    refine ⟨32163891439191876627928757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21442594292794584418619171 32163891439191876627928757)
                    ·
                      refine ⟨3015364822424238433868321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32163891439191876627928757 3015364822424238433868321)
                      ·
                        rfl

theorem cell23_5872402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5872402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872402 prefixEnd_5872402 := by exact prefixLift 5872402
  have htrace : WordTrace (prefixWord ++ tailWord_5872402) baseStart_5872402 baseEnd_5872402 := by
    simpa [prefixWord, tailWord_5872402, baseEnd_5872402] using wordTrace_append hprefix tailTrace_5872402
  have hstable : (prefixWord ++ tailWord_5872402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872402).length < 2 ^ (prefixWord ++ tailWord_5872402).sum := by decide
  have hdescent : baseEnd_5872402 < baseStart_5872402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872411 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_5872411 : Nat := 118140960795 + 5872411 * 2 ^ 59
def prefixEnd_5872411 : Nat := 4983230072969 + 3 ^ 40 * 5872411 * 2
def baseEnd_5872411 : Nat := 3015369443750128898655779

theorem tailTrace_5872411 : CollatzResearch.WordTrace tailWord_5872411 prefixEnd_5872411 3015369443750128898655779 := by
  unfold tailWord_5872411
  simp only [CollatzResearch.WordTrace]
  refine ⟨214184425128265349796737087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142789616752176899864491391 214184425128265349796737087)
  ·
    refine ⟨321276637692398024695105631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214184425128265349796737087 321276637692398024695105631)
    ·
      refine ⟨481914956538597037042658447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321276637692398024695105631 481914956538597037042658447)
      ·
        refine ⟨722872434807895555563987671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481914956538597037042658447 722872434807895555563987671)
        ·
          refine ⟨1084308652211843333345981507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722872434807895555563987671 1084308652211843333345981507)
          ·
            refine ⟨1626462978317765000018972261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084308652211843333345981507 1626462978317765000018972261)
            ·
              refine ⟨304961808434580937503557299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1626462978317765000018972261 304961808434580937503557299)
              ·
                refine ⟨457442712651871406255335949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304961808434580937503557299 457442712651871406255335949)
                ·
                  refine ⟨171541017244451777345750981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457442712651871406255335949 171541017244451777345750981)
                  ·
                    refine ⟨32163940733334708252328309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171541017244451777345750981 32163940733334708252328309)
                    ·
                      refine ⟨3015369443750128898655779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32163940733334708252328309 3015369443750128898655779)
                      ·
                        rfl

theorem cell23_5872411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_5872411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872411 prefixEnd_5872411 := by exact prefixLift 5872411
  have htrace : WordTrace (prefixWord ++ tailWord_5872411) baseStart_5872411 baseEnd_5872411 := by
    simpa [prefixWord, tailWord_5872411, baseEnd_5872411] using wordTrace_append hprefix tailTrace_5872411
  have hstable : (prefixWord ++ tailWord_5872411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872411).length < 2 ^ (prefixWord ++ tailWord_5872411).sum := by decide
  have hdescent : baseEnd_5872411 < baseStart_5872411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872415 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_5872415 : Nat := 118140960795 + 5872415 * 2 ^ 59
def prefixEnd_5872415 : Nat := 4983230072969 + 3 ^ 40 * 5872415 * 2
def baseEnd_5872415 : Nat := 3015371497672746883005761

theorem tailTrace_5872415 : CollatzResearch.WordTrace tailWord_5872415 prefixEnd_5872415 3015371497672746883005761 := by
  unfold tailWord_5872415
  simp only [CollatzResearch.WordTrace]
  refine ⟨214184571020250858479882699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142789714013500572319921799 214184571020250858479882699)
  ·
    refine ⟨321276856530376287719824049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214184571020250858479882699 321276856530376287719824049)
    ·
      refine ⟨240957642397782215789868037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321276856530376287719824049 240957642397782215789868037)
      ·
        refine ⟨45179557949584165460600257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240957642397782215789868037 45179557949584165460600257)
        ·
          refine ⟨33884668462188124095450193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45179557949584165460600257 33884668462188124095450193)
          ·
            refine ⟨25413501346641093071587645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33884668462188124095450193 25413501346641093071587645)
            ·
              refine ⟨9530063004990409901845367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25413501346641093071587645 9530063004990409901845367)
              ·
                refine ⟨14295094507485614852768051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9530063004990409901845367 14295094507485614852768051)
                ·
                  refine ⟨21442641761228422279152077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14295094507485614852768051 21442641761228422279152077)
                  ·
                    refine ⟨8040990660460658354682029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21442641761228422279152077 8040990660460658354682029)
                    ·
                      refine ⟨3015371497672746883005761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8040990660460658354682029 3015371497672746883005761)
                      ·
                        rfl

theorem cell23_5872415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_5872415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872415 prefixEnd_5872415 := by exact prefixLift 5872415
  have htrace : WordTrace (prefixWord ++ tailWord_5872415) baseStart_5872415 baseEnd_5872415 := by
    simpa [prefixWord, tailWord_5872415, baseEnd_5872415] using wordTrace_append hprefix tailTrace_5872415
  have hstable : (prefixWord ++ tailWord_5872415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872415).length < 2 ^ (prefixWord ++ tailWord_5872415).sum := by decide
  have hdescent : baseEnd_5872415 < baseStart_5872415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872476 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5872476 : Nat := 118140960795 + 5872476 * 2 ^ 59
def prefixEnd_5872476 : Nat := 4983230072969 + 3 ^ 40 * 5872476 * 2
def baseEnd_5872476 : Nat := 3015402819992671144342981

theorem tailTrace_5872476 : CollatzResearch.WordTrace tailWord_5872476 prefixEnd_5872476 3015402819992671144342981 := by
  unfold tailWord_5872476
  simp only [CollatzResearch.WordTrace]
  refine ⟨107093397936514932948926641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142791197248686577265235521 107093397936514932948926641)
  ·
    refine ⟨80320048452386199711694981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107093397936514932948926641 80320048452386199711694981)
    ·
      refine ⟨15060009084822412445942809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80320048452386199711694981 15060009084822412445942809)
      ·
        refine ⟨11295006813616809334457107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15060009084822412445942809 11295006813616809334457107)
        ·
          refine ⟨16942510220425214001685661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295006813616809334457107 16942510220425214001685661)
          ·
            refine ⟨6353441332659455250632123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16942510220425214001685661 6353441332659455250632123)
            ·
              refine ⟨9530161998989182875948185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353441332659455250632123 9530161998989182875948185)
              ·
                refine ⟨7147621499241887156961139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9530161998989182875948185 7147621499241887156961139)
                ·
                  refine ⟨10721432248862830735441709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147621499241887156961139 10721432248862830735441709)
                  ·
                    refine ⟨4020537093323561525790641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10721432248862830735441709 4020537093323561525790641)
                    ·
                      refine ⟨3015402819992671144342981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020537093323561525790641 3015402819992671144342981)
                      ·
                        rfl

theorem cell23_5872476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5872476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872476 prefixEnd_5872476 := by exact prefixLift 5872476
  have htrace : WordTrace (prefixWord ++ tailWord_5872476) baseStart_5872476 baseEnd_5872476 := by
    simpa [prefixWord, tailWord_5872476, baseEnd_5872476] using wordTrace_append hprefix tailTrace_5872476
  have hstable : (prefixWord ++ tailWord_5872476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872476).length < 2 ^ (prefixWord ++ tailWord_5872476).sum := by decide
  have hdescent : baseEnd_5872476 < baseStart_5872476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872515 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 7, 2]
def baseStart_5872515 : Nat := 118140960795 + 5872515 * 2 ^ 59
def prefixEnd_5872515 : Nat := 4983230072969 + 3 ^ 40 * 5872515 * 2
def baseEnd_5872515 : Nat := 3015422845738196491755301

theorem tailTrace_5872515 : CollatzResearch.WordTrace tailWord_5872515 prefixEnd_5872515 3015422845738196491755301 := by
  unfold tailWord_5872515
  simp only [CollatzResearch.WordTrace]
  refine ⟨214188218319888575558522999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142792145546592383705681999 214188218319888575558522999)
  ·
    refine ⟨321282327479832863337784499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214188218319888575558522999 321282327479832863337784499)
    ·
      refine ⟨481923491219749295006676749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321282327479832863337784499 481923491219749295006676749)
      ·
        refine ⟨180721309207405985627503781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481923491219749295006676749 180721309207405985627503781)
        ·
          refine ⟨33885245476388622305156959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180721309207405985627503781 33885245476388622305156959)
          ·
            refine ⟨50827868214582933457735439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33885245476388622305156959 50827868214582933457735439)
            ·
              refine ⟨76241802321874400186603159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50827868214582933457735439 76241802321874400186603159)
              ·
                refine ⟨114362703482811600279904739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76241802321874400186603159 114362703482811600279904739)
                ·
                  refine ⟨171544055224217400419857109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114362703482811600279904739 171544055224217400419857109)
                  ·
                    refine ⟨4020563794317595322340401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 171544055224217400419857109 4020563794317595322340401)
                    ·
                      refine ⟨3015422845738196491755301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020563794317595322340401 3015422845738196491755301)
                      ·
                        rfl

theorem cell23_5872515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_5872515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872515 prefixEnd_5872515 := by exact prefixLift 5872515
  have htrace : WordTrace (prefixWord ++ tailWord_5872515) baseStart_5872515 baseEnd_5872515 := by
    simpa [prefixWord, tailWord_5872515, baseEnd_5872515] using wordTrace_append hprefix tailTrace_5872515
  have hstable : (prefixWord ++ tailWord_5872515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872515).length < 2 ^ (prefixWord ++ tailWord_5872515).sum := by decide
  have hdescent : baseEnd_5872515 < baseStart_5872515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872522 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5872522 : Nat := 118140960795 + 5872522 * 2 ^ 59
def prefixEnd_5872522 : Nat := 4983230072969 + 3 ^ 40 * 5872522 * 2
def baseEnd_5872522 : Nat := 3015426440102777964367769

theorem tailTrace_5872522 : CollatzResearch.WordTrace tailWord_5872522 prefixEnd_5872522 3015426440102777964367769 := by
  unfold tailWord_5872522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53547118407715803938506955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142792315753908810502685213 53547118407715803938506955)
  ·
    refine ⟨80320677611573705907760433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53547118407715803938506955 80320677611573705907760433)
    ·
      refine ⟨60240508208680279430820325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80320677611573705907760433 60240508208680279430820325)
      ·
        refine ⟨11295095289127552393278811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60240508208680279430820325 11295095289127552393278811)
        ·
          refine ⟨16942642933691328589918217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295095289127552393278811 16942642933691328589918217)
          ·
            refine ⟨12706982200268496442438663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16942642933691328589918217 12706982200268496442438663)
            ·
              refine ⟨19060473300402744663657995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12706982200268496442438663 19060473300402744663657995)
              ·
                refine ⟨28590709950604116995486993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19060473300402744663657995 28590709950604116995486993)
                ·
                  refine ⟨21443032462953087746615245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28590709950604116995486993 21443032462953087746615245)
                  ·
                    refine ⟨8041137173607407904980717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21443032462953087746615245 8041137173607407904980717)
                    ·
                      refine ⟨3015426440102777964367769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8041137173607407904980717 3015426440102777964367769)
                      ·
                        rfl

theorem cell23_5872522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5872522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872522 prefixEnd_5872522 := by exact prefixLift 5872522
  have htrace : WordTrace (prefixWord ++ tailWord_5872522) baseStart_5872522 baseEnd_5872522 := by
    simpa [prefixWord, tailWord_5872522, baseEnd_5872522] using wordTrace_append hprefix tailTrace_5872522
  have hstable : (prefixWord ++ tailWord_5872522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872522).length < 2 ^ (prefixWord ++ tailWord_5872522).sum := by decide
  have hdescent : baseEnd_5872522 < baseStart_5872522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872532 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5872532 : Nat := 118140960795 + 5872532 * 2 ^ 59
def prefixEnd_5872532 : Nat := 4983230072969 + 3 ^ 40 * 5872532 * 2
def baseEnd_5872532 : Nat := 3015431574909322925242723

theorem tailTrace_5872532 : CollatzResearch.WordTrace tailWord_5872532 prefixEnd_5872532 3015431574909322925242723 := by
  unfold tailWord_5872532
  simp only [CollatzResearch.WordTrace]
  refine ⟨107094419180413493730945925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142792558907217991641261233 107094419180413493730945925)
  ·
    refine ⟨20080203596327530074552361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107094419180413493730945925 20080203596327530074552361)
    ·
      refine ⟨15060152697245647555914271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20080203596327530074552361 15060152697245647555914271)
      ·
        refine ⟨22590229045868471333871407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060152697245647555914271 22590229045868471333871407)
        ·
          refine ⟨33885343568802707000807111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22590229045868471333871407 33885343568802707000807111)
          ·
            refine ⟨50828015353204060501210667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33885343568802707000807111 50828015353204060501210667)
            ·
              refine ⟨76242023029806090751816001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50828015353204060501210667 76242023029806090751816001)
              ·
                refine ⟨57181517272354568063862001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76242023029806090751816001 57181517272354568063862001)
                ·
                  refine ⟨42886137954265926047896501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57181517272354568063862001 42886137954265926047896501)
                  ·
                    refine ⟨4020575433212430566990297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42886137954265926047896501 4020575433212430566990297)
                    ·
                      refine ⟨3015431574909322925242723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020575433212430566990297 3015431574909322925242723)
                      ·
                        rfl

theorem cell23_5872532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5872532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872532 prefixEnd_5872532 := by exact prefixLift 5872532
  have htrace : WordTrace (prefixWord ++ tailWord_5872532) baseStart_5872532 baseEnd_5872532 := by
    simpa [prefixWord, tailWord_5872532, baseEnd_5872532] using wordTrace_append hprefix tailTrace_5872532
  have hstable : (prefixWord ++ tailWord_5872532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872532).length < 2 ^ (prefixWord ++ tailWord_5872532).sum := by decide
  have hdescent : baseEnd_5872532 < baseStart_5872532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872635 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 4]
def baseStart_5872635 : Nat := 118140960795 + 5872635 * 2 ^ 59
def prefixEnd_5872635 : Nat := 4983230072969 + 3 ^ 40 * 5872635 * 2
def baseEnd_5872635 : Nat := 3015484463416736022254749

theorem tailTrace_5872635 : CollatzResearch.WordTrace tailWord_5872635 prefixEnd_5872635 3015484463416736022254749 := by
  unfold tailWord_5872635
  simp only [CollatzResearch.WordTrace]
  refine ⟨214192595079453836052891359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142795063386302557368594239 214192595079453836052891359)
  ·
    refine ⟨321288892619180754079337039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214192595079453836052891359 321288892619180754079337039)
    ·
      refine ⟨481933338928771131119005559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321288892619180754079337039 481933338928771131119005559)
      ·
        refine ⟨722900008393156696678508339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481933338928771131119005559 722900008393156696678508339)
        ·
          refine ⟨1084350012589735045017762509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722900008393156696678508339 1084350012589735045017762509)
          ·
            refine ⟨406631254721150641881660941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084350012589735045017762509 406631254721150641881660941)
            ·
              refine ⟨152486720520431490705622853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406631254721150641881660941 152486720520431490705622853)
              ·
                refine ⟨28591260097580904507304285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152486720520431490705622853 28591260097580904507304285)
                ·
                  refine ⟨10721722536592839190239107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28591260097580904507304285 10721722536592839190239107)
                  ·
                    refine ⟨16082583804889258785358661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10721722536592839190239107 16082583804889258785358661)
                    ·
                      refine ⟨3015484463416736022254749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16082583804889258785358661 3015484463416736022254749)
                      ·
                        rfl

theorem cell23_5872635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 4].length) (baseStart_5872635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872635 prefixEnd_5872635 := by exact prefixLift 5872635
  have htrace : WordTrace (prefixWord ++ tailWord_5872635) baseStart_5872635 baseEnd_5872635 := by
    simpa [prefixWord, tailWord_5872635, baseEnd_5872635] using wordTrace_append hprefix tailTrace_5872635
  have hstable : (prefixWord ++ tailWord_5872635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872635).length < 2 ^ (prefixWord ++ tailWord_5872635).sum := by decide
  have hdescent : baseEnd_5872635 < baseStart_5872635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872645 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_5872645 : Nat := 118140960795 + 5872645 * 2 ^ 59
def prefixEnd_5872645 : Nat := 4983230072969 + 3 ^ 40 * 5872645 * 2
def baseEnd_5872645 : Nat := 1005163199407760327709901

theorem tailTrace_5872645 : CollatzResearch.WordTrace tailWord_5872645 prefixEnd_5872645 1005163199407760327709901 := by
  unfold tailWord_5872645
  simp only [CollatzResearch.WordTrace]
  refine ⟨214192959809417607760755389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142795306539611738507170259 214192959809417607760755389)
  ·
    refine ⟨80322359928531602910283271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214192959809417607760755389 80322359928531602910283271)
    ·
      refine ⟨120483539892797404365424907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80322359928531602910283271 120483539892797404365424907)
      ·
        refine ⟨180725309839196106548137361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120483539892797404365424907 180725309839196106548137361)
        ·
          refine ⟨135543982379397079911103021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180725309839196106548137361 135543982379397079911103021)
          ·
            refine ⟨50828993392273904966663633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135543982379397079911103021 50828993392273904966663633)
            ·
              refine ⟨38121745044205428724997725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50828993392273904966663633 38121745044205428724997725)
              ·
                refine ⟨14295654391577035771874147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38121745044205428724997725 14295654391577035771874147)
                ·
                  refine ⟨21443481587365553657811221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14295654391577035771874147 21443481587365553657811221)
                  ·
                    refine ⟨1005163199407760327709901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21443481587365553657811221 1005163199407760327709901)
                    ·
                      rfl

theorem cell23_5872645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_5872645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872645 prefixEnd_5872645 := by exact prefixLift 5872645
  have htrace : WordTrace (prefixWord ++ tailWord_5872645) baseStart_5872645 baseEnd_5872645 := by
    simpa [prefixWord, tailWord_5872645, baseEnd_5872645] using wordTrace_append hprefix tailTrace_5872645
  have hstable : (prefixWord ++ tailWord_5872645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872645).length < 2 ^ (prefixWord ++ tailWord_5872645).sum := by decide
  have hdescent : baseEnd_5872645 < baseStart_5872645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872652 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_5872652 : Nat := 118140960795 + 5872652 * 2 ^ 59
def prefixEnd_5872652 : Nat := 4983230072969 + 3 ^ 40 * 5872652 * 2
def baseEnd_5872652 : Nat := 3015493192587862455742171

theorem tailTrace_5872652 : CollatzResearch.WordTrace tailWord_5872652 prefixEnd_5872652 3015493192587862455742171 := by
  unfold tailWord_5872652
  simp only [CollatzResearch.WordTrace]
  refine ⟨107096607560196123978130105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142795476746928165304173473 107096607560196123978130105)
  ·
    refine ⟨80322455670147092983597579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107096607560196123978130105 80322455670147092983597579)
    ·
      refine ⟨120483683505220639475396369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80322455670147092983597579 120483683505220639475396369)
      ·
        refine ⟨90362762628915479606547277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120483683505220639475396369 90362762628915479606547277)
        ·
          refine ⟨33886035985843304852455229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90362762628915479606547277 33886035985843304852455229)
          ·
            refine ⟨12707263494691239319670711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33886035985843304852455229 12707263494691239319670711)
            ·
              refine ⟨19060895242036858979506067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707263494691239319670711 19060895242036858979506067)
              ·
                refine ⟨28591342863055288469259101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19060895242036858979506067 28591342863055288469259101)
                ·
                  refine ⟨10721753573645733175972163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28591342863055288469259101 10721753573645733175972163)
                  ·
                    refine ⟨16082630360468599763958245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10721753573645733175972163 16082630360468599763958245)
                    ·
                      refine ⟨3015493192587862455742171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16082630360468599763958245 3015493192587862455742171)
                      ·
                        rfl

theorem cell23_5872652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_5872652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872652 prefixEnd_5872652 := by exact prefixLift 5872652
  have htrace : WordTrace (prefixWord ++ tailWord_5872652) baseStart_5872652 baseEnd_5872652 := by
    simpa [prefixWord, tailWord_5872652, baseEnd_5872652] using wordTrace_append hprefix tailTrace_5872652
  have hstable : (prefixWord ++ tailWord_5872652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872652).length < 2 ^ (prefixWord ++ tailWord_5872652).sum := by decide
  have hdescent : baseEnd_5872652 < baseStart_5872652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872665 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_5872665 : Nat := 118140960795 + 5872665 * 2 ^ 59
def prefixEnd_5872665 : Nat := 4983230072969 + 3 ^ 40 * 5872665 * 2
def baseEnd_5872665 : Nat := 3015499867836370904879611

theorem tailTrace_5872665 : CollatzResearch.WordTrace tailWord_5872665 prefixEnd_5872665 3015499867836370904879611 := by
  unfold tailWord_5872665
  simp only [CollatzResearch.WordTrace]
  refine ⟨214193689269345151176483449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142795792846230100784322299 214193689269345151176483449)
  ·
    refine ⟨160645266952008863382362587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214193689269345151176483449 160645266952008863382362587)
    ·
      refine ⟨240967900428013295073543881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160645266952008863382362587 240967900428013295073543881)
      ·
        refine ⟨180725925321009971305157911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240967900428013295073543881 180725925321009971305157911)
        ·
          refine ⟨271088887981514956957736867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180725925321009971305157911 271088887981514956957736867)
          ·
            refine ⟨406633331972272435436605301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271088887981514956957736867 406633331972272435436605301)
            ·
              refine ⟨38121874872400540822181747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 406633331972272435436605301 38121874872400540822181747)
              ·
                refine ⟨57182812308600811233272621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38121874872400540822181747 57182812308600811233272621)
                ·
                  refine ⟨21443554615725304212477233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57182812308600811233272621 21443554615725304212477233)
                  ·
                    refine ⟨16082665961793978159357925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21443554615725304212477233 16082665961793978159357925)
                    ·
                      refine ⟨3015499867836370904879611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16082665961793978159357925 3015499867836370904879611)
                      ·
                        rfl

theorem cell23_5872665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_5872665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872665 prefixEnd_5872665 := by exact prefixLift 5872665
  have htrace : WordTrace (prefixWord ++ tailWord_5872665) baseStart_5872665 baseEnd_5872665 := by
    simpa [prefixWord, tailWord_5872665, baseEnd_5872665] using wordTrace_append hprefix tailTrace_5872665
  have hstable : (prefixWord ++ tailWord_5872665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872665).length < 2 ^ (prefixWord ++ tailWord_5872665).sum := by decide
  have hdescent : baseEnd_5872665 < baseStart_5872665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872686 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_5872686 : Nat := 118140960795 + 5872686 * 2 ^ 59
def prefixEnd_5872686 : Nat := 4983230072969 + 3 ^ 40 * 5872686 * 2
def baseEnd_5872686 : Nat := 3015510650930115322717015

theorem tailTrace_5872686 : CollatzResearch.WordTrace tailWord_5872686 prefixEnd_5872686 3015510650930115322717015 := by
  unfold tailWord_5872686
  simp only [CollatzResearch.WordTrace]
  refine ⟨26774306900283633970374739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142796303468179381175331941 26774306900283633970374739)
  ·
    refine ⟨40161460350425450955562109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26774306900283633970374739 40161460350425450955562109)
    ·
      refine ⟨15060547631409544108335791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40161460350425450955562109 15060547631409544108335791)
      ·
        refine ⟨22590821447114316162503687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060547631409544108335791 22590821447114316162503687)
        ·
          refine ⟨33886232170671474243755531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22590821447114316162503687 33886232170671474243755531)
          ·
            refine ⟨50829348256007211365633297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33886232170671474243755531 50829348256007211365633297)
            ·
              refine ⟨38122011192005408524224973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50829348256007211365633297 38122011192005408524224973)
              ·
                refine ⟨14295754197002028196584365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38122011192005408524224973 14295754197002028196584365)
                ·
                  refine ⟨5360907823875760573719137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14295754197002028196584365 5360907823875760573719137)
                  ·
                    refine ⟨4020680867906820430289353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5360907823875760573719137 4020680867906820430289353)
                    ·
                      refine ⟨3015510650930115322717015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020680867906820430289353 3015510650930115322717015)
                      ·
                        rfl

theorem cell23_5872686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_5872686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872686 prefixEnd_5872686 := by exact prefixLift 5872686
  have htrace : WordTrace (prefixWord ++ tailWord_5872686) baseStart_5872686 baseEnd_5872686 := by
    simpa [prefixWord, tailWord_5872686, baseEnd_5872686] using wordTrace_append hprefix tailTrace_5872686
  have hstable : (prefixWord ++ tailWord_5872686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872686).length < 2 ^ (prefixWord ++ tailWord_5872686).sum := by decide
  have hdescent : baseEnd_5872686 < baseStart_5872686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872735 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 4, 6]
def baseStart_5872735 : Nat := 118140960795 + 5872735 * 2 ^ 59
def prefixEnd_5872735 : Nat := 4983230072969 + 3 ^ 40 * 5872735 * 2
def baseEnd_5872735 : Nat := 1005178603827395210334763

theorem tailTrace_5872735 : CollatzResearch.WordTrace tailWord_5872735 prefixEnd_5872735 1005178603827395210334763 := by
  unfold tailWord_5872735
  simp only [CollatzResearch.WordTrace]
  refine ⟨214196242379091553131531659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142797494919394368754354439 214196242379091553131531659)
  ·
    refine ⟨321294363568637329697297489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214196242379091553131531659 321294363568637329697297489)
    ·
      refine ⟨240970772676477997272973117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321294363568637329697297489 240970772676477997272973117)
      ·
        refine ⟨90364039753679248977364919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240970772676477997272973117 90364039753679248977364919)
        ·
          refine ⟨135546059630518873466047379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90364039753679248977364919 135546059630518873466047379)
          ·
            refine ⟨203319089445778310199071069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135546059630518873466047379 203319089445778310199071069)
            ·
              refine ⟨76244658542166866324651651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203319089445778310199071069 76244658542166866324651651)
              ·
                refine ⟨114366987813250299486977477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76244658542166866324651651 114366987813250299486977477)
                ·
                  refine ⟨21443810214984431153808277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114366987813250299486977477 21443810214984431153808277)
                  ·
                    refine ⟨1005178603827395210334763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21443810214984431153808277 1005178603827395210334763)
                    ·
                      rfl

theorem cell23_5872735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_5872735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872735 prefixEnd_5872735 := by exact prefixLift 5872735
  have htrace : WordTrace (prefixWord ++ tailWord_5872735) baseStart_5872735 baseEnd_5872735 := by
    simpa [prefixWord, tailWord_5872735, baseEnd_5872735] using wordTrace_append hprefix tailTrace_5872735
  have hstable : (prefixWord ++ tailWord_5872735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872735).length < 2 ^ (prefixWord ++ tailWord_5872735).sum := by decide
  have hdescent : baseEnd_5872735 < baseStart_5872735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872785 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_5872785 : Nat := 118140960795 + 5872785 * 2 ^ 59
def prefixEnd_5872785 : Nat := 4983230072969 + 3 ^ 40 * 5872785 * 2
def baseEnd_5872785 : Nat := 3015561485514910435379059

theorem tailTrace_5872785 : CollatzResearch.WordTrace tailWord_5872785 prefixEnd_5872785 3015561485514910435379059 := by
  unfold tailWord_5872785
  simp only [CollatzResearch.WordTrace]
  refine ⟨214198066028910411670851809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142798710685940274447234539 214198066028910411670851809)
  ·
    refine ⟨160648549521682808753138857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214198066028910411670851809 160648549521682808753138857)
    ·
      refine ⟨120486412141262106564854143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160648549521682808753138857 120486412141262106564854143)
      ·
        refine ⟨180729618211893159847281215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120486412141262106564854143 180729618211893159847281215)
        ·
          refine ⟨271094427317839739770921823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180729618211893159847281215 271094427317839739770921823)
          ·
            refine ⟨406641640976759609656382735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271094427317839739770921823 406641640976759609656382735)
            ·
              refine ⟨609962461465139414484574103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406641640976759609656382735 609962461465139414484574103)
              ·
                refine ⟨914943692197709121726861155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609962461465139414484574103 914943692197709121726861155)
                ·
                  refine ⟨1372415538296563682590291733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 914943692197709121726861155 1372415538296563682590291733)
                  ·
                    refine ⟨64331978357651422621419925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1372415538296563682590291733 64331978357651422621419925)
                    ·
                      refine ⟨3015561485514910435379059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64331978357651422621419925 3015561485514910435379059)
                      ·
                        rfl

theorem cell23_5872785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_5872785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872785 prefixEnd_5872785 := by exact prefixLift 5872785
  have htrace : WordTrace (prefixWord ++ tailWord_5872785) baseStart_5872785 baseEnd_5872785 := by
    simpa [prefixWord, tailWord_5872785, baseEnd_5872785] using wordTrace_append hprefix tailTrace_5872785
  have hstable : (prefixWord ++ tailWord_5872785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872785).length < 2 ^ (prefixWord ++ tailWord_5872785).sum := by decide
  have hdescent : baseEnd_5872785 < baseStart_5872785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872795 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 5, 7]
def baseStart_5872795 : Nat := 118140960795 + 5872795 * 2 ^ 59
def prefixEnd_5872795 : Nat := 4983230072969 + 3 ^ 40 * 5872795 * 2
def baseEnd_5872795 : Nat := 1005188873440485132084671

theorem tailTrace_5872795 : CollatzResearch.WordTrace tailWord_5872795 prefixEnd_5872795 1005188873440485132084671 := by
  unfold tailWord_5872795
  simp only [CollatzResearch.WordTrace]
  refine ⟨214198430758874183378715839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142798953839249455585810559 214198430758874183378715839)
  ·
    refine ⟨321297646138311275068073759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214198430758874183378715839 321297646138311275068073759)
    ·
      refine ⟨481946469207466912602110639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321297646138311275068073759 481946469207466912602110639)
      ·
        refine ⟨722919703811200368903165959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481946469207466912602110639 722919703811200368903165959)
        ·
          refine ⟨1084379555716800553354748939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722919703811200368903165959 1084379555716800553354748939)
          ·
            refine ⟨1626569333575200830032123409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084379555716800553354748939 1626569333575200830032123409)
            ·
              refine ⟨1219927000181400622524092557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626569333575200830032123409 1219927000181400622524092557)
              ·
                refine ⟨457472625068025233446534709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1219927000181400622524092557 457472625068025233446534709)
                ·
                  refine ⟨42888058600127365635612629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457472625068025233446534709 42888058600127365635612629)
                  ·
                    refine ⟨1005188873440485132084671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42888058600127365635612629 1005188873440485132084671)
                    ·
                      rfl

theorem cell23_5872795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_5872795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872795 prefixEnd_5872795 := by exact prefixLift 5872795
  have htrace : WordTrace (prefixWord ++ tailWord_5872795) baseStart_5872795 baseEnd_5872795 := by
    simpa [prefixWord, tailWord_5872795, baseEnd_5872795] using wordTrace_append hprefix tailTrace_5872795
  have hstable : (prefixWord ++ tailWord_5872795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872795).length < 2 ^ (prefixWord ++ tailWord_5872795).sum := by decide
  have hdescent : baseEnd_5872795 < baseStart_5872795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872810 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5872810 : Nat := 118140960795 + 5872810 * 2 ^ 59
def prefixEnd_5872810 : Nat := 4983230072969 + 3 ^ 40 * 5872810 * 2
def baseEnd_5872810 : Nat := 3015574322531272837566445

theorem tailTrace_5872810 : CollatzResearch.WordTrace tailWord_5872810 prefixEnd_5872810 3015574322531272837566445 := by
  unfold tailWord_5872810
  simp only [CollatzResearch.WordTrace]
  refine ⟨53549744463454960235127971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142799318569213227293674589 53549744463454960235127971)
  ·
    refine ⟨80324616695182440352691957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53549744463454960235127971 80324616695182440352691957)
    ·
      refine ⟨7530432815173353783064871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80324616695182440352691957 7530432815173353783064871)
      ·
        refine ⟨11295649222760030674597307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7530432815173353783064871 11295649222760030674597307)
        ·
          refine ⟨16943473834140046011895961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295649222760030674597307 16943473834140046011895961)
          ·
            refine ⟨12707605375605034508921971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16943473834140046011895961 12707605375605034508921971)
            ·
              refine ⟨19061408063407551763382957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707605375605034508921971 19061408063407551763382957)
              ·
                refine ⟨7148028023777831911268609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19061408063407551763382957 7148028023777831911268609)
                ·
                  refine ⟨5361021017833373933451457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7148028023777831911268609 5361021017833373933451457)
                  ·
                    refine ⟨4020765763375030450088593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361021017833373933451457 4020765763375030450088593)
                    ·
                      refine ⟨3015574322531272837566445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020765763375030450088593 3015574322531272837566445)
                      ·
                        rfl

theorem cell23_5872810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5872810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872810 prefixEnd_5872810 := by exact prefixLift 5872810
  have htrace : WordTrace (prefixWord ++ tailWord_5872810) baseStart_5872810 baseEnd_5872810 := by
    simpa [prefixWord, tailWord_5872810, baseEnd_5872810] using wordTrace_append hprefix tailTrace_5872810
  have hstable : (prefixWord ++ tailWord_5872810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872810).length < 2 ^ (prefixWord ++ tailWord_5872810).sum := by decide
  have hdescent : baseEnd_5872810 < baseStart_5872810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872849 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 2, 4, 2]
def baseStart_5872849 : Nat := 118140960795 + 5872849 * 2 ^ 59
def prefixEnd_5872849 : Nat := 4983230072969 + 3 ^ 40 * 5872849 * 2
def baseEnd_5872849 : Nat := 3015594348276798184978765

theorem tailTrace_5872849 : CollatzResearch.WordTrace tailWord_5872849 prefixEnd_5872849 3015594348276798184978765 := by
  unfold tailWord_5872849
  simp only [CollatzResearch.WordTrace]
  refine ⟨214200400300678550601181601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142800266867119033734121067 214200400300678550601181601)
  ·
    refine ⟨160650300225508912950886201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214200400300678550601181601 160650300225508912950886201)
    ·
      refine ⟨120487725169131684713164651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160650300225508912950886201 120487725169131684713164651)
      ·
        refine ⟨180731587753697527069746977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120487725169131684713164651 180731587753697527069746977)
        ·
          refine ⟨135548690815273145302310233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180731587753697527069746977 135548690815273145302310233)
          ·
            refine ⟨101661518111454858976732675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135548690815273145302310233 101661518111454858976732675)
            ·
              refine ⟨152492277167182288465099013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101661518111454858976732675 152492277167182288465099013)
              ·
                refine ⟨28592301968846679087206065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152492277167182288465099013 28592301968846679087206065)
                ·
                  refine ⟨21444226476635009315404549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28592301968846679087206065 21444226476635009315404549)
                  ·
                    refine ⟨4020792464369064246638353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21444226476635009315404549 4020792464369064246638353)
                    ·
                      refine ⟨3015594348276798184978765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020792464369064246638353 3015594348276798184978765)
                      ·
                        rfl

theorem cell23_5872849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_5872849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872849 prefixEnd_5872849 := by exact prefixLift 5872849
  have htrace : WordTrace (prefixWord ++ tailWord_5872849) baseStart_5872849 baseEnd_5872849 := by
    simpa [prefixWord, tailWord_5872849, baseEnd_5872849] using wordTrace_append hprefix tailTrace_5872849
  have hstable : (prefixWord ++ tailWord_5872849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872849).length < 2 ^ (prefixWord ++ tailWord_5872849).sum := by decide
  have hdescent : baseEnd_5872849 < baseStart_5872849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872936 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5872936 : Nat := 118140960795 + 5872936 * 2 ^ 59
def prefixEnd_5872936 : Nat := 4983230072969 + 3 ^ 40 * 5872936 * 2
def baseEnd_5872936 : Nat := 1005213007031246448196955

theorem tailTrace_5872936 : CollatzResearch.WordTrace tailWord_5872936 prefixEnd_5872936 1005213007031246448196955 := by
  unfold tailWord_5872936
  simp only [CollatzResearch.WordTrace]
  refine ⟨107101786725681682229799331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142802382300908909639732441 107101786725681682229799331)
  ·
    refine ⟨160652680088522523344698997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107101786725681682229799331 160652680088522523344698997)
    ·
      refine ⟨15061188758298986563565531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160652680088522523344698997 15061188758298986563565531)
      ·
        refine ⟨22591783137448479845348297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15061188758298986563565531 22591783137448479845348297)
        ·
          refine ⟨16943837353086359884011223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22591783137448479845348297 16943837353086359884011223)
          ·
            refine ⟨25415756029629539826016835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16943837353086359884011223 25415756029629539826016835)
            ·
              refine ⟨38123634044444309739025253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25415756029629539826016835 38123634044444309739025253)
              ·
                refine ⟨7148181383333308076067235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38123634044444309739025253 7148181383333308076067235)
                ·
                  refine ⟨10722272074999962114100853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7148181383333308076067235 10722272074999962114100853)
                  ·
                    refine ⟨1005213007031246448196955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10722272074999962114100853 1005213007031246448196955)
                    ·
                      rfl

theorem cell23_5872936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5872936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872936 prefixEnd_5872936 := by exact prefixLift 5872936
  have htrace : WordTrace (prefixWord ++ tailWord_5872936) baseStart_5872936 baseEnd_5872936 := by
    simpa [prefixWord, tailWord_5872936, baseEnd_5872936] using wordTrace_append hprefix tailTrace_5872936
  have hstable : (prefixWord ++ tailWord_5872936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872936).length < 2 ^ (prefixWord ++ tailWord_5872936).sum := by decide
  have hdescent : baseEnd_5872936 < baseStart_5872936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872956 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_5872956 : Nat := 118140960795 + 5872956 * 2 ^ 59
def prefixEnd_5872956 : Nat := 4983230072969 + 3 ^ 40 * 5872956 * 2
def baseEnd_5872956 : Nat := 3015649290706829266340773

theorem tailTrace_5872956 : CollatzResearch.WordTrace tailWord_5872956 prefixEnd_5872956 3015649290706829266340773 := by
  unfold tailWord_5872956
  simp only [CollatzResearch.WordTrace]
  refine ⟨107102151455645453937663361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142802868607527271916884481 107102151455645453937663361)
  ·
    refine ⟨80326613591734090453247521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107102151455645453937663361 80326613591734090453247521)
    ·
      refine ⟨60244960193800567839935641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80326613591734090453247521 60244960193800567839935641)
      ·
        refine ⟨45183720145350425879951731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60244960193800567839935641 45183720145350425879951731)
        ·
          refine ⟨67775580218025638819927597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45183720145350425879951731 67775580218025638819927597)
          ·
            refine ⟨25415842581759614557472849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67775580218025638819927597 25415842581759614557472849)
            ·
              refine ⟨19061881936319710918104637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25415842581759614557472849 19061881936319710918104637)
              ·
                refine ⟨7148205726119891594289239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19061881936319710918104637 7148205726119891594289239)
                ·
                  refine ⟨10722308589179837391433859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7148205726119891594289239 10722308589179837391433859)
                  ·
                    refine ⟨16083462883769756087150789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10722308589179837391433859 16083462883769756087150789)
                    ·
                      refine ⟨3015649290706829266340773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16083462883769756087150789 3015649290706829266340773)
                      ·
                        rfl

theorem cell23_5872956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_5872956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872956 prefixEnd_5872956 := by exact prefixLift 5872956
  have htrace : WordTrace (prefixWord ++ tailWord_5872956) baseStart_5872956 baseEnd_5872956 := by
    simpa [prefixWord, tailWord_5872956, baseEnd_5872956] using wordTrace_append hprefix tailTrace_5872956
  have hstable : (prefixWord ++ tailWord_5872956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872956).length < 2 ^ (prefixWord ++ tailWord_5872956).sum := by decide
  have hdescent : baseEnd_5872956 < baseStart_5872956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872959 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_5872959 : Nat := 118140960795 + 5872959 * 2 ^ 59
def prefixEnd_5872959 : Nat := 4983230072969 + 3 ^ 40 * 5872959 * 2
def baseEnd_5872959 : Nat := 3015650831148792754603259

theorem tailTrace_5872959 : CollatzResearch.WordTrace tailWord_5872959 prefixEnd_5872959 3015650831148792754603259 := by
  unfold tailWord_5872959
  simp only [CollatzResearch.WordTrace]
  refine ⟨214204412330280039387685931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142802941553520026258457287 214204412330280039387685931)
  ·
    refine ⟨321306618495420059081528897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214204412330280039387685931 321306618495420059081528897)
    ·
      refine ⟨240979963871565044311146673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321306618495420059081528897 240979963871565044311146673)
      ·
        refine ⟨180734972903673783233360005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240979963871565044311146673 180734972903673783233360005)
        ·
          refine ⟨33887807419438834356255001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180734972903673783233360005 33887807419438834356255001)
          ·
            refine ⟨25415855564579125767191251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33887807419438834356255001 25415855564579125767191251)
            ·
              refine ⟨38123783346868688650786877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25415855564579125767191251 38123783346868688650786877)
              ·
                refine ⟨14296418755075758244045079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38123783346868688650786877 14296418755075758244045079)
                ·
                  refine ⟨21444628132613637366067619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14296418755075758244045079 21444628132613637366067619)
                  ·
                    refine ⟨32166942198920456049101429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21444628132613637366067619 32166942198920456049101429)
                    ·
                      refine ⟨3015650831148792754603259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32166942198920456049101429 3015650831148792754603259)
                      ·
                        rfl

theorem cell23_5872959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_5872959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872959 prefixEnd_5872959 := by exact prefixLift 5872959
  have htrace : WordTrace (prefixWord ++ tailWord_5872959) baseStart_5872959 baseEnd_5872959 := by
    simpa [prefixWord, tailWord_5872959, baseEnd_5872959] using wordTrace_append hprefix tailTrace_5872959
  have hstable : (prefixWord ++ tailWord_5872959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872959).length < 2 ^ (prefixWord ++ tailWord_5872959).sum := by decide
  have hdescent : baseEnd_5872959 < baseStart_5872959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5872983 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 2, 4]
def baseStart_5872983 : Nat := 118140960795 + 5872983 * 2 ^ 59
def prefixEnd_5872983 : Nat := 4983230072969 + 3 ^ 40 * 5872983 * 2
def baseEnd_5872983 : Nat := 1005221051561500220234383

theorem tailTrace_5872983 : CollatzResearch.WordTrace tailWord_5872983 prefixEnd_5872983 1005221051561500220234383 := by
  unfold tailWord_5872983
  simp only [CollatzResearch.WordTrace]
  refine ⟨214205287682193091486559603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142803525121462060991039735 214205287682193091486559603)
  ·
    refine ⟨321307931523289637229839405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214205287682193091486559603 321307931523289637229839405)
    ·
      refine ⟨120490474321233613961189777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321307931523289637229839405 120490474321233613961189777)
      ·
        refine ⟨90367855740925210470892333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120490474321233613961189777 90367855740925210470892333)
        ·
          refine ⟨33887945902846953926584625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90367855740925210470892333 33887945902846953926584625)
          ·
            refine ⟨25415959427135215444938469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33887945902846953926584625 25415959427135215444938469)
            ·
              refine ⟨4765492392587852895925963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25415959427135215444938469 4765492392587852895925963)
              ·
                refine ⟨7148238588881779343888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4765492392587852895925963 7148238588881779343888945)
                ·
                  refine ⟨5361178941661334507916709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7148238588881779343888945 5361178941661334507916709)
                  ·
                    refine ⟨1005221051561500220234383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361178941661334507916709 1005221051561500220234383)
                    ·
                      rfl

theorem cell23_5872983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_5872983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5872983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5872983 prefixEnd_5872983 := by exact prefixLift 5872983
  have htrace : WordTrace (prefixWord ++ tailWord_5872983) baseStart_5872983 baseEnd_5872983 := by
    simpa [prefixWord, tailWord_5872983, baseEnd_5872983] using wordTrace_append hprefix tailTrace_5872983
  have hstable : (prefixWord ++ tailWord_5872983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5872983).length < 2 ^ (prefixWord ++ tailWord_5872983).sum := by decide
  have hdescent : baseEnd_5872983 < baseStart_5872983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5872983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873029 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_5873029 : Nat := 118140960795 + 5873029 * 2 ^ 59
def prefixEnd_5873029 : Nat := 4983230072969 + 3 ^ 40 * 5873029 * 2
def baseEnd_5873029 : Nat := 3015686774794607480727937

theorem tailTrace_5873029 : CollatzResearch.WordTrace tailWord_5873029 prefixEnd_5873029 3015686774794607480727937 := by
  unfold tailWord_5873029
  simp only [CollatzResearch.WordTrace]
  refine ⟨214206965440026441342734141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142804643626684294228489427 214206965440026441342734141)
  ·
    refine ⟨80327612040009915503525303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214206965440026441342734141 80327612040009915503525303)
    ·
      refine ⟨120491418060014873255287955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80327612040009915503525303 120491418060014873255287955)
      ·
        refine ⟨180737127090022309882931933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120491418060014873255287955 180737127090022309882931933)
        ·
          refine ⟨67776422658758366206099475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180737127090022309882931933 67776422658758366206099475)
          ·
            refine ⟨101664633988137549309149213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67776422658758366206099475 101664633988137549309149213)
            ·
              refine ⟨38124237745551580990930955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101664633988137549309149213 38124237745551580990930955)
              ·
                refine ⟨57186356618327371486396433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38124237745551580990930955 57186356618327371486396433)
                ·
                  refine ⟨42889767463745528614797325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57186356618327371486396433 42889767463745528614797325)
                  ·
                    refine ⟨16083662798904573230548997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42889767463745528614797325 16083662798904573230548997)
                    ·
                      refine ⟨3015686774794607480727937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16083662798904573230548997 3015686774794607480727937)
                      ·
                        rfl

theorem cell23_5873029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_5873029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873029 prefixEnd_5873029 := by exact prefixLift 5873029
  have htrace : WordTrace (prefixWord ++ tailWord_5873029) baseStart_5873029 baseEnd_5873029 := by
    simpa [prefixWord, tailWord_5873029, baseEnd_5873029] using wordTrace_append hprefix tailTrace_5873029
  have hstable : (prefixWord ++ tailWord_5873029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873029).length < 2 ^ (prefixWord ++ tailWord_5873029).sum := by decide
  have hdescent : baseEnd_5873029 < baseStart_5873029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873059 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4]
def baseStart_5873059 : Nat := 118140960795 + 5873059 * 2 ^ 59
def prefixEnd_5873059 : Nat := 4983230072969 + 3 ^ 40 * 5873059 * 2
def baseEnd_5873059 : Nat := 3015702179214242363352799

theorem tailTrace_5873059 : CollatzResearch.WordTrace tailWord_5873059 prefixEnd_5873059 3015702179214242363352799 := by
  unfold tailWord_5873059
  simp only [CollatzResearch.WordTrace]
  refine ⟨214208059629917756466326231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142805373086611837644217487 214208059629917756466326231)
  ·
    refine ⟨321312089444876634699489347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214208059629917756466326231 321312089444876634699489347)
    ·
      refine ⟨481968134167314952049234021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321312089444876634699489347 481968134167314952049234021)
      ·
        refine ⟨90369025156371553509231379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 481968134167314952049234021 90369025156371553509231379)
        ·
          refine ⟨135553537734557330263847069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90369025156371553509231379 135553537734557330263847069)
          ·
            refine ⟨50832576650458998848942651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135553537734557330263847069 50832576650458998848942651)
            ·
              refine ⟨76248864975688498273413977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50832576650458998848942651 76248864975688498273413977)
              ·
                refine ⟨57186648731766373705060483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76248864975688498273413977 57186648731766373705060483)
                ·
                  refine ⟨85779973097649560557590725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57186648731766373705060483 85779973097649560557590725)
                  ·
                    refine ⟨16083744955809292604548261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85779973097649560557590725 16083744955809292604548261)
                    ·
                      refine ⟨3015702179214242363352799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16083744955809292604548261 3015702179214242363352799)
                      ·
                        rfl

theorem cell23_5873059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_5873059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873059 prefixEnd_5873059 := by exact prefixLift 5873059
  have htrace : WordTrace (prefixWord ++ tailWord_5873059) baseStart_5873059 baseEnd_5873059 := by
    simpa [prefixWord, tailWord_5873059, baseEnd_5873059] using wordTrace_append hprefix tailTrace_5873059
  have hstable : (prefixWord ++ tailWord_5873059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873059).length < 2 ^ (prefixWord ++ tailWord_5873059).sum := by decide
  have hdescent : baseEnd_5873059 < baseStart_5873059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873063 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5873063 : Nat := 118140960795 + 5873063 * 2 ^ 59
def prefixEnd_5873063 : Nat := 4983230072969 + 3 ^ 40 * 5873063 * 2
def baseEnd_5873063 : Nat := 3015704233136860347702781

theorem tailTrace_5873063 : CollatzResearch.WordTrace tailWord_5873063 prefixEnd_5873063 3015704233136860347702781 := by
  unfold tailWord_5873063
  simp only [CollatzResearch.WordTrace]
  refine ⟨214208205521903265149471843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142805470347935510099647895 214208205521903265149471843)
  ·
    refine ⟨321312308282854897724207765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214208205521903265149471843 321312308282854897724207765)
    ·
      refine ⟨15061514450758823330822239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 321312308282854897724207765 15061514450758823330822239)
      ·
        refine ⟨22592271676138234996233359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15061514450758823330822239 22592271676138234996233359)
        ·
          refine ⟨33888407514207352494350039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22592271676138234996233359 33888407514207352494350039)
          ·
            refine ⟨50832611271311028741525059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33888407514207352494350039 50832611271311028741525059)
            ·
              refine ⟨76248916906966543112287589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50832611271311028741525059 76248916906966543112287589)
              ·
                refine ⟨14296671920056226833553923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76248916906966543112287589 14296671920056226833553923)
                ·
                  refine ⟨21445007880084340250330885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14296671920056226833553923 21445007880084340250330885)
                  ·
                    refine ⟨4020938977515813796937041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21445007880084340250330885 4020938977515813796937041)
                    ·
                      refine ⟨3015704233136860347702781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020938977515813796937041 3015704233136860347702781)
                      ·
                        rfl

theorem cell23_5873063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5873063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873063 prefixEnd_5873063 := by exact prefixLift 5873063
  have htrace : WordTrace (prefixWord ++ tailWord_5873063) baseStart_5873063 baseEnd_5873063 := by
    simpa [prefixWord, tailWord_5873063, baseEnd_5873063] using wordTrace_append hprefix tailTrace_5873063
  have hstable : (prefixWord ++ tailWord_5873063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873063).length < 2 ^ (prefixWord ++ tailWord_5873063).sum := by decide
  have hdescent : baseEnd_5873063 < baseStart_5873063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873080 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 2, 2, 2]
def baseStart_5873080 : Nat := 118140960795 + 5873080 * 2 ^ 59
def prefixEnd_5873080 : Nat := 4983230072969 + 3 ^ 40 * 5873080 * 2
def baseEnd_5873080 : Nat := 3015712962307986781190203

theorem tailTrace_5873080 : CollatzResearch.WordTrace tailWord_5873080 prefixEnd_5873080 3015712962307986781190203 := by
  unfold tailWord_5873080
  simp only [CollatzResearch.WordTrace]
  refine ⟨107104412781420838526420347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142805883708561118035227129 107104412781420838526420347)
  ·
    refine ⟨160656619172131257789630521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107104412781420838526420347 160656619172131257789630521)
    ·
      refine ⟨120492464379098443342222891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160656619172131257789630521 120492464379098443342222891)
      ·
        refine ⟨180738696568647665013334337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120492464379098443342222891 180738696568647665013334337)
        ·
          refine ⟨135554022426485748760000753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180738696568647665013334337 135554022426485748760000753)
          ·
            refine ⟨101665516819864311570000565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135554022426485748760000753 101665516819864311570000565)
            ·
              refine ⟨9531142201862279209687553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101665516819864311570000565 9531142201862279209687553)
              ·
                refine ⟨7148356651396709407265665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9531142201862279209687553 7148356651396709407265665)
                ·
                  refine ⟨5361267488547532055449249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7148356651396709407265665 5361267488547532055449249)
                  ·
                    refine ⟨4020950616410649041586937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361267488547532055449249 4020950616410649041586937)
                    ·
                      refine ⟨3015712962307986781190203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4020950616410649041586937 3015712962307986781190203)
                      ·
                        rfl

theorem cell23_5873080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_5873080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873080 prefixEnd_5873080 := by exact prefixLift 5873080
  have htrace : WordTrace (prefixWord ++ tailWord_5873080) baseStart_5873080 baseEnd_5873080 := by
    simpa [prefixWord, tailWord_5873080, baseEnd_5873080] using wordTrace_append hprefix tailTrace_5873080
  have hstable : (prefixWord ++ tailWord_5873080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873080).length < 2 ^ (prefixWord ++ tailWord_5873080).sum := by decide
  have hdescent : baseEnd_5873080 < baseStart_5873080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873096 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_5873096 : Nat := 118140960795 + 5873096 * 2 ^ 59
def prefixEnd_5873096 : Nat := 4983230072969 + 3 ^ 40 * 5873096 * 2
def baseEnd_5873096 : Nat := 3015721177998458718590129

theorem tailTrace_5873096 : CollatzResearch.WordTrace tailWord_5873096 prefixEnd_5873096 3015721177998458718590129 := by
  unfold tailWord_5873096
  simp only [CollatzResearch.WordTrace]
  refine ⟨107104704565391855892711571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142806272753855807856948761 107104704565391855892711571)
  ·
    refine ⟨160657056848087783839067357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107104704565391855892711571 160657056848087783839067357)
    ·
      refine ⟨60246396318032918939650259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160657056848087783839067357 60246396318032918939650259)
      ·
        refine ⟨90369594477049378409475389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60246396318032918939650259 90369594477049378409475389)
        ·
          refine ⟨33888597928893516903553271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90369594477049378409475389 33888597928893516903553271)
          ·
            refine ⟨50832896893340275355329907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33888597928893516903553271 50832896893340275355329907)
            ·
              refine ⟨76249345340010413032994861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50832896893340275355329907 76249345340010413032994861)
              ·
                refine ⟨28593504502503904887373073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76249345340010413032994861 28593504502503904887373073)
                ·
                  refine ⟨21445128376877928665529805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28593504502503904887373073 21445128376877928665529805)
                  ·
                    refine ⟨8041923141329223249573677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21445128376877928665529805 8041923141329223249573677)
                    ·
                      refine ⟨3015721177998458718590129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8041923141329223249573677 3015721177998458718590129)
                      ·
                        rfl

theorem cell23_5873096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_5873096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873096 prefixEnd_5873096 := by exact prefixLift 5873096
  have htrace : WordTrace (prefixWord ++ tailWord_5873096) baseStart_5873096 baseEnd_5873096 := by
    simpa [prefixWord, tailWord_5873096, baseEnd_5873096] using wordTrace_append hprefix tailTrace_5873096
  have hstable : (prefixWord ++ tailWord_5873096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873096).length < 2 ^ (prefixWord ++ tailWord_5873096).sum := by decide
  have hdescent : baseEnd_5873096 < baseStart_5873096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873099 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 1, 7]
def baseStart_5873099 : Nat := 118140960795 + 5873099 * 2 ^ 59
def prefixEnd_5873099 : Nat := 4983230072969 + 3 ^ 40 * 5873099 * 2
def baseEnd_5873099 : Nat := 1005240906146807402284205

theorem tailTrace_5873099 : CollatzResearch.WordTrace tailWord_5873099 prefixEnd_5873099 1005240906146807402284205 := by
  unfold tailWord_5873099
  simp only [CollatzResearch.WordTrace]
  refine ⟨214209518549772843297782351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142806345699848562198521567 214209518549772843297782351)
  ·
    refine ⟨321314277824659264946673527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214209518549772843297782351 321314277824659264946673527)
    ·
      refine ⟨481971416736988897420010291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321314277824659264946673527 481971416736988897420010291)
      ·
        refine ⟨722957125105483346130015437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481971416736988897420010291 722957125105483346130015437)
        ·
          refine ⟨271108921914556254798755789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722957125105483346130015437 271108921914556254798755789)
          ·
            refine ⟨101665845717958595549533421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271108921914556254798755789 101665845717958595549533421)
            ·
              refine ⟨38124692144234473331075033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101665845717958595549533421 38124692144234473331075033)
              ·
                refine ⟨28593519108175854998306275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38124692144234473331075033 28593519108175854998306275)
                ·
                  refine ⟨42890278662263782497459413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28593519108175854998306275 42890278662263782497459413)
                  ·
                    refine ⟨1005240906146807402284205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42890278662263782497459413 1005240906146807402284205)
                    ·
                      rfl

theorem cell23_5873099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_5873099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873099 prefixEnd_5873099 := by exact prefixLift 5873099
  have htrace : WordTrace (prefixWord ++ tailWord_5873099) baseStart_5873099 baseEnd_5873099 := by
    simpa [prefixWord, tailWord_5873099, baseEnd_5873099] using wordTrace_append hprefix tailTrace_5873099
  have hstable : (prefixWord ++ tailWord_5873099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873099).length < 2 ^ (prefixWord ++ tailWord_5873099).sum := by decide
  have hdescent : baseEnd_5873099 < baseStart_5873099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873136 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_5873136 : Nat := 118140960795 + 5873136 * 2 ^ 59
def prefixEnd_5873136 : Nat := 4983230072969 + 3 ^ 40 * 5873136 * 2
def baseEnd_5873136 : Nat := 3015741717224638562089945

theorem tailTrace_5873136 : CollatzResearch.WordTrace tailWord_5873136 prefixEnd_5873136 3015741717224638562089945 := by
  unfold tailWord_5873136
  simp only [CollatzResearch.WordTrace]
  refine ⟨107105434025319399308439631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142807245367092532411252841 107105434025319399308439631)
  ·
    refine ⟨160658151037979098962659447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107105434025319399308439631 160658151037979098962659447)
    ·
      refine ⟨240987226556968648443989171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160658151037979098962659447 240987226556968648443989171)
      ·
        refine ⟨361480839835452972665983757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240987226556968648443989171 361480839835452972665983757)
        ·
          refine ⟨135555314938294864749743909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361480839835452972665983757 135555314938294864749743909)
          ·
            refine ⟨25416621550930287140576983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135555314938294864749743909 25416621550930287140576983)
            ·
              refine ⟨38124932326395430710865475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25416621550930287140576983 38124932326395430710865475)
              ·
                refine ⟨57187398489593146066298213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38124932326395430710865475 57187398489593146066298213)
                ·
                  refine ⟨10722637216798714887430915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57187398489593146066298213 10722637216798714887430915)
                  ·
                    refine ⟨16083955825198072331146373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10722637216798714887430915 16083955825198072331146373)
                    ·
                      refine ⟨3015741717224638562089945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16083955825198072331146373 3015741717224638562089945)
                      ·
                        rfl

theorem cell23_5873136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_5873136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873136 prefixEnd_5873136 := by exact prefixLift 5873136
  have htrace : WordTrace (prefixWord ++ tailWord_5873136) baseStart_5873136 baseEnd_5873136 := by
    simpa [prefixWord, tailWord_5873136, baseEnd_5873136] using wordTrace_append hprefix tailTrace_5873136
  have hstable : (prefixWord ++ tailWord_5873136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873136).length < 2 ^ (prefixWord ++ tailWord_5873136).sum := by decide
  have hdescent : baseEnd_5873136 < baseStart_5873136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873139 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_5873139 : Nat := 118140960795 + 5873139 * 2 ^ 59
def prefixEnd_5873139 : Nat := 4983230072969 + 3 ^ 40 * 5873139 * 2
def baseEnd_5873139 : Nat := 3015743257666602050352431

theorem tailTrace_5873139 : CollatzResearch.WordTrace tailWord_5873139 prefixEnd_5873139 3015743257666602050352431 := by
  unfold tailWord_5873139
  simp only [CollatzResearch.WordTrace]
  refine ⟨214210977469627930129238471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142807318313085286752825647 214210977469627930129238471)
  ·
    refine ⟨321316466204441895193857707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214210977469627930129238471 321316466204441895193857707)
    ·
      refine ⟨481974699306662842790786561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321316466204441895193857707 481974699306662842790786561)
      ·
        refine ⟨361481024479997132093089921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481974699306662842790786561 361481024479997132093089921)
        ·
          refine ⟨271110768359997849069817441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361481024479997132093089921 271110768359997849069817441)
          ·
            refine ⟨203333076269998386802363081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271110768359997849069817441 203333076269998386802363081)
            ·
              refine ⟨152499807202498790101772311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203333076269998386802363081 152499807202498790101772311)
              ·
                refine ⟨228749710803748185152658467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152499807202498790101772311 228749710803748185152658467)
                ·
                  refine ⟨343124566205622277728987701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228749710803748185152658467 343124566205622277728987701)
                  ·
                    refine ⟨32167928081777088537092597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 343124566205622277728987701 32167928081777088537092597)
                    ·
                      refine ⟨3015743257666602050352431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32167928081777088537092597 3015743257666602050352431)
                      ·
                        rfl

theorem cell23_5873139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_5873139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873139 prefixEnd_5873139 := by exact prefixLift 5873139
  have htrace : WordTrace (prefixWord ++ tailWord_5873139) baseStart_5873139 baseEnd_5873139 := by
    simpa [prefixWord, tailWord_5873139, baseEnd_5873139] using wordTrace_append hprefix tailTrace_5873139
  have hstable : (prefixWord ++ tailWord_5873139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873139).length < 2 ^ (prefixWord ++ tailWord_5873139).sum := by decide
  have hdescent : baseEnd_5873139 < baseStart_5873139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873173 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_5873173 : Nat := 118140960795 + 5873173 * 2 ^ 59
def prefixEnd_5873173 : Nat := 4983230072969 + 3 ^ 40 * 5873173 * 2
def baseEnd_5873173 : Nat := 3015760716008854917327275

theorem tailTrace_5873173 : CollatzResearch.WordTrace tailWord_5873173 prefixEnd_5873173 3015760716008854917327275 := by
  unfold tailWord_5873173
  simp only [CollatzResearch.WordTrace]
  refine ⟨214212217551504753935976173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142808145034336502623984115 214212217551504753935976173)
  ·
    refine ⟨80329581581814282725991065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214212217551504753935976173 80329581581814282725991065)
    ·
      refine ⟨60247186186360712044493299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80329581581814282725991065 60247186186360712044493299)
      ·
        refine ⟨90370779279541068066739949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60247186186360712044493299 90370779279541068066739949)
        ·
          refine ⟨33889042229827900525027481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90370779279541068066739949 33889042229827900525027481)
          ·
            refine ⟨25416781672370925393770611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33889042229827900525027481 25416781672370925393770611)
            ·
              refine ⟨38125172508556388090655917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25416781672370925393770611 38125172508556388090655917)
              ·
                refine ⟨14296939690708645533995969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38125172508556388090655917 14296939690708645533995969)
                ·
                  refine ⟨10722704768031484150496977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14296939690708645533995969 10722704768031484150496977)
                  ·
                    refine ⟨8042028576023613112872733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10722704768031484150496977 8042028576023613112872733)
                    ·
                      refine ⟨3015760716008854917327275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8042028576023613112872733 3015760716008854917327275)
                      ·
                        rfl

theorem cell23_5873173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_5873173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873173 prefixEnd_5873173 := by exact prefixLift 5873173
  have htrace : WordTrace (prefixWord ++ tailWord_5873173) baseStart_5873173 baseEnd_5873173 := by
    simpa [prefixWord, tailWord_5873173, baseEnd_5873173] using wordTrace_append hprefix tailTrace_5873173
  have hstable : (prefixWord ++ tailWord_5873173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873173).length < 2 ^ (prefixWord ++ tailWord_5873173).sum := by decide
  have hdescent : baseEnd_5873173 < baseStart_5873173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873180 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_5873180 : Nat := 118140960795 + 5873180 * 2 ^ 59
def prefixEnd_5873180 : Nat := 4983230072969 + 3 ^ 40 * 5873180 * 2
def baseEnd_5873180 : Nat := 1005254770124478796646581

theorem tailTrace_5873180 : CollatzResearch.WordTrace tailWord_5873180 prefixEnd_5873180 1005254770124478796646581 := by
  unfold tailWord_5873180
  simp only [CollatzResearch.WordTrace]
  refine ⟨107106236431239697065740497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142808315241652929420987329 107106236431239697065740497)
  ·
    refine ⟨80329677323429772799305373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107106236431239697065740497 80329677323429772799305373)
    ·
      refine ⟨30123628996286164799739515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80329677323429772799305373 30123628996286164799739515)
      ·
        refine ⟨45185443494429247199609273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30123628996286164799739515 45185443494429247199609273)
        ·
          refine ⟨33889082620821935399706955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45185443494429247199609273 33889082620821935399706955)
          ·
            refine ⟨50833623931232903099560433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33889082620821935399706955 50833623931232903099560433)
            ·
              refine ⟨38125217948424677324670325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50833623931232903099560433 38125217948424677324670325)
              ·
                refine ⟨3574239182664813499187843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38125217948424677324670325 3574239182664813499187843)
                ·
                  refine ⟨5361358773997220248781765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574239182664813499187843 5361358773997220248781765)
                  ·
                    refine ⟨1005254770124478796646581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361358773997220248781765 1005254770124478796646581)
                    ·
                      rfl

theorem cell23_5873180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_5873180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873180 prefixEnd_5873180 := by exact prefixLift 5873180
  have htrace : WordTrace (prefixWord ++ tailWord_5873180) baseStart_5873180 baseEnd_5873180 := by
    simpa [prefixWord, tailWord_5873180, baseEnd_5873180] using wordTrace_append hprefix tailTrace_5873180
  have hstable : (prefixWord ++ tailWord_5873180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873180).length < 2 ^ (prefixWord ++ tailWord_5873180).sum := by decide
  have hdescent : baseEnd_5873180 < baseStart_5873180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873270 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_5873270 : Nat := 118140960795 + 5873270 * 2 ^ 59
def prefixEnd_5873270 : Nat := 4983230072969 + 3 ^ 40 * 5873270 * 2
def baseEnd_5873270 : Nat := 1005270174544113679271443

theorem tailTrace_5873270 : CollatzResearch.WordTrace tailWord_5873270 prefixEnd_5873270 1005270174544113679271443 := by
  unfold tailWord_5873270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388484714509583718891079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142810503621435559668171509 13388484714509583718891079)
  ·
    refine ⟨20082727071764375578336619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13388484714509583718891079 20082727071764375578336619)
    ·
      refine ⟨30124090607646563367504929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20082727071764375578336619 30124090607646563367504929)
      ·
        refine ⟨22593067955734922525628697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30124090607646563367504929 22593067955734922525628697)
        ·
          refine ⟨16944800966801191894221523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22593067955734922525628697 16944800966801191894221523)
          ·
            refine ⟨25417201450201787841332285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16944800966801191894221523 25417201450201787841332285)
            ·
              refine ⟨9531450543825670440499607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25417201450201787841332285 9531450543825670440499607)
              ·
                refine ⟨14297175815738505660749411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9531450543825670440499607 14297175815738505660749411)
                ·
                  refine ⟨21445763723607758491124117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14297175815738505660749411 21445763723607758491124117)
                  ·
                    refine ⟨1005270174544113679271443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21445763723607758491124117 1005270174544113679271443)
                    ·
                      rfl

theorem cell23_5873270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_5873270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873270 prefixEnd_5873270 := by exact prefixLift 5873270
  have htrace : WordTrace (prefixWord ++ tailWord_5873270) baseStart_5873270 baseEnd_5873270 := by
    simpa [prefixWord, tailWord_5873270, baseEnd_5873270] using wordTrace_append hprefix tailTrace_5873270
  have hstable : (prefixWord ++ tailWord_5873270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873270).length < 2 ^ (prefixWord ++ tailWord_5873270).sum := by decide
  have hdescent : baseEnd_5873270 < baseStart_5873270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873277 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_5873277 : Nat := 118140960795 + 5873277 * 2 ^ 59
def prefixEnd_5873277 : Nat := 4983230072969 + 3 ^ 40 * 5873277 * 2
def baseEnd_5873277 : Nat := 3015814117996922510426797

theorem tailTrace_5873277 : CollatzResearch.WordTrace tailWord_5873277 prefixEnd_5873277 3015814117996922510426797 := by
  unfold tailWord_5873277
  simp only [CollatzResearch.WordTrace]
  refine ⟨214216010743127979697762085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142810673828751986465174723 214216010743127979697762085)
  ·
    refine ⟨40165502014336496193330391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214216010743127979697762085 40165502014336496193330391)
    ·
      refine ⟨60248253021504744289995587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40165502014336496193330391 60248253021504744289995587)
      ·
        refine ⟨90372379532257116434993381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60248253021504744289995587 90372379532257116434993381)
        ·
          refine ⟨16944821162298209331561259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90372379532257116434993381 16944821162298209331561259)
          ·
            refine ⟨25417231743447313997341889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16944821162298209331561259 25417231743447313997341889)
            ·
              refine ⟨19062923807585485498006417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25417231743447313997341889 19062923807585485498006417)
              ·
                refine ⟨14297192855689114123504813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19062923807585485498006417 14297192855689114123504813)
                ·
                  refine ⟨5361447320883417796314305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14297192855689114123504813 5361447320883417796314305)
                  ·
                    refine ⟨4021085490662563347235729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361447320883417796314305 4021085490662563347235729)
                    ·
                      refine ⟨3015814117996922510426797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021085490662563347235729 3015814117996922510426797)
                      ·
                        rfl

theorem cell23_5873277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_5873277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873277 prefixEnd_5873277 := by exact prefixLift 5873277
  have htrace : WordTrace (prefixWord ++ tailWord_5873277) baseStart_5873277 baseEnd_5873277 := by
    simpa [prefixWord, tailWord_5873277, baseEnd_5873277] using wordTrace_append hprefix tailTrace_5873277
  have hstable : (prefixWord ++ tailWord_5873277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873277).length < 2 ^ (prefixWord ++ tailWord_5873277).sum := by decide
  have hdescent : baseEnd_5873277 < baseStart_5873277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873280 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3]
def baseStart_5873280 : Nat := 118140960795 + 5873280 * 2 ^ 59
def prefixEnd_5873280 : Nat := 4983230072969 + 3 ^ 40 * 5873280 * 2
def baseEnd_5873280 : Nat := 3015815658438885998689283

theorem tailTrace_5873280 : CollatzResearch.WordTrace tailWord_5873280 prefixEnd_5873280 3015815658438885998689283 := by
  unfold tailWord_5873280
  simp only [CollatzResearch.WordTrace]
  refine ⟨107108060081058555605060647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142810746774744740806747529 107108060081058555605060647)
  ·
    refine ⟨160662090121587833407590971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107108060081058555605060647 160662090121587833407590971)
    ·
      refine ⟨240993135182381750111386457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160662090121587833407590971 240993135182381750111386457)
      ·
        refine ⟨180744851386786312583539843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240993135182381750111386457 180744851386786312583539843)
        ·
          refine ⟨271117277080179468875309765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180744851386786312583539843 271117277080179468875309765)
          ·
            refine ⟨50834489452533650414120581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271117277080179468875309765 50834489452533650414120581)
            ·
              refine ⟨9531466772350059452647609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50834489452533650414120581 9531466772350059452647609)
              ·
                refine ⟨7148600079262544589485707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9531466772350059452647609 7148600079262544589485707)
                ·
                  refine ⟨10722900118893816884228561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7148600079262544589485707 10722900118893816884228561)
                  ·
                    refine ⟨8042175089170362663171421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10722900118893816884228561 8042175089170362663171421)
                    ·
                      refine ⟨3015815658438885998689283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8042175089170362663171421 3015815658438885998689283)
                      ·
                        rfl

theorem cell23_5873280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_5873280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873280 prefixEnd_5873280 := by exact prefixLift 5873280
  have htrace : WordTrace (prefixWord ++ tailWord_5873280) baseStart_5873280 baseEnd_5873280 := by
    simpa [prefixWord, tailWord_5873280, baseEnd_5873280] using wordTrace_append hprefix tailTrace_5873280
  have hstable : (prefixWord ++ tailWord_5873280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873280).length < 2 ^ (prefixWord ++ tailWord_5873280).sum := by decide
  have hdescent : baseEnd_5873280 < baseStart_5873280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
