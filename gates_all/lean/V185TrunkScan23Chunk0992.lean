import V185TrunkScan23Chunk0991

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5873288 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5873288 : Nat := 118140960795 + 5873288 * 2 ^ 59
def prefixEnd_5873288 : Nat := 4983230072969 + 3 ^ 40 * 5873288 * 2
def baseEnd_5873288 : Nat := 3015819766284121967389247

theorem tailTrace_5873288 : CollatzResearch.WordTrace tailWord_5873288 prefixEnd_5873288 3015819766284121967389247 := by
  unfold tailWord_5873288
  simp only [CollatzResearch.WordTrace]
  refine ⟨107108205973044064288206259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142810941297392085717608345 107108205973044064288206259)
  ·
    refine ⟨160662308959566096432309389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107108205973044064288206259 160662308959566096432309389)
    ·
      refine ⟨60248365859837286162116021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160662308959566096432309389 60248365859837286162116021)
      ·
        refine ⟨5648284299359745577698377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60248365859837286162116021 5648284299359745577698377)
        ·
          refine ⟨4236213224519809183273783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5648284299359745577698377 4236213224519809183273783)
          ·
            refine ⟨6354319836779713774910675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236213224519809183273783 6354319836779713774910675)
            ·
              refine ⟨9531479755169570662366013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354319836779713774910675 9531479755169570662366013)
              ·
                refine ⟨3574304908188588998387255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9531479755169570662366013 3574304908188588998387255)
                ·
                  refine ⟨5361457362282883497580883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574304908188588998387255 5361457362282883497580883)
                  ·
                    refine ⟨8042186043424325246371325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5361457362282883497580883 8042186043424325246371325)
                    ·
                      refine ⟨3015819766284121967389247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8042186043424325246371325 3015819766284121967389247)
                      ·
                        rfl

theorem cell23_5873288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5873288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873288 prefixEnd_5873288 := by exact prefixLift 5873288
  have htrace : WordTrace (prefixWord ++ tailWord_5873288) baseStart_5873288 baseEnd_5873288 := by
    simpa [prefixWord, tailWord_5873288, baseEnd_5873288] using wordTrace_append hprefix tailTrace_5873288
  have hstable : (prefixWord ++ tailWord_5873288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873288).length < 2 ^ (prefixWord ++ tailWord_5873288).sum := by decide
  have hdescent : baseEnd_5873288 < baseStart_5873288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873300 : List Nat := [2, 4, 2, 2, 2, 2, 9]
def baseStart_5873300 : Nat := 118140960795 + 5873300 * 2 ^ 59
def prefixEnd_5873300 : Nat := 4983230072969 + 3 ^ 40 * 5873300 * 2
def baseEnd_5873300 : Nat := 37232418864839208894311

theorem tailTrace_5873300 : CollatzResearch.WordTrace tailWord_5873300 prefixEnd_5873300 37232418864839208894311 := by
  unfold tailWord_5873300
  simp only [CollatzResearch.WordTrace]
  refine ⟨107108424811022327312924677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142811233081363103083899569 107108424811022327312924677)
  ·
    refine ⟨20082829652066686371173377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107108424811022327312924677 20082829652066686371173377)
    ·
      refine ⟨15062122239050014778380033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20082829652066686371173377 15062122239050014778380033)
      ·
        refine ⟨11296591679287511083785025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15062122239050014778380033 11296591679287511083785025)
        ·
          refine ⟨8472443759465633312838769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11296591679287511083785025 8472443759465633312838769)
          ·
            refine ⟨6354332819599224984629077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8472443759465633312838769 6354332819599224984629077)
            ·
              refine ⟨37232418864839208894311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6354332819599224984629077 37232418864839208894311)
              ·
                rfl

theorem cell23_5873300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 9].length) (baseStart_5873300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873300 prefixEnd_5873300 := by exact prefixLift 5873300
  have htrace : WordTrace (prefixWord ++ tailWord_5873300) baseStart_5873300 baseEnd_5873300 := by
    simpa [prefixWord, tailWord_5873300, baseEnd_5873300] using wordTrace_append hprefix tailTrace_5873300
  have hstable : (prefixWord ++ tailWord_5873300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873300).length < 2 ^ (prefixWord ++ tailWord_5873300).sum := by decide
  have hdescent : baseEnd_5873300 < baseStart_5873300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873311 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5873311 : Nat := 118140960795 + 5873311 * 2 ^ 59
def prefixEnd_5873311 : Nat := 4983230072969 + 3 ^ 40 * 5873311 * 2
def baseEnd_5873311 : Nat := 3015831576339175377401641

theorem tailTrace_5873311 : CollatzResearch.WordTrace tailWord_5873311 prefixEnd_5873311 3015831576339175377401641 := by
  unfold tailWord_5873311
  simp only [CollatzResearch.WordTrace]
  refine ⟨214217250825004803504499787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142811500550003202336333191 214217250825004803504499787)
  ·
    refine ⟨321325876237507205256749681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214217250825004803504499787 321325876237507205256749681)
    ·
      refine ⟨240994407178130403942562261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321325876237507205256749681 240994407178130403942562261)
      ·
        refine ⟨5648306418237431342403803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 240994407178130403942562261 5648306418237431342403803)
        ·
          refine ⟨8472459627356147013605705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648306418237431342403803 8472459627356147013605705)
          ·
            refine ⟨6354344720517110260204279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8472459627356147013605705 6354344720517110260204279)
            ·
              refine ⟨9531517080775665390306419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354344720517110260204279 9531517080775665390306419)
              ·
                refine ⟨14297275621163498085459629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9531517080775665390306419 14297275621163498085459629)
                ·
                  refine ⟨5361478357936311782047361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14297275621163498085459629 5361478357936311782047361)
                  ·
                    refine ⟨4021108768452233836535521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361478357936311782047361 4021108768452233836535521)
                    ·
                      refine ⟨3015831576339175377401641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021108768452233836535521 3015831576339175377401641)
                      ·
                        rfl

theorem cell23_5873311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5873311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873311 prefixEnd_5873311 := by exact prefixLift 5873311
  have htrace : WordTrace (prefixWord ++ tailWord_5873311) baseStart_5873311 baseEnd_5873311 := by
    simpa [prefixWord, tailWord_5873311, baseEnd_5873311] using wordTrace_append hprefix tailTrace_5873311
  have hstable : (prefixWord ++ tailWord_5873311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873311).length < 2 ^ (prefixWord ++ tailWord_5873311).sum := by decide
  have hdescent : baseEnd_5873311 < baseStart_5873311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873337 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 1, 3, 2]
def baseStart_5873337 : Nat := 118140960795 + 5873337 * 2 ^ 59
def prefixEnd_5873337 : Nat := 4983230072969 + 3 ^ 40 * 5873337 * 2
def baseEnd_5873337 : Nat := 3015844926836192275676521

theorem tailTrace_5873337 : CollatzResearch.WordTrace tailWord_5873337 prefixEnd_5873337 3015844926836192275676521 := by
  unfold tailWord_5873337
  simp only [CollatzResearch.WordTrace]
  refine ⟨214218199122910609944946265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142812132748607073296630843 214218199122910609944946265)
  ·
    refine ⟨160663649342182957458709699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214218199122910609944946265 160663649342182957458709699)
    ·
      refine ⟨240995474013274436188064549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160663649342182957458709699 240995474013274436188064549)
      ·
        refine ⟨45186651377488956785262103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240995474013274436188064549 45186651377488956785262103)
        ·
          refine ⟨67779977066233435177893155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45186651377488956785262103 67779977066233435177893155)
          ·
            refine ⟨101669965599350152766839733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67779977066233435177893155 101669965599350152766839733)
            ·
              refine ⟨9531559274939076821891225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101669965599350152766839733 9531559274939076821891225)
              ·
                refine ⟨7148669456204307616418419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9531559274939076821891225 7148669456204307616418419)
                ·
                  refine ⟨10723004184306461424627629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7148669456204307616418419 10723004184306461424627629)
                  ·
                    refine ⟨4021126569114923034235361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10723004184306461424627629 4021126569114923034235361)
                    ·
                      refine ⟨3015844926836192275676521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021126569114923034235361 3015844926836192275676521)
                      ·
                        rfl

theorem cell23_5873337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_5873337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873337 prefixEnd_5873337 := by exact prefixLift 5873337
  have htrace : WordTrace (prefixWord ++ tailWord_5873337) baseStart_5873337 baseEnd_5873337 := by
    simpa [prefixWord, tailWord_5873337, baseEnd_5873337] using wordTrace_append hprefix tailTrace_5873337
  have hstable : (prefixWord ++ tailWord_5873337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873337).length < 2 ^ (prefixWord ++ tailWord_5873337).sum := by decide
  have hdescent : baseEnd_5873337 < baseStart_5873337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873384 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5873384 : Nat := 118140960795 + 5873384 * 2 ^ 59
def prefixEnd_5873384 : Nat := 4983230072969 + 3 ^ 40 * 5873384 * 2
def baseEnd_5873384 : Nat := 3015869060426953591788805

theorem tailTrace_5873384 : CollatzResearch.WordTrace tailWord_5873384 prefixEnd_5873384 3015869060426953591788805 := by
  unfold tailWord_5873384
  simp only [CollatzResearch.WordTrace]
  refine ⟨107109956676870168485953603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142813275569160224647938137 107109956676870168485953603)
  ·
    refine ⟨160664935015305252728930405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107109956676870168485953603 160664935015305252728930405)
    ·
      refine ⟨30124675315369734886674451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160664935015305252728930405 30124675315369734886674451)
      ·
        refine ⟨45187012973054602330011677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30124675315369734886674451 45187012973054602330011677)
        ·
          refine ⟨16945129864895475873754379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45187012973054602330011677 16945129864895475873754379)
          ·
            refine ⟨25417694797343213810631569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16945129864895475873754379 25417694797343213810631569)
            ·
              refine ⟨19063271098007410357973677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25417694797343213810631569 19063271098007410357973677)
              ·
                refine ⟨7148726661752778884240129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19063271098007410357973677 7148726661752778884240129)
                ·
                  refine ⟨5361544996314584163180097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7148726661752778884240129 5361544996314584163180097)
                  ·
                    refine ⟨4021158747235938122385073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361544996314584163180097 4021158747235938122385073)
                    ·
                      refine ⟨3015869060426953591788805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021158747235938122385073 3015869060426953591788805)
                      ·
                        rfl

theorem cell23_5873384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5873384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873384 prefixEnd_5873384 := by exact prefixLift 5873384
  have htrace : WordTrace (prefixWord ++ tailWord_5873384) baseStart_5873384 baseEnd_5873384 := by
    simpa [prefixWord, tailWord_5873384, baseEnd_5873384] using wordTrace_append hprefix tailTrace_5873384
  have hstable : (prefixWord ++ tailWord_5873384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873384).length < 2 ^ (prefixWord ++ tailWord_5873384).sum := by decide
  have hdescent : baseEnd_5873384 < baseStart_5873384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873403 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 2, 5]
def baseStart_5873403 : Nat := 118140960795 + 5873403 * 2 ^ 59
def prefixEnd_5873403 : Nat := 4983230072969 + 3 ^ 40 * 5873403 * 2
def baseEnd_5873403 : Nat := 1005292938853129672483739

theorem tailTrace_5873403 : CollatzResearch.WordTrace tailWord_5873403 prefixEnd_5873403 1005292938853129672483739 := by
  unfold tailWord_5873403
  simp only [CollatzResearch.WordTrace]
  refine ⟨214220606340671503216848863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142813737560447668811232575 214220606340671503216848863)
  ·
    refine ⟨321330909511007254825273295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214220606340671503216848863 321330909511007254825273295)
    ·
      refine ⟨481996364266510882237909943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321330909511007254825273295 481996364266510882237909943)
      ·
        refine ⟨722994546399766323356864915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481996364266510882237909943 722994546399766323356864915)
        ·
          refine ⟨1084491819599649485035297373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722994546399766323356864915 1084491819599649485035297373)
          ·
            refine ⟨406684432349868556888236515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084491819599649485035297373 406684432349868556888236515)
            ·
              refine ⟨610026648524802835332354773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406684432349868556888236515 610026648524802835332354773)
              ·
                refine ⟨14297499574800066453102065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 610026648524802835332354773 14297499574800066453102065)
                ·
                  refine ⟨10723124681100049839826549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14297499574800066453102065 10723124681100049839826549)
                  ·
                    refine ⟨1005292938853129672483739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10723124681100049839826549 1005292938853129672483739)
                    ·
                      rfl

theorem cell23_5873403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 5].length) (baseStart_5873403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873403 prefixEnd_5873403 := by exact prefixLift 5873403
  have htrace : WordTrace (prefixWord ++ tailWord_5873403) baseStart_5873403 baseEnd_5873403 := by
    simpa [prefixWord, tailWord_5873403, baseEnd_5873403] using wordTrace_append hprefix tailTrace_5873403
  have hstable : (prefixWord ++ tailWord_5873403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873403).length < 2 ^ (prefixWord ++ tailWord_5873403).sum := by decide
  have hdescent : baseEnd_5873403 < baseStart_5873403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873484 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_5873484 : Nat := 118140960795 + 5873484 * 2 ^ 59
def prefixEnd_5873484 : Nat := 4983230072969 + 3 ^ 40 * 5873484 * 2
def baseEnd_5873484 : Nat := 1005306802830801066846115

theorem tailTrace_5873484 : CollatzResearch.WordTrace tailWord_5873484 prefixEnd_5873484 1005306802830801066846115 := by
  unfold tailWord_5873484
  simp only [CollatzResearch.WordTrace]
  refine ⟨107111780326689027025273753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142815707102252036033698337 107111780326689027025273753)
  ·
    refine ⟨80333835245016770268955315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107111780326689027025273753 80333835245016770268955315)
    ·
      refine ⟨120500752867525155403432973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80333835245016770268955315 120500752867525155403432973)
      ·
        refine ⟨45187782325321933276287365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120500752867525155403432973 45187782325321933276287365)
        ·
          refine ⟨8472709185997862489303881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45187782325321933276287365 8472709185997862489303881)
          ·
            refine ⟨6354531889498396866977911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8472709185997862489303881 6354531889498396866977911)
            ·
              refine ⟨9531797834247595300466867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354531889498396866977911 9531797834247595300466867)
              ·
                refine ⟨14297696751371392950700301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9531797834247595300466867 14297696751371392950700301)
                ·
                  refine ⟨5361636281764272356512613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14297696751371392950700301 5361636281764272356512613)
                  ·
                    refine ⟨1005306802830801066846115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361636281764272356512613 1005306802830801066846115)
                    ·
                      rfl

theorem cell23_5873484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_5873484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873484 prefixEnd_5873484 := by exact prefixLift 5873484
  have htrace : WordTrace (prefixWord ++ tailWord_5873484) baseStart_5873484 baseEnd_5873484 := by
    simpa [prefixWord, tailWord_5873484, baseEnd_5873484] using wordTrace_append hprefix tailTrace_5873484
  have hstable : (prefixWord ++ tailWord_5873484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873484).length < 2 ^ (prefixWord ++ tailWord_5873484).sum := by decide
  have hdescent : baseEnd_5873484 < baseStart_5873484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873517 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_5873517 : Nat := 118140960795 + 5873517 * 2 ^ 59
def prefixEnd_5873517 : Nat := 4983230072969 + 3 ^ 40 * 5873517 * 2
def baseEnd_5873517 : Nat := 3015937353354001571425693

theorem tailTrace_5873517 : CollatzResearch.WordTrace tailWord_5873517 prefixEnd_5873517 3015937353354001571425693 := by
  unfold tailWord_5873517
  simp only [CollatzResearch.WordTrace]
  refine ⟨214224764262258500686498805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142816509508172333790999203 214224764262258500686498805)
  ·
    refine ⟨20083571649586734439359263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214224764262258500686498805 20083571649586734439359263)
    ·
      refine ⟨30125357474380101659038895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20083571649586734439359263 30125357474380101659038895)
      ·
        refine ⟨45188036211570152488558343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30125357474380101659038895 45188036211570152488558343)
        ·
          refine ⟨67782054317355228732837515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45188036211570152488558343 67782054317355228732837515)
          ·
            refine ⟨101673081476032843099256273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67782054317355228732837515 101673081476032843099256273)
            ·
              refine ⟨76254811107024632324442205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101673081476032843099256273 76254811107024632324442205)
              ·
                refine ⟨28595554165134237121665827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76254811107024632324442205 28595554165134237121665827)
                ·
                  refine ⟨42893331247701355682498741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28595554165134237121665827 42893331247701355682498741)
                  ·
                    refine ⟨4021249804472002095234257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42893331247701355682498741 4021249804472002095234257)
                    ·
                      refine ⟨3015937353354001571425693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021249804472002095234257 3015937353354001571425693)
                      ·
                        rfl

theorem cell23_5873517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_5873517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873517 prefixEnd_5873517 := by exact prefixLift 5873517
  have htrace : WordTrace (prefixWord ++ tailWord_5873517) baseStart_5873517 baseEnd_5873517 := by
    simpa [prefixWord, tailWord_5873517, baseEnd_5873517] using wordTrace_append hprefix tailTrace_5873517
  have hstable : (prefixWord ++ tailWord_5873517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873517).length < 2 ^ (prefixWord ++ tailWord_5873517).sum := by decide
  have hdescent : baseEnd_5873517 < baseStart_5873517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873557 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_5873557 : Nat := 118140960795 + 5873557 * 2 ^ 59
def prefixEnd_5873557 : Nat := 4983230072969 + 3 ^ 40 * 5873557 * 2
def baseEnd_5873557 : Nat := 1005319297526727138308503

theorem tailTrace_5873557 : CollatzResearch.WordTrace tailWord_5873557 prefixEnd_5873557 1005319297526727138308503 := by
  unfold tailWord_5873557
  simp only [CollatzResearch.WordTrace]
  refine ⟨214226223182113587517954925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142817482121409058345303283 214226223182113587517954925)
  ·
    refine ⟨80334833693292595319233097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214226223182113587517954925 80334833693292595319233097)
    ·
      refine ⟨60251125269969446489424823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80334833693292595319233097 60251125269969446489424823)
      ·
        refine ⟨90376687904954169734137235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60251125269969446489424823 90376687904954169734137235)
        ·
          refine ⟨135565031857431254601205853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90376687904954169734137235 135565031857431254601205853)
          ·
            refine ⟨50836886946536720475452195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135565031857431254601205853 50836886946536720475452195)
            ·
              refine ⟨76255330419805080713178293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50836886946536720475452195 76255330419805080713178293)
              ·
                refine ⟨7148937226856726316860465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76255330419805080713178293 7148937226856726316860465)
                ·
                  refine ⟨5361702920142544737645349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7148937226856726316860465 5361702920142544737645349)
                  ·
                    refine ⟨1005319297526727138308503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361702920142544737645349 1005319297526727138308503)
                    ·
                      rfl

theorem cell23_5873557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_5873557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873557 prefixEnd_5873557 := by exact prefixLift 5873557
  have htrace : WordTrace (prefixWord ++ tailWord_5873557) baseStart_5873557 baseEnd_5873557 := by
    simpa [prefixWord, tailWord_5873557, baseEnd_5873557] using wordTrace_append hprefix tailTrace_5873557
  have hstable : (prefixWord ++ tailWord_5873557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873557).length < 2 ^ (prefixWord ++ tailWord_5873557).sum := by decide
  have hdescent : baseEnd_5873557 < baseStart_5873557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873598 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_5873598 : Nat := 118140960795 + 5873598 * 2 ^ 59
def prefixEnd_5873598 : Nat := 4983230072969 + 3 ^ 40 * 5873598 * 2
def baseEnd_5873598 : Nat := 3015978945287015754512821

theorem tailTrace_5873598 : CollatzResearch.WordTrace tailWord_5873598 prefixEnd_5873598 3015978945287015754512821 := by
  unfold tailWord_5873598
  simp only [CollatzResearch.WordTrace]
  refine ⟨26778464821870631440024681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142818479049976701013464965 26778464821870631440024681)
  ·
    refine ⟨20083848616402973580018511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26778464821870631440024681 20083848616402973580018511)
    ·
      refine ⟨30125772924604460370027767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20083848616402973580018511 30125772924604460370027767)
      ·
        refine ⟨45188659386906690555041651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30125772924604460370027767 45188659386906690555041651)
        ·
          refine ⟨67782989080360035832562477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45188659386906690555041651 67782989080360035832562477)
          ·
            refine ⟨25418620905135013437210929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67782989080360035832562477 25418620905135013437210929)
            ·
              refine ⟨19063965678851260077908197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25418620905135013437210929 19063965678851260077908197)
              ·
                refine ⟨3574493564784611264607787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19063965678851260077908197 3574493564784611264607787)
                ·
                  refine ⟨5361740347176916896911681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574493564784611264607787 5361740347176916896911681)
                  ·
                    refine ⟨4021305260382687672683761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361740347176916896911681 4021305260382687672683761)
                    ·
                      refine ⟨3015978945287015754512821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021305260382687672683761 3015978945287015754512821)
                      ·
                        rfl

theorem cell23_5873598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_5873598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873598 prefixEnd_5873598 := by exact prefixLift 5873598
  have htrace : WordTrace (prefixWord ++ tailWord_5873598) baseStart_5873598 baseEnd_5873598 := by
    simpa [prefixWord, tailWord_5873598, baseEnd_5873598] using wordTrace_append hprefix tailTrace_5873598
  have hstable : (prefixWord ++ tailWord_5873598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873598).length < 2 ^ (prefixWord ++ tailWord_5873598).sum := by decide
  have hdescent : baseEnd_5873598 < baseStart_5873598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873714 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_5873714 : Nat := 118140960795 + 5873714 * 2 ^ 59
def prefixEnd_5873714 : Nat := 4983230072969 + 3 ^ 40 * 5873714 * 2
def baseEnd_5873714 : Nat := 3016038509042937300662287

theorem tailTrace_5873714 : CollatzResearch.WordTrace tailWord_5873714 prefixEnd_5873714 3016038509042937300662287 := by
  unfold tailWord_5873714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53557987360636200832855049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142821299628363202220946797 53557987360636200832855049)
  ·
    refine ⟨40168490520477150624641287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53557987360636200832855049 40168490520477150624641287)
    ·
      refine ⟨60252735780715725936961931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40168490520477150624641287 60252735780715725936961931)
      ·
        refine ⟨90379103671073588905442897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60252735780715725936961931 90379103671073588905442897)
        ·
          refine ⟨67784327753305191679082173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90379103671073588905442897 67784327753305191679082173)
          ·
            refine ⟨25419122907489446879655815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67784327753305191679082173 25419122907489446879655815)
            ·
              refine ⟨38128684361234170319483723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25419122907489446879655815 38128684361234170319483723)
              ·
                refine ⟨57193026541851255479225585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38128684361234170319483723 57193026541851255479225585)
                ·
                  refine ⟨42894769906388441609419189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57193026541851255479225585 42894769906388441609419189)
                  ·
                    refine ⟨4021384678723916400883049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42894769906388441609419189 4021384678723916400883049)
                    ·
                      refine ⟨3016038509042937300662287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021384678723916400883049 3016038509042937300662287)
                      ·
                        rfl

theorem cell23_5873714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_5873714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873714 prefixEnd_5873714 := by exact prefixLift 5873714
  have htrace : WordTrace (prefixWord ++ tailWord_5873714) baseStart_5873714 baseEnd_5873714 := by
    simpa [prefixWord, tailWord_5873714, baseEnd_5873714] using wordTrace_append hprefix tailTrace_5873714
  have hstable : (prefixWord ++ tailWord_5873714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873714).length < 2 ^ (prefixWord ++ tailWord_5873714).sum := by decide
  have hdescent : baseEnd_5873714 < baseStart_5873714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873717 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_5873717 : Nat := 118140960795 + 5873717 * 2 ^ 59
def prefixEnd_5873717 : Nat := 4983230072969 + 3 ^ 40 * 5873717 * 2
def baseEnd_5873717 : Nat := 3016040049484900788924773

theorem tailTrace_5873717 : CollatzResearch.WordTrace tailWord_5873717 prefixEnd_5873717 3016040049484900788924773 := by
  unfold tailWord_5873717
  simp only [CollatzResearch.WordTrace]
  refine ⟨214232058861533934843779405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142821372574355956562519603 214232058861533934843779405)
  ·
    refine ⟨80337022073075225566417277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214232058861533934843779405 80337022073075225566417277)
    ·
      refine ⟨30126383277403209587406479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80337022073075225566417277 30126383277403209587406479)
      ·
        refine ⟨45189574916104814381109719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30126383277403209587406479 45189574916104814381109719)
        ·
          refine ⟨67784362374157221571664579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45189574916104814381109719 67784362374157221571664579)
          ·
            refine ⟨101676543561235832357496869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67784362374157221571664579 101676543561235832357496869)
            ·
              refine ⟨19064351917731718567030663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101676543561235832357496869 19064351917731718567030663)
              ·
                refine ⟨28596527876597577850545995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19064351917731718567030663 28596527876597577850545995)
                ·
                  refine ⟨42894791814896366775818993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28596527876597577850545995 42894791814896366775818993)
                  ·
                    refine ⟨32171093861172275081864245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42894791814896366775818993 32171093861172275081864245)
                    ·
                      refine ⟨3016040049484900788924773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32171093861172275081864245 3016040049484900788924773)
                      ·
                        rfl

theorem cell23_5873717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_5873717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873717 prefixEnd_5873717 := by exact prefixLift 5873717
  have htrace : WordTrace (prefixWord ++ tailWord_5873717) baseStart_5873717 baseEnd_5873717 := by
    simpa [prefixWord, tailWord_5873717, baseEnd_5873717] using wordTrace_append hprefix tailTrace_5873717
  have hstable : (prefixWord ++ tailWord_5873717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873717).length < 2 ^ (prefixWord ++ tailWord_5873717).sum := by decide
  have hdescent : baseEnd_5873717 < baseStart_5873717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873727 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_5873727 : Nat := 118140960795 + 5873727 * 2 ^ 59
def prefixEnd_5873727 : Nat := 4983230072969 + 3 ^ 40 * 5873727 * 2
def baseEnd_5873727 : Nat := 3016045184291445749799727

theorem tailTrace_5873727 : CollatzResearch.WordTrace tailWord_5873727 prefixEnd_5873727 3016045184291445749799727 := by
  unfold tailWord_5873727
  simp only [CollatzResearch.WordTrace]
  refine ⟨214232423591497706551643435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142821615727665137701095623 214232423591497706551643435)
  ·
    refine ⟨321348635387246559827465153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214232423591497706551643435 321348635387246559827465153)
    ·
      refine ⟨241011476540434919870598865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321348635387246559827465153 241011476540434919870598865)
      ·
        refine ⟨180758607405326189902949149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241011476540434919870598865 180758607405326189902949149)
        ·
          refine ⟨67784477776997321213605931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180758607405326189902949149 67784477776997321213605931)
          ·
            refine ⟨101676716665495981820408897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67784477776997321213605931 101676716665495981820408897)
            ·
              refine ⟨76257537499121986365306673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101676716665495981820408897 76257537499121986365306673)
              ·
                refine ⟨57193153124341489773980005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76257537499121986365306673 57193153124341489773980005)
                ·
                  refine ⟨10723716210814029332621251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57193153124341489773980005 10723716210814029332621251)
                  ·
                    refine ⟨16085574316221043998931877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10723716210814029332621251 16085574316221043998931877)
                    ·
                      refine ⟨3016045184291445749799727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16085574316221043998931877 3016045184291445749799727)
                      ·
                        rfl

theorem cell23_5873727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_5873727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873727 prefixEnd_5873727 := by exact prefixLift 5873727
  have htrace : WordTrace (prefixWord ++ tailWord_5873727) baseStart_5873727 baseEnd_5873727 := by
    simpa [prefixWord, tailWord_5873727, baseEnd_5873727] using wordTrace_append hprefix tailTrace_5873727
  have hstable : (prefixWord ++ tailWord_5873727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873727).length < 2 ^ (prefixWord ++ tailWord_5873727).sum := by decide
  have hdescent : baseEnd_5873727 < baseStart_5873727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873764 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_5873764 : Nat := 118140960795 + 5873764 * 2 ^ 59
def prefixEnd_5873764 : Nat := 4983230072969 + 3 ^ 40 * 5873764 * 2
def baseEnd_5873764 : Nat := 3016064183075662105037057

theorem tailTrace_5873764 : CollatzResearch.WordTrace tailWord_5873764 prefixEnd_5873764 3016064183075662105037057 := by
  unfold tailWord_5873764
  simp only [CollatzResearch.WordTrace]
  refine ⟨107116886546181830935370173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142822515394909107913826897 107116886546181830935370173)
  ·
    refine ⟨40168832454818186600763815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107116886546181830935370173 40168832454818186600763815)
    ·
      refine ⟨60253248682227279901145723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40168832454818186600763815 60253248682227279901145723)
      ·
        refine ⟨90379873023340919851718585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60253248682227279901145723 90379873023340919851718585)
        ·
          refine ⟨67784904767505689888788939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90379873023340919851718585 67784904767505689888788939)
          ·
            refine ⟨101677357151258534833183409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67784904767505689888788939 101677357151258534833183409)
            ·
              refine ⟨76258017863443901124887557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101677357151258534833183409 76258017863443901124887557)
              ·
                refine ⟨14298378349395731460916417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76258017863443901124887557 14298378349395731460916417)
                ·
                  refine ⟨10723783762046798595687313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14298378349395731460916417 10723783762046798595687313)
                  ·
                    refine ⟨8042837821535098946765485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10723783762046798595687313 8042837821535098946765485)
                    ·
                      refine ⟨3016064183075662105037057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8042837821535098946765485 3016064183075662105037057)
                      ·
                        rfl

theorem cell23_5873764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_5873764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873764 prefixEnd_5873764 := by exact prefixLift 5873764
  have htrace : WordTrace (prefixWord ++ tailWord_5873764) baseStart_5873764 baseEnd_5873764 := by
    simpa [prefixWord, tailWord_5873764, baseEnd_5873764] using wordTrace_append hprefix tailTrace_5873764
  have hstable : (prefixWord ++ tailWord_5873764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873764).length < 2 ^ (prefixWord ++ tailWord_5873764).sum := by decide
  have hdescent : baseEnd_5873764 < baseStart_5873764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873767 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 8]
def baseStart_5873767 : Nat := 118140960795 + 5873767 * 2 ^ 59
def prefixEnd_5873767 : Nat := 4983230072969 + 3 ^ 40 * 5873767 * 2
def baseEnd_5873767 : Nat := 335118413724180621477727

theorem tailTrace_5873767 : CollatzResearch.WordTrace tailWord_5873767 prefixEnd_5873767 335118413724180621477727 := by
  unfold tailWord_5873767
  simp only [CollatzResearch.WordTrace]
  refine ⟨214233882511352793383099555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142822588340901862255399703 214233882511352793383099555)
  ·
    refine ⟨321350823767029190074649333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214233882511352793383099555 321350823767029190074649333)
    ·
      refine ⟨30126639728158986569498375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321350823767029190074649333 30126639728158986569498375)
      ·
        refine ⟨45189959592238479854247563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30126639728158986569498375 45189959592238479854247563)
        ·
          refine ⟨67784939388357719781371345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45189959592238479854247563 67784939388357719781371345)
          ·
            refine ⟨50838704541268289836028509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67784939388357719781371345 50838704541268289836028509)
            ·
              refine ⟨19064514202975608688510691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50838704541268289836028509 19064514202975608688510691)
              ·
                refine ⟨28596771304463413032766037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19064514202975608688510691 28596771304463413032766037)
                ·
                  refine ⟨335118413724180621477727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28596771304463413032766037 335118413724180621477727)
                  ·
                    rfl

theorem cell23_5873767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 8].length) (baseStart_5873767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873767 prefixEnd_5873767 := by exact prefixLift 5873767
  have htrace : WordTrace (prefixWord ++ tailWord_5873767) baseStart_5873767 baseEnd_5873767 := by
    simpa [prefixWord, tailWord_5873767, baseEnd_5873767] using wordTrace_append hprefix tailTrace_5873767
  have hstable : (prefixWord ++ tailWord_5873767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873767).length < 2 ^ (prefixWord ++ tailWord_5873767).sum := by decide
  have hdescent : baseEnd_5873767 < baseStart_5873767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873821 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_5873821 : Nat := 118140960795 + 5873821 * 2 ^ 59
def prefixEnd_5873821 : Nat := 4983230072969 + 3 ^ 40 * 5873821 * 2
def baseEnd_5873821 : Nat := 3016093451472968382024295

theorem tailTrace_5873821 : CollatzResearch.WordTrace tailWord_5873821 prefixEnd_5873821 3016093451472968382024295 := by
  unfold tailWord_5873821
  simp only [CollatzResearch.WordTrace]
  refine ⟨214235852053157160605565317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142823901368771440403710211 214235852053157160605565317)
  ·
    refine ⟨40169222259966967613543497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214235852053157160605565317 40169222259966967613543497)
    ·
      refine ⟨30126916694975225710157623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40169222259966967613543497 30126916694975225710157623)
      ·
        refine ⟨45190375042462838565236435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30126916694975225710157623 45190375042462838565236435)
        ·
          refine ⟨67785562563694257847854653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45190375042462838565236435 67785562563694257847854653)
          ·
            refine ⟨25419585961385346692945495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67785562563694257847854653 25419585961385346692945495)
            ·
              refine ⟨38129378942078020039418243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25419585961385346692945495 38129378942078020039418243)
              ·
                refine ⟨57194068413117030059127365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38129378942078020039418243 57194068413117030059127365)
                ·
                  refine ⟨10723887827459443136086381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57194068413117030059127365 10723887827459443136086381)
                  ·
                    refine ⟨4021457935297291176032393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10723887827459443136086381 4021457935297291176032393)
                    ·
                      refine ⟨3016093451472968382024295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021457935297291176032393 3016093451472968382024295)
                      ·
                        rfl

theorem cell23_5873821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_5873821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873821 prefixEnd_5873821 := by exact prefixLift 5873821
  have htrace : WordTrace (prefixWord ++ tailWord_5873821) baseStart_5873821 baseEnd_5873821 := by
    simpa [prefixWord, tailWord_5873821, baseEnd_5873821] using wordTrace_append hprefix tailTrace_5873821
  have hstable : (prefixWord ++ tailWord_5873821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873821).length < 2 ^ (prefixWord ++ tailWord_5873821).sum := by decide
  have hdescent : baseEnd_5873821 < baseStart_5873821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873822 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_5873822 : Nat := 118140960795 + 5873822 * 2 ^ 59
def prefixEnd_5873822 : Nat := 4983230072969 + 3 ^ 40 * 5873822 * 2
def baseEnd_5873822 : Nat := 1005364654984540959370597

theorem tailTrace_5873822 : CollatzResearch.WordTrace tailWord_5873822 prefixEnd_5873822 1005364654984540959370597 := by
  unfold tailWord_5873822
  simp only [CollatzResearch.WordTrace]
  refine ⟨26779486065769192222043965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142823925684102358517567813 26779486065769192222043965)
  ·
    refine ⟨10042307274663447083266487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26779486065769192222043965 10042307274663447083266487)
    ·
      refine ⟨15063460911995170624899731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10042307274663447083266487 15063460911995170624899731)
      ·
        refine ⟨22595191367992755937349597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15063460911995170624899731 22595191367992755937349597)
        ·
          refine ⟨8473196762997283476506099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22595191367992755937349597 8473196762997283476506099)
          ·
            refine ⟨12709795144495925214759149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473196762997283476506099 12709795144495925214759149)
            ·
              refine ⟨4766173179185971955534681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12709795144495925214759149 4766173179185971955534681)
              ·
                refine ⟨3574629884389478966651011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4766173179185971955534681 3574629884389478966651011)
                ·
                  refine ⟨5361944826584218449976517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574629884389478966651011 5361944826584218449976517)
                  ·
                    refine ⟨1005364654984540959370597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361944826584218449976517 1005364654984540959370597)
                    ·
                      rfl

theorem cell23_5873822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_5873822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873822 prefixEnd_5873822 := by exact prefixLift 5873822
  have htrace : WordTrace (prefixWord ++ tailWord_5873822) baseStart_5873822 baseEnd_5873822 := by
    simpa [prefixWord, tailWord_5873822, baseEnd_5873822] using wordTrace_append hprefix tailTrace_5873822
  have hstable : (prefixWord ++ tailWord_5873822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873822).length < 2 ^ (prefixWord ++ tailWord_5873822).sum := by decide
  have hdescent : baseEnd_5873822 < baseStart_5873822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873851 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 5, 2, 2]
def baseStart_5873851 : Nat := 118140960795 + 5873851 * 2 ^ 59
def prefixEnd_5873851 : Nat := 4983230072969 + 3 ^ 40 * 5873851 * 2
def baseEnd_5873851 : Nat := 3016108855892603264649157

theorem tailTrace_5873851 : CollatzResearch.WordTrace tailWord_5873851 prefixEnd_5873851 3016108855892603264649157 := by
  unfold tailWord_5873851
  simp only [CollatzResearch.WordTrace]
  refine ⟨214236946243048475729157407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142824630828698983819438271 214236946243048475729157407)
  ·
    refine ⟨321355419364572713593736111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214236946243048475729157407 321355419364572713593736111)
    ·
      refine ⟨482033129046859070390604167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321355419364572713593736111 482033129046859070390604167)
      ·
        refine ⟨723049693570288605585906251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482033129046859070390604167 723049693570288605585906251)
        ·
          refine ⟨1084574540355432908378859377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723049693570288605585906251 1084574540355432908378859377)
          ·
            refine ⟨813430905266574681284144533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1084574540355432908378859377 813430905266574681284144533)
            ·
              refine ⟨38129573684370688185194275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 813430905266574681284144533 38129573684370688185194275)
              ·
                refine ⟨57194360526556032277791413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38129573684370688185194275 57194360526556032277791413)
                ·
                  refine ⟨5361971299364628026042945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57194360526556032277791413 5361971299364628026042945)
                  ·
                    refine ⟨4021478474523471019532209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361971299364628026042945 4021478474523471019532209)
                    ·
                      refine ⟨3016108855892603264649157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021478474523471019532209 3016108855892603264649157)
                      ·
                        rfl

theorem cell23_5873851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 2, 2].length) (baseStart_5873851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873851 prefixEnd_5873851 := by exact prefixLift 5873851
  have htrace : WordTrace (prefixWord ++ tailWord_5873851) baseStart_5873851 baseEnd_5873851 := by
    simpa [prefixWord, tailWord_5873851, baseEnd_5873851] using wordTrace_append hprefix tailTrace_5873851
  have hstable : (prefixWord ++ tailWord_5873851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873851).length < 2 ^ (prefixWord ++ tailWord_5873851).sum := by decide
  have hdescent : baseEnd_5873851 < baseStart_5873851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873918 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5873918 : Nat := 118140960795 + 5873918 * 2 ^ 59
def prefixEnd_5873918 : Nat := 4983230072969 + 3 ^ 40 * 5873918 * 2
def baseEnd_5873918 : Nat := 3016143259096454502511349

theorem tailTrace_5873918 : CollatzResearch.WordTrace tailWord_5873918 prefixEnd_5873918 3016143259096454502511349 := by
  unfold tailWord_5873918
  simp only [CollatzResearch.WordTrace]
  refine ⟨26779923741725718271480801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142826259955870497447897605 26779923741725718271480801)
  ·
    refine ⟨20084942806294288703610601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26779923741725718271480801 20084942806294288703610601)
    ·
      refine ⟨15063707104720716527707951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20084942806294288703610601 15063707104720716527707951)
      ·
        refine ⟨22595560657081074791561927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15063707104720716527707951 22595560657081074791561927)
        ·
          refine ⟨33893340985621612187342891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22595560657081074791561927 33893340985621612187342891)
          ·
            refine ⟨50840011478432418281014337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33893340985621612187342891 50840011478432418281014337)
            ·
              refine ⟨38130008608824313710760753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50840011478432418281014337 38130008608824313710760753)
              ·
                refine ⟨28597506456618235283070565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38130008608824313710760753 28597506456618235283070565)
                ·
                  refine ⟨5362032460615919115575731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28597506456618235283070565 5362032460615919115575731)
                  ·
                    refine ⟨8043048690923878673363597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5362032460615919115575731 8043048690923878673363597)
                    ·
                      refine ⟨3016143259096454502511349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8043048690923878673363597 3016143259096454502511349)
                      ·
                        rfl

theorem cell23_5873918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5873918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873918 prefixEnd_5873918 := by exact prefixLift 5873918
  have htrace : WordTrace (prefixWord ++ tailWord_5873918) baseStart_5873918 baseEnd_5873918 := by
    simpa [prefixWord, tailWord_5873918, baseEnd_5873918] using wordTrace_append hprefix tailTrace_5873918
  have hstable : (prefixWord ++ tailWord_5873918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873918).length < 2 ^ (prefixWord ++ tailWord_5873918).sum := by decide
  have hdescent : baseEnd_5873918 < baseStart_5873918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873922 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_5873922 : Nat := 118140960795 + 5873922 * 2 ^ 59
def prefixEnd_5873922 : Nat := 4983230072969 + 3 ^ 40 * 5873922 * 2
def baseEnd_5873922 : Nat := 3016145313019072486861331

theorem tailTrace_5873922 : CollatzResearch.WordTrace tailWord_5873922 prefixEnd_5873922 3016145313019072486861331 := by
  unfold tailWord_5873922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53559883956447813713748005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142826357217194169903328013 53559883956447813713748005)
  ·
    refine ⟨10042478241833965071327751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53559883956447813713748005 10042478241833965071327751)
    ·
      refine ⟨15063717362750947606991627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10042478241833965071327751 15063717362750947606991627)
      ·
        refine ⟨22595576044126421410487441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15063717362750947606991627 22595576044126421410487441)
        ·
          refine ⟨16946682033094816057865581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22595576044126421410487441 16946682033094816057865581)
          ·
            refine ⟨6355005762410556021699593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16946682033094816057865581 6355005762410556021699593)
            ·
              refine ⟨4766254321807917016274695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6355005762410556021699593 4766254321807917016274695)
              ·
                refine ⟨7149381482711875524412043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766254321807917016274695 7149381482711875524412043)
                ·
                  refine ⟨10724072224067813286618065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149381482711875524412043 10724072224067813286618065)
                  ·
                    refine ⟨8043054168050859964963549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10724072224067813286618065 8043054168050859964963549)
                    ·
                      refine ⟨3016145313019072486861331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8043054168050859964963549 3016145313019072486861331)
                      ·
                        rfl

theorem cell23_5873922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_5873922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873922 prefixEnd_5873922 := by exact prefixLift 5873922
  have htrace : WordTrace (prefixWord ++ tailWord_5873922) baseStart_5873922 baseEnd_5873922 := by
    simpa [prefixWord, tailWord_5873922, baseEnd_5873922] using wordTrace_append hprefix tailTrace_5873922
  have hstable : (prefixWord ++ tailWord_5873922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873922).length < 2 ^ (prefixWord ++ tailWord_5873922).sum := by decide
  have hdescent : baseEnd_5873922 < baseStart_5873922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873934 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_5873934 : Nat := 118140960795 + 5873934 * 2 ^ 59
def prefixEnd_5873934 : Nat := 4983230072969 + 3 ^ 40 * 5873934 * 2
def baseEnd_5873934 : Nat := 1005383824928975479970425

theorem tailTrace_5873934 : CollatzResearch.WordTrace tailWord_5873934 prefixEnd_5873934 1005383824928975479970425 := by
  unfold tailWord_5873934
  simp only [CollatzResearch.WordTrace]
  refine ⟨26779996687718472613053607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142826649001165187269619237 26779996687718472613053607)
  ·
    refine ⟨40169995031577708919580411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26779996687718472613053607 40169995031577708919580411)
    ·
      refine ⟨60254992547366563379370617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40169995031577708919580411 60254992547366563379370617)
      ·
        refine ⟨45191244410524922534527963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60254992547366563379370617 45191244410524922534527963)
        ·
          refine ⟨67786866615787383801791945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45191244410524922534527963 67786866615787383801791945)
          ·
            refine ⟨50840149961840537851343959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67786866615787383801791945 50840149961840537851343959)
            ·
              refine ⟨76260224942760806777015939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50840149961840537851343959 76260224942760806777015939)
              ·
                refine ⟨114390337414141210165523909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76260224942760806777015939 114390337414141210165523909)
                ·
                  refine ⟨21448188265151476906035733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114390337414141210165523909 21448188265151476906035733)
                  ·
                    refine ⟨1005383824928975479970425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21448188265151476906035733 1005383824928975479970425)
                    ·
                      rfl

theorem cell23_5873934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_5873934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873934 prefixEnd_5873934 := by exact prefixLift 5873934
  have htrace : WordTrace (prefixWord ++ tailWord_5873934) baseStart_5873934 baseEnd_5873934 := by
    simpa [prefixWord, tailWord_5873934, baseEnd_5873934] using wordTrace_append hprefix tailTrace_5873934
  have hstable : (prefixWord ++ tailWord_5873934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873934).length < 2 ^ (prefixWord ++ tailWord_5873934).sum := by decide
  have hdescent : baseEnd_5873934 < baseStart_5873934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873941 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_5873941 : Nat := 118140960795 + 5873941 * 2 ^ 59
def prefixEnd_5873941 : Nat := 4983230072969 + 3 ^ 40 * 5873941 * 2
def baseEnd_5873941 : Nat := 3016155069151507912523743

theorem tailTrace_5873941 : CollatzResearch.WordTrace tailWord_5873941 prefixEnd_5873941 3016155069151507912523743 := by
  unfold tailWord_5873941
  simp only [CollatzResearch.WordTrace]
  refine ⟨214240228812722421099933677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142826819208481614066622451 214240228812722421099933677)
  ·
    refine ⟨80340085804770907912475129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214240228812722421099933677 80340085804770907912475129)
    ·
      refine ⟨60255064353578180934356347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80340085804770907912475129 60255064353578180934356347)
      ·
        refine ⟨90382596530367271401534521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60255064353578180934356347 90382596530367271401534521)
        ·
          refine ⟨67786947397775453551150891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90382596530367271401534521 67786947397775453551150891)
          ·
            refine ⟨101680421096663180326726337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67786947397775453551150891 101680421096663180326726337)
            ·
              refine ⟨76260315822497385245044753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101680421096663180326726337 76260315822497385245044753)
              ·
                refine ⟨57195236866873038933783565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76260315822497385245044753 57195236866873038933783565)
                ·
                  refine ⟨21448213825077389600168837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57195236866873038933783565 21448213825077389600168837)
                  ·
                    refine ⟨4021540092202010550031657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21448213825077389600168837 4021540092202010550031657)
                    ·
                      refine ⟨3016155069151507912523743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021540092202010550031657 3016155069151507912523743)
                      ·
                        rfl

theorem cell23_5873941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_5873941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873941 prefixEnd_5873941 := by exact prefixLift 5873941
  have htrace : WordTrace (prefixWord ++ tailWord_5873941) baseStart_5873941 baseEnd_5873941 := by
    simpa [prefixWord, tailWord_5873941, baseEnd_5873941] using wordTrace_append hprefix tailTrace_5873941
  have hstable : (prefixWord ++ tailWord_5873941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873941).length < 2 ^ (prefixWord ++ tailWord_5873941).sum := by decide
  have hdescent : baseEnd_5873941 < baseStart_5873941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873962 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5873962 : Nat := 118140960795 + 5873962 * 2 ^ 59
def prefixEnd_5873962 : Nat := 4983230072969 + 3 ^ 40 * 5873962 * 2
def baseEnd_5873962 : Nat := 3016165852245252330361147

theorem tailTrace_5873962 : CollatzResearch.WordTrace tailWord_5873962 prefixEnd_5873962 3016165852245252330361147 := by
  unfold tailWord_5873962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53560248686411585421612035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142827329830430894457632093 53560248686411585421612035)
  ·
    refine ⟨80340373029617378132418053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53560248686411585421612035 80340373029617378132418053)
    ·
      refine ⟨15063819943053258399828385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80340373029617378132418053 15063819943053258399828385)
      ·
        refine ⟨11297864957289943799871289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15063819943053258399828385 11297864957289943799871289)
        ·
          refine ⟨8473398717967457849903467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11297864957289943799871289 8473398717967457849903467)
          ·
            refine ⟨12710098076951186774855201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473398717967457849903467 12710098076951186774855201)
            ·
              refine ⟨9532573557713390081141401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12710098076951186774855201 9532573557713390081141401)
              ·
                refine ⟨7149430168285042560856051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9532573557713390081141401 7149430168285042560856051)
                ·
                  refine ⟨10724145252427563841284077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149430168285042560856051 10724145252427563841284077)
                  ·
                    refine ⟨4021554469660336440481529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10724145252427563841284077 4021554469660336440481529)
                    ·
                      refine ⟨3016165852245252330361147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021554469660336440481529 3016165852245252330361147)
                      ·
                        rfl

theorem cell23_5873962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5873962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873962 prefixEnd_5873962 := by exact prefixLift 5873962
  have htrace : WordTrace (prefixWord ++ tailWord_5873962) baseStart_5873962 baseEnd_5873962 := by
    simpa [prefixWord, tailWord_5873962, baseEnd_5873962] using wordTrace_append hprefix tailTrace_5873962
  have hstable : (prefixWord ++ tailWord_5873962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873962).length < 2 ^ (prefixWord ++ tailWord_5873962).sum := by decide
  have hdescent : baseEnd_5873962 < baseStart_5873962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5873964 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 7]
def baseStart_5873964 : Nat := 118140960795 + 5873964 * 2 ^ 59
def prefixEnd_5873964 : Nat := 4983230072969 + 3 ^ 40 * 5873964 * 2
def baseEnd_5873964 : Nat := 335129653245173480281793

theorem tailTrace_5873964 : CollatzResearch.WordTrace tailWord_5873964 prefixEnd_5873964 335129653245173480281793 := by
  unfold tailWord_5873964
  simp only [CollatzResearch.WordTrace]
  refine ⟨107120533845819548014010473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142827378461092730685347297 107120533845819548014010473)
  ·
    refine ⟨80340400384364661010507855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107120533845819548014010473 80340400384364661010507855)
    ·
      refine ⟨120510600576546991515761783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80340400384364661010507855 120510600576546991515761783)
      ·
        refine ⟨180765900864820487273642675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120510600576546991515761783 180765900864820487273642675)
        ·
          refine ⟨271148851297230730910464013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180765900864820487273642675 271148851297230730910464013)
          ·
            refine ⟨101680819236461524091424005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271148851297230730910464013 101680819236461524091424005)
            ·
              refine ⟨19065153606836535767142001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101680819236461524091424005 19065153606836535767142001)
              ·
                refine ⟨14298865205127401825356501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19065153606836535767142001 14298865205127401825356501)
                ·
                  refine ⟨335129653245173480281793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14298865205127401825356501 335129653245173480281793)
                  ·
                    rfl

theorem cell23_5873964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_5873964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5873964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5873964 prefixEnd_5873964 := by exact prefixLift 5873964
  have htrace : WordTrace (prefixWord ++ tailWord_5873964) baseStart_5873964 baseEnd_5873964 := by
    simpa [prefixWord, tailWord_5873964, baseEnd_5873964] using wordTrace_append hprefix tailTrace_5873964
  have hstable : (prefixWord ++ tailWord_5873964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5873964).length < 2 ^ (prefixWord ++ tailWord_5873964).sum := by decide
  have hdescent : baseEnd_5873964 < baseStart_5873964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5873964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874028 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_5874028 : Nat := 118140960795 + 5874028 * 2 ^ 59
def prefixEnd_5874028 : Nat := 4983230072969 + 3 ^ 40 * 5874028 * 2
def baseEnd_5874028 : Nat := 1005399913989483024045281

theorem tailTrace_5874028 : CollatzResearch.WordTrace tailWord_5874028 prefixEnd_5874028 1005399913989483024045281 := by
  unfold tailWord_5874028
  simp only [CollatzResearch.WordTrace]
  refine ⟨107121700981703617479175369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142828934642271489972233825 107121700981703617479175369)
  ·
    refine ⟨80341275736277713109381527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107121700981703617479175369 80341275736277713109381527)
    ·
      refine ⟨120511913604416569664072291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80341275736277713109381527 120511913604416569664072291)
      ·
        refine ⟨180767870406624854496108437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120511913604416569664072291 180767870406624854496108437)
        ·
          refine ⟨8473493925310540054505083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180767870406624854496108437 8473493925310540054505083)
          ·
            refine ⟨12710240887965810081757625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473493925310540054505083 12710240887965810081757625)
            ·
              refine ⟨9532680665974357561318219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12710240887965810081757625 9532680665974357561318219)
              ·
                refine ⟨14299020998961536341977329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9532680665974357561318219 14299020998961536341977329)
                ·
                  refine ⟨10724265749221152256482997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14299020998961536341977329 10724265749221152256482997)
                  ·
                    refine ⟨1005399913989483024045281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10724265749221152256482997 1005399913989483024045281)
                    ·
                      rfl

theorem cell23_5874028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_5874028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874028 prefixEnd_5874028 := by exact prefixLift 5874028
  have htrace : WordTrace (prefixWord ++ tailWord_5874028) baseStart_5874028 baseEnd_5874028 := by
    simpa [prefixWord, tailWord_5874028, baseEnd_5874028] using wordTrace_append hprefix tailTrace_5874028
  have hstable : (prefixWord ++ tailWord_5874028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874028).length < 2 ^ (prefixWord ++ tailWord_5874028).sum := by decide
  have hdescent : baseEnd_5874028 < baseStart_5874028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874031 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 6, 2]
def baseStart_5874031 : Nat := 118140960795 + 5874031 * 2 ^ 59
def prefixEnd_5874031 : Nat := 4983230072969 + 3 ^ 40 * 5874031 * 2
def baseEnd_5874031 : Nat := 3016201282410412560398329

theorem tailTrace_5874031 : CollatzResearch.WordTrace tailWord_5874031 prefixEnd_5874031 3016201282410412560398329 := by
  unfold tailWord_5874031
  simp only [CollatzResearch.WordTrace]
  refine ⟨214243511382396366470709947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142829007588264244313806631 214243511382396366470709947)
  ·
    refine ⟨321365267073594549706064921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214243511382396366470709947 321365267073594549706064921)
    ·
      refine ⟨241023950305195912279548691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321365267073594549706064921 241023950305195912279548691)
      ·
        refine ⟨361535925457793868419323037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241023950305195912279548691 361535925457793868419323037)
        ·
          refine ⟨135575972046672700657246139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361535925457793868419323037 135575972046672700657246139)
          ·
            refine ⟨203363958070009050985869209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135575972046672700657246139 203363958070009050985869209)
            ·
              refine ⟨152522968552506788239401907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203363958070009050985869209 152522968552506788239401907)
              ·
                refine ⟨228784452828760182359102861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152522968552506788239401907 228784452828760182359102861)
                ·
                  refine ⟨85794169810785068384663573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228784452828760182359102861 85794169810785068384663573)
                  ·
                    refine ⟨4021601709880550080531105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85794169810785068384663573 4021601709880550080531105)
                    ·
                      refine ⟨3016201282410412560398329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021601709880550080531105 3016201282410412560398329)
                      ·
                        rfl

theorem cell23_5874031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6, 2].length) (baseStart_5874031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874031 prefixEnd_5874031 := by exact prefixLift 5874031
  have htrace : WordTrace (prefixWord ++ tailWord_5874031) baseStart_5874031 baseEnd_5874031 := by
    simpa [prefixWord, tailWord_5874031, baseEnd_5874031] using wordTrace_append hprefix tailTrace_5874031
  have hstable : (prefixWord ++ tailWord_5874031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874031).length < 2 ^ (prefixWord ++ tailWord_5874031).sum := by decide
  have hdescent : baseEnd_5874031 < baseStart_5874031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874071 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 6]
def baseStart_5874071 : Nat := 118140960795 + 5874071 * 2 ^ 59
def prefixEnd_5874071 : Nat := 4983230072969 + 3 ^ 40 * 5874071 * 2
def baseEnd_5874071 : Nat := 335135757959621378210905

theorem tailTrace_5874071 : CollatzResearch.WordTrace tailWord_5874071 prefixEnd_5874071 335135757959621378210905 := by
  unfold tailWord_5874071
  simp only [CollatzResearch.WordTrace]
  refine ⟨214244970302251453302166067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142829980201500968868110711 214244970302251453302166067)
  ·
    refine ⟨321367455453377179953249101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214244970302251453302166067 321367455453377179953249101)
    ·
      refine ⟨120512795795016442482468413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321367455453377179953249101 120512795795016442482468413)
      ·
        refine ⟨45192298423131165930925655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120512795795016442482468413 45192298423131165930925655)
        ·
          refine ⟨67788447634696748896388483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45192298423131165930925655 67788447634696748896388483)
          ·
            refine ⟨101682671452045123344582725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67788447634696748896388483 101682671452045123344582725)
            ·
              refine ⟨19065500897258460627109261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101682671452045123344582725 19065500897258460627109261)
              ·
                refine ⟨7149562836471922735165973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19065500897258460627109261 7149562836471922735165973)
                ·
                  refine ⟨335135757959621378210905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7149562836471922735165973 335135757959621378210905)
                  ·
                    rfl

theorem cell23_5874071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 6].length) (baseStart_5874071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874071 prefixEnd_5874071 := by exact prefixLift 5874071
  have htrace : WordTrace (prefixWord ++ tailWord_5874071) baseStart_5874071 baseEnd_5874071 := by
    simpa [prefixWord, tailWord_5874071, baseEnd_5874071] using wordTrace_append hprefix tailTrace_5874071
  have hstable : (prefixWord ++ tailWord_5874071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874071).length < 2 ^ (prefixWord ++ tailWord_5874071).sum := by decide
  have hdescent : baseEnd_5874071 < baseStart_5874071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874098 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_5874098 : Nat := 118140960795 + 5874098 * 2 ^ 59
def prefixEnd_5874098 : Nat := 4983230072969 + 3 ^ 40 * 5874098 * 2
def baseEnd_5874098 : Nat := 3016235685614263798260521

theorem tailTrace_5874098 : CollatzResearch.WordTrace tailWord_5874098 prefixEnd_5874098 3016235685614263798260521 := by
  unfold tailWord_5874098
  simp only [CollatzResearch.WordTrace]
  refine ⟨53561488768288409228349737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142830636715435757942265965 53561488768288409228349737)
  ·
    refine ⟨40171116576216306921262303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53561488768288409228349737 40171116576216306921262303)
    ·
      refine ⟨60256674864324460381893455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40171116576216306921262303 60256674864324460381893455)
      ·
        refine ⟨90385012296486690572840183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60256674864324460381893455 90385012296486690572840183)
        ·
          refine ⟨135577518444730035859260275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90385012296486690572840183 135577518444730035859260275)
          ·
            refine ⟨203366277667095053788890413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135577518444730035859260275 203366277667095053788890413)
            ·
              refine ⟨76262354125160645170833905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203366277667095053788890413 76262354125160645170833905)
              ·
                refine ⟨57196765593870483878125429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76262354125160645170833905 57196765593870483878125429)
                ·
                  refine ⟨5362196774425357863574259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57196765593870483878125429 5362196774425357863574259)
                  ·
                    refine ⟨8043295161638036795361389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5362196774425357863574259 8043295161638036795361389)
                    ·
                      refine ⟨3016235685614263798260521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8043295161638036795361389 3016235685614263798260521)
                      ·
                        rfl

theorem cell23_5874098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_5874098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874098 prefixEnd_5874098 := by exact prefixLift 5874098
  have htrace : WordTrace (prefixWord ++ tailWord_5874098) baseStart_5874098 baseEnd_5874098 := by
    simpa [prefixWord, tailWord_5874098, baseEnd_5874098] using wordTrace_append hprefix tailTrace_5874098
  have hstable : (prefixWord ++ tailWord_5874098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874098).length < 2 ^ (prefixWord ++ tailWord_5874098).sum := by decide
  have hdescent : baseEnd_5874098 < baseStart_5874098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874121 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_5874121 : Nat := 118140960795 + 5874121 * 2 ^ 59
def prefixEnd_5874121 : Nat := 4983230072969 + 3 ^ 40 * 5874121 * 2
def baseEnd_5874121 : Nat := 3016247495669317208272915

theorem tailTrace_5874121 : CollatzResearch.WordTrace tailWord_5874121 prefixEnd_5874121 3016247495669317208272915 := by
  unfold tailWord_5874121
  simp only [CollatzResearch.WordTrace]
  refine ⟨214246793952070311841486217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142831195968046874560990811 214246793952070311841486217)
  ·
    refine ⟨160685095464052733881114663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214246793952070311841486217 160685095464052733881114663)
    ·
      refine ⟨241027643196079100821671995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160685095464052733881114663 241027643196079100821671995)
      ·
        refine ⟨361541464794118651232507993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241027643196079100821671995 361541464794118651232507993)
        ·
          refine ⟨271156098595588988424380995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361541464794118651232507993 271156098595588988424380995)
          ·
            refine ⟨406734147893383482636571493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271156098595588988424380995 406734147893383482636571493)
            ·
              refine ⟨76262652730009402994357155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406734147893383482636571493 76262652730009402994357155)
              ·
                refine ⟨114393979095014104491535733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76262652730009402994357155 114393979095014104491535733)
                ·
                  refine ⟨10724435540157572296081475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114393979095014104491535733 10724435540157572296081475)
                  ·
                    refine ⟨16086653310236358444122213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10724435540157572296081475 16086653310236358444122213)
                    ·
                      refine ⟨3016247495669317208272915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16086653310236358444122213 3016247495669317208272915)
                      ·
                        rfl

theorem cell23_5874121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_5874121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874121 prefixEnd_5874121 := by exact prefixLift 5874121
  have htrace : WordTrace (prefixWord ++ tailWord_5874121) baseStart_5874121 baseEnd_5874121 := by
    simpa [prefixWord, tailWord_5874121, baseEnd_5874121] using wordTrace_append hprefix tailTrace_5874121
  have hstable : (prefixWord ++ tailWord_5874121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874121).length < 2 ^ (prefixWord ++ tailWord_5874121).sum := by decide
  have hdescent : baseEnd_5874121 < baseStart_5874121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874138 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2]
def baseStart_5874138 : Nat := 118140960795 + 5874138 * 2 ^ 59
def prefixEnd_5874138 : Nat := 4983230072969 + 3 ^ 40 * 5874138 * 2
def baseEnd_5874138 : Nat := 3016256224840443641760337

theorem tailTrace_5874138 : CollatzResearch.WordTrace tailWord_5874138 prefixEnd_5874138 3016256224840443641760337 := by
  unfold tailWord_5874138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53561853498252180936213767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142831609328672482496570045 53561853498252180936213767)
  ·
    refine ⟨80342780247378271404320651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53561853498252180936213767 80342780247378271404320651)
    ·
      refine ⟨120514170371067407106480977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80342780247378271404320651 120514170371067407106480977)
      ·
        refine ⟨90385627778300555329860733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120514170371067407106480977 90385627778300555329860733)
        ·
          refine ⟨33894610416862708248697775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90385627778300555329860733 33894610416862708248697775)
          ·
            refine ⟨50841915625294062373046663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33894610416862708248697775 50841915625294062373046663)
            ·
              refine ⟨76262873437941093559569995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50841915625294062373046663 76262873437941093559569995)
              ·
                refine ⟨114394310156911640339354993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76262873437941093559569995 114394310156911640339354993)
                ·
                  refine ⟨85795732617683730254516245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114394310156911640339354993 85795732617683730254516245)
                  ·
                    refine ⟨4021674966453924855680449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85795732617683730254516245 4021674966453924855680449)
                    ·
                      refine ⟨3016256224840443641760337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021674966453924855680449 3016256224840443641760337)
                      ·
                        rfl

theorem cell23_5874138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_5874138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874138 prefixEnd_5874138 := by exact prefixLift 5874138
  have htrace : WordTrace (prefixWord ++ tailWord_5874138) baseStart_5874138 baseEnd_5874138 := by
    simpa [prefixWord, tailWord_5874138, baseEnd_5874138] using wordTrace_append hprefix tailTrace_5874138
  have hstable : (prefixWord ++ tailWord_5874138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874138).length < 2 ^ (prefixWord ++ tailWord_5874138).sum := by decide
  have hdescent : baseEnd_5874138 < baseStart_5874138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874158 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_5874158 : Nat := 118140960795 + 5874158 * 2 ^ 59
def prefixEnd_5874158 : Nat := 4983230072969 + 3 ^ 40 * 5874158 * 2
def baseEnd_5874158 : Nat := 3016266494453533563510245

theorem tailTrace_5874158 : CollatzResearch.WordTrace tailWord_5874158 prefixEnd_5874158 3016266494453533563510245 := by
  unfold tailWord_5874158
  simp only [CollatzResearch.WordTrace]
  refine ⟨26781017931617033395072891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142832095635290844773722085 26781017931617033395072891)
  ·
    refine ⟨40171526897425550092609337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26781017931617033395072891 40171526897425550092609337)
    ·
      refine ⟨30128645173069162569457003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40171526897425550092609337 30128645173069162569457003)
      ·
        refine ⟨45192967759603743854185505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30128645173069162569457003 45192967759603743854185505)
        ·
          refine ⟨33894725819702807890639129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45192967759603743854185505 33894725819702807890639129)
          ·
            refine ⟨25421044364777105917979347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33894725819702807890639129 25421044364777105917979347)
            ·
              refine ⟨38131566547165658876969021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25421044364777105917979347 38131566547165658876969021)
              ·
                refine ⟨14299337455187122078863383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38131566547165658876969021 14299337455187122078863383)
                ·
                  refine ⟨21449006182780683118295075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14299337455187122078863383 21449006182780683118295075)
                  ·
                    refine ⟨32173509274171024677442613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21449006182780683118295075 32173509274171024677442613)
                    ·
                      refine ⟨3016266494453533563510245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32173509274171024677442613 3016266494453533563510245)
                      ·
                        rfl

theorem cell23_5874158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_5874158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874158 prefixEnd_5874158 := by exact prefixLift 5874158
  have htrace : WordTrace (prefixWord ++ tailWord_5874158) baseStart_5874158 baseEnd_5874158 := by
    simpa [prefixWord, tailWord_5874158, baseEnd_5874158] using wordTrace_append hprefix tailTrace_5874158
  have hstable : (prefixWord ++ tailWord_5874158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874158).length < 2 ^ (prefixWord ++ tailWord_5874158).sum := by decide
  have hdescent : baseEnd_5874158 < baseStart_5874158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874171 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 3]
def baseStart_5874171 : Nat := 118140960795 + 5874171 * 2 ^ 59
def prefixEnd_5874171 : Nat := 4983230072969 + 3 ^ 40 * 5874171 * 2
def baseEnd_5874171 : Nat := 3016273169702042012647685

theorem tailTrace_5874171 : CollatzResearch.WordTrace tailWord_5874171 prefixEnd_5874171 3016273169702042012647685 := by
  unfold tailWord_5874171
  simp only [CollatzResearch.WordTrace]
  refine ⟨214248617601889170380806367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142832411734592780253870911 214248617601889170380806367)
  ·
    refine ⟨321372926402833755571209551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214248617601889170380806367 321372926402833755571209551)
    ·
      refine ⟨482059389604250633356814327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321372926402833755571209551 482059389604250633356814327)
      ·
        refine ⟨723089084406375950035221491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482059389604250633356814327 723089084406375950035221491)
        ·
          refine ⟨1084633626609563925052832237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723089084406375950035221491 1084633626609563925052832237)
          ·
            refine ⟨406737609978586471894812089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084633626609563925052832237 406737609978586471894812089)
            ·
              refine ⟨305053207483939853921109067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406737609978586471894812089 305053207483939853921109067)
              ·
                refine ⟨457579811225909780881663601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305053207483939853921109067 457579811225909780881663601)
                ·
                  refine ⟨343184858419432335661247701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457579811225909780881663601 343184858419432335661247701)
                  ·
                    refine ⟨8043395119205445367060493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 343184858419432335661247701 8043395119205445367060493)
                    ·
                      refine ⟨3016273169702042012647685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8043395119205445367060493 3016273169702042012647685)
                      ·
                        rfl

theorem cell23_5874171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 3].length) (baseStart_5874171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874171 prefixEnd_5874171 := by exact prefixLift 5874171
  have htrace : WordTrace (prefixWord ++ tailWord_5874171) baseStart_5874171 baseEnd_5874171 := by
    simpa [prefixWord, tailWord_5874171, baseEnd_5874171] using wordTrace_append hprefix tailTrace_5874171
  have hstable : (prefixWord ++ tailWord_5874171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874171).length < 2 ^ (prefixWord ++ tailWord_5874171).sum := by decide
  have hdescent : baseEnd_5874171 < baseStart_5874171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874189 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5874189 : Nat := 118140960795 + 5874189 * 2 ^ 59
def prefixEnd_5874189 : Nat := 4983230072969 + 3 ^ 40 * 5874189 * 2
def baseEnd_5874189 : Nat := 3016282412353822942222603

theorem tailTrace_5874189 : CollatzResearch.WordTrace tailWord_5874189 prefixEnd_5874189 3016282412353822942222603 := by
  unfold tailWord_5874189
  simp only [CollatzResearch.WordTrace]
  refine ⟨214249274115823959454961621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142832849410549306303307747 214249274115823959454961621)
  ·
    refine ⟨5021467362089624049725663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 214249274115823959454961621 5021467362089624049725663)
    ·
      refine ⟨7532201043134436074588495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5021467362089624049725663 7532201043134436074588495)
      ·
        refine ⟨11298301564701654111882743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7532201043134436074588495 11298301564701654111882743)
        ·
          refine ⟨16947452347052481167824115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11298301564701654111882743 16947452347052481167824115)
          ·
            refine ⟨25421178520578721751736173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16947452347052481167824115 25421178520578721751736173)
            ·
              refine ⟨9532941945217020656901065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25421178520578721751736173 9532941945217020656901065)
              ·
                refine ⟨7149706458912765492675799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9532941945217020656901065 7149706458912765492675799)
                ·
                  refine ⟨10724559688369148239013699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149706458912765492675799 10724559688369148239013699)
                  ·
                    refine ⟨16086839532553722358520549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10724559688369148239013699 16086839532553722358520549)
                    ·
                      refine ⟨3016282412353822942222603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16086839532553722358520549 3016282412353822942222603)
                      ·
                        rfl

theorem cell23_5874189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5874189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874189 prefixEnd_5874189 := by exact prefixLift 5874189
  have htrace : WordTrace (prefixWord ++ tailWord_5874189) baseStart_5874189 baseEnd_5874189 := by
    simpa [prefixWord, tailWord_5874189, baseEnd_5874189] using wordTrace_append hprefix tailTrace_5874189
  have hstable : (prefixWord ++ tailWord_5874189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874189).length < 2 ^ (prefixWord ++ tailWord_5874189).sum := by decide
  have hdescent : baseEnd_5874189 < baseStart_5874189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874205 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_5874205 : Nat := 118140960795 + 5874205 * 2 ^ 59
def prefixEnd_5874205 : Nat := 4983230072969 + 3 ^ 40 * 5874205 * 2
def baseEnd_5874205 : Nat := 3016290628044294879622529

theorem tailTrace_5874205 : CollatzResearch.WordTrace tailWord_5874205 prefixEnd_5874205 3016290628044294879622529 := by
  unfold tailWord_5874205
  simp only [CollatzResearch.WordTrace]
  refine ⟨214249857683765994187544069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142833238455843996125029379 214249857683765994187544069)
  ·
    refine ⟨40171848315706123910164513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214249857683765994187544069 40171848315706123910164513)
    ·
      refine ⟨30128886236779592932623385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40171848315706123910164513 30128886236779592932623385)
      ·
        refine ⟨22596664677584694699467539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30128886236779592932623385 22596664677584694699467539)
        ·
          refine ⟨33894997016377042049201309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22596664677584694699467539 33894997016377042049201309)
          ·
            refine ⟨12710623881141390768450491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33894997016377042049201309 12710623881141390768450491)
            ·
              refine ⟨19065935821712086152675737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12710623881141390768450491 19065935821712086152675737)
              ·
                refine ⟨14299451866284064614506803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19065935821712086152675737 14299451866284064614506803)
                ·
                  refine ⟨21449177799426096921760205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14299451866284064614506803 21449177799426096921760205)
                  ·
                    refine ⟨8043441674784786345660077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21449177799426096921760205 8043441674784786345660077)
                    ·
                      refine ⟨3016290628044294879622529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8043441674784786345660077 3016290628044294879622529)
                      ·
                        rfl

theorem cell23_5874205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_5874205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874205 prefixEnd_5874205 := by exact prefixLift 5874205
  have htrace : WordTrace (prefixWord ++ tailWord_5874205) baseStart_5874205 baseEnd_5874205 := by
    simpa [prefixWord, tailWord_5874205, baseEnd_5874205] using wordTrace_append hprefix tailTrace_5874205
  have hstable : (prefixWord ++ tailWord_5874205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874205).length < 2 ^ (prefixWord ++ tailWord_5874205).sum := by decide
  have hdescent : baseEnd_5874205 < baseStart_5874205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874245 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 1, 4, 2]
def baseStart_5874245 : Nat := 118140960795 + 5874245 * 2 ^ 59
def prefixEnd_5874245 : Nat := 4983230072969 + 3 ^ 40 * 5874245 * 2
def baseEnd_5874245 : Nat := 3016311167270474723122345

theorem tailTrace_5874245 : CollatzResearch.WordTrace tailWord_5874245 prefixEnd_5874245 3016311167270474723122345 := by
  unfold tailWord_5874245
  simp only [CollatzResearch.WordTrace]
  refine ⟨214251316603621081019000189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142834211069080720679333459 214251316603621081019000189)
  ·
    refine ⟨80344243726357905382125071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214251316603621081019000189 80344243726357905382125071)
    ·
      refine ⟨120516365589536858073187607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80344243726357905382125071 120516365589536858073187607)
      ·
        refine ⟨180774548384305287109781411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120516365589536858073187607 180774548384305287109781411)
        ·
          refine ⟨271161822576457930664672117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180774548384305287109781411 271161822576457930664672117)
          ·
            refine ⟨25421420866542930999813011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271161822576457930664672117 25421420866542930999813011)
            ·
              refine ⟨38132131299814396499719517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25421420866542930999813011 38132131299814396499719517)
              ·
                refine ⟨14299549237430398687394819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38132131299814396499719517 14299549237430398687394819)
                ·
                  refine ⟨21449323856145598031092229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14299549237430398687394819 21449323856145598031092229)
                  ·
                    refine ⟨4021748223027299630829793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21449323856145598031092229 4021748223027299630829793)
                    ·
                      refine ⟨3016311167270474723122345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021748223027299630829793 3016311167270474723122345)
                      ·
                        rfl

theorem cell23_5874245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_5874245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874245 prefixEnd_5874245 := by exact prefixLift 5874245
  have htrace : WordTrace (prefixWord ++ tailWord_5874245) baseStart_5874245 baseEnd_5874245 := by
    simpa [prefixWord, tailWord_5874245, baseEnd_5874245] using wordTrace_append hprefix tailTrace_5874245
  have hstable : (prefixWord ++ tailWord_5874245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874245).length < 2 ^ (prefixWord ++ tailWord_5874245).sum := by decide
  have hdescent : baseEnd_5874245 < baseStart_5874245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874251 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 9]
def baseStart_5874251 : Nat := 118140960795 + 5874251 * 2 ^ 59
def prefixEnd_5874251 : Nat := 4983230072969 + 3 ^ 40 * 5874251 * 2
def baseEnd_5874251 : Nat := 335146027572711299960813

theorem tailTrace_5874251 : CollatzResearch.WordTrace tailWord_5874251 prefixEnd_5874251 335146027572711299960813 := by
  unfold tailWord_5874251
  simp only [CollatzResearch.WordTrace]
  refine ⟨214251535441599344043718607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142834356961066229362479071 214251535441599344043718607)
  ·
    refine ⟨321377303162399016065577911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214251535441599344043718607 321377303162399016065577911)
    ·
      refine ⟨482065954743598524098366867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321377303162399016065577911 482065954743598524098366867)
      ·
        refine ⟨723098932115397786147550301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482065954743598524098366867 723098932115397786147550301)
        ·
          refine ⟨271162099543274169805331363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 723098932115397786147550301 271162099543274169805331363)
          ·
            refine ⟨406743149314911254707997045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271162099543274169805331363 406743149314911254707997045)
            ·
              refine ⟨38132170248272930128874723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 406743149314911254707997045 38132170248272930128874723)
              ·
                refine ⟨57198255372409395193312085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38132170248272930128874723 57198255372409395193312085)
                ·
                  refine ⟨335146027572711299960813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57198255372409395193312085 335146027572711299960813)
                  ·
                    rfl

theorem cell23_5874251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 9].length) (baseStart_5874251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874251 prefixEnd_5874251 := by exact prefixLift 5874251
  have htrace : WordTrace (prefixWord ++ tailWord_5874251) baseStart_5874251 baseEnd_5874251 := by
    simpa [prefixWord, tailWord_5874251, baseEnd_5874251] using wordTrace_append hprefix tailTrace_5874251
  have hstable : (prefixWord ++ tailWord_5874251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874251).length < 2 ^ (prefixWord ++ tailWord_5874251).sum := by decide
  have hdescent : baseEnd_5874251 < baseStart_5874251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874258 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_5874258 : Nat := 118140960795 + 5874258 * 2 ^ 59
def prefixEnd_5874258 : Nat := 4983230072969 + 3 ^ 40 * 5874258 * 2
def baseEnd_5874258 : Nat := 3016317842518983172259785

theorem tailTrace_5874258 : CollatzResearch.WordTrace tailWord_5874258 prefixEnd_5874258 3016317842518983172259785 := by
  unfold tailWord_5874258
  simp only [CollatzResearch.WordTrace]
  refine ⟨53562947688143496059805857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142834527168382656159482285 53562947688143496059805857)
  ·
    refine ⟨40172210766107622044854393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53562947688143496059805857 40172210766107622044854393)
    ·
      refine ⟨30129158074580716533640795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40172210766107622044854393 30129158074580716533640795)
      ·
        refine ⟨45193737111871074800461193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30129158074580716533640795 45193737111871074800461193)
        ·
          refine ⟨33895302833903306100345895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45193737111871074800461193 33895302833903306100345895)
          ·
            refine ⟨50842954250854959150518843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33895302833903306100345895 50842954250854959150518843)
            ·
              refine ⟨76264431376282438725778265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50842954250854959150518843 76264431376282438725778265)
              ·
                refine ⟨57198323532211829044333699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76264431376282438725778265 57198323532211829044333699)
                ·
                  refine ⟨85797485298317743566500549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57198323532211829044333699 85797485298317743566500549)
                  ·
                    refine ⟨16087028493434576918718853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85797485298317743566500549 16087028493434576918718853)
                    ·
                      refine ⟨3016317842518983172259785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16087028493434576918718853 3016317842518983172259785)
                      ·
                        rfl

theorem cell23_5874258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_5874258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874258 prefixEnd_5874258 := by exact prefixLift 5874258
  have htrace : WordTrace (prefixWord ++ tailWord_5874258) baseStart_5874258 baseEnd_5874258 := by
    simpa [prefixWord, tailWord_5874258, baseEnd_5874258] using wordTrace_append hprefix tailTrace_5874258
  have hstable : (prefixWord ++ tailWord_5874258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874258).length < 2 ^ (prefixWord ++ tailWord_5874258).sum := by decide
  have hdescent : baseEnd_5874258 < baseStart_5874258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874285 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 7]
def baseStart_5874285 : Nat := 118140960795 + 5874285 * 2 ^ 59
def prefixEnd_5874285 : Nat := 4983230072969 + 3 ^ 40 * 5874285 * 2
def baseEnd_5874285 : Nat := 335147967388517174069129

theorem tailTrace_5874285 : CollatzResearch.WordTrace tailWord_5874285 prefixEnd_5874285 335147967388517174069129 := by
  unfold tailWord_5874285
  simp only [CollatzResearch.WordTrace]
  refine ⟨214252775523476167850456309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142835183682317445233637539 214252775523476167850456309)
  ·
    refine ⟨20086197705325890735980279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214252775523476167850456309 20086197705325890735980279)
    ·
      refine ⟨30129296557988836103970419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20086197705325890735980279 30129296557988836103970419)
      ·
        refine ⟨45193944836983254155955629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30129296557988836103970419 45193944836983254155955629)
        ·
          refine ⟨16947729313868720308483361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45193944836983254155955629 16947729313868720308483361)
          ·
            refine ⟨12710796985401540231362521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16947729313868720308483361 12710796985401540231362521)
            ·
              refine ⟨9533097739051155173521891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12710796985401540231362521 9533097739051155173521891)
              ·
                refine ⟨14299646608576732760282837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9533097739051155173521891 14299646608576732760282837)
                ·
                  refine ⟨335147967388517174069129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14299646608576732760282837 335147967388517174069129)
                  ·
                    rfl

theorem cell23_5874285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_5874285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874285 prefixEnd_5874285 := by exact prefixLift 5874285
  have htrace : WordTrace (prefixWord ++ tailWord_5874285) baseStart_5874285 baseEnd_5874285 := by
    simpa [prefixWord, tailWord_5874285, baseEnd_5874285] using wordTrace_append hprefix tailTrace_5874285
  have hstable : (prefixWord ++ tailWord_5874285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874285).length < 2 ^ (prefixWord ++ tailWord_5874285).sum := by decide
  have hdescent : baseEnd_5874285 < baseStart_5874285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874372 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_5874372 : Nat := 118140960795 + 5874372 * 2 ^ 59
def prefixEnd_5874372 : Nat := 4983230072969 + 3 ^ 40 * 5874372 * 2
def baseEnd_5874372 : Nat := 3016376379313595726234261

theorem tailTrace_5874372 : CollatzResearch.WordTrace tailWord_5874372 prefixEnd_5874372 3016376379313595726234261 := by
  unfold tailWord_5874372
  simp only [CollatzResearch.WordTrace]
  refine ⟨107127974337080490854436685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142837299116107321139248913 107127974337080490854436685)
  ·
    refine ⟨40172990376405184070413757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107127974337080490854436685 40172990376405184070413757)
    ·
      refine ⟨15064871391151944026405159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40172990376405184070413757 15064871391151944026405159)
      ·
        refine ⟨22597307086727916039607739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15064871391151944026405159 22597307086727916039607739)
        ·
          refine ⟨33895960630091874059411609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22597307086727916039607739 33895960630091874059411609)
          ·
            refine ⟨25421970472568905544558707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33895960630091874059411609 25421970472568905544558707)
            ·
              refine ⟨38132955708853358316838061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25421970472568905544558707 38132955708853358316838061)
              ·
                refine ⟨14299858390820009368814273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38132955708853358316838061 14299858390820009368814273)
                ·
                  refine ⟨10724893793115007026610705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14299858390820009368814273 10724893793115007026610705)
                  ·
                    refine ⟨8043670344836255269958029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10724893793115007026610705 8043670344836255269958029)
                    ·
                      refine ⟨3016376379313595726234261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8043670344836255269958029 3016376379313595726234261)
                      ·
                        rfl

theorem cell23_5874372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_5874372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874372 prefixEnd_5874372 := by exact prefixLift 5874372
  have htrace : WordTrace (prefixWord ++ tailWord_5874372) baseStart_5874372 baseEnd_5874372 := by
    simpa [prefixWord, tailWord_5874372, baseEnd_5874372] using wordTrace_append hprefix tailTrace_5874372
  have hstable : (prefixWord ++ tailWord_5874372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874372).length < 2 ^ (prefixWord ++ tailWord_5874372).sum := by decide
  have hdescent : baseEnd_5874372 < baseStart_5874372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874396 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5874396 : Nat := 118140960795 + 5874396 * 2 ^ 59
def prefixEnd_5874396 : Nat := 4983230072969 + 3 ^ 40 * 5874396 * 2
def baseEnd_5874396 : Nat := 1005462900949767877444717

theorem tailTrace_5874396 : CollatzResearch.WordTrace tailWord_5874396 prefixEnd_5874396 1005462900949767877444717 := by
  unfold tailWord_5874396
  simp only [CollatzResearch.WordTrace]
  refine ⟨107128412013037016903873521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142837882684049355871831361 107128412013037016903873521)
  ·
    refine ⟨80346309009777762677905141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107128412013037016903873521 80346309009777762677905141)
    ·
      refine ⟨7532466469666665251053607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80346309009777762677905141 7532466469666665251053607)
      ·
        refine ⟨11298699704499997876580411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7532466469666665251053607 11298699704499997876580411)
        ·
          refine ⟨16948049556749996814870617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11298699704499997876580411 16948049556749996814870617)
          ·
            refine ⟨12711037167562497611152963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16948049556749996814870617 12711037167562497611152963)
            ·
              refine ⟨19066555751343746416729445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12711037167562497611152963 19066555751343746416729445)
              ·
                refine ⟨3574979203376952453136771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19066555751343746416729445 3574979203376952453136771)
                ·
                  refine ⟨5362468805065428679705157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574979203376952453136771 5362468805065428679705157)
                  ·
                    refine ⟨1005462900949767877444717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362468805065428679705157 1005462900949767877444717)
                    ·
                      rfl

theorem cell23_5874396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5874396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874396 prefixEnd_5874396 := by exact prefixLift 5874396
  have htrace : WordTrace (prefixWord ++ tailWord_5874396) baseStart_5874396 baseEnd_5874396 := by
    simpa [prefixWord, tailWord_5874396, baseEnd_5874396] using wordTrace_append hprefix tailTrace_5874396
  have hstable : (prefixWord ++ tailWord_5874396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874396).length < 2 ^ (prefixWord ++ tailWord_5874396).sum := by decide
  have hdescent : baseEnd_5874396 < baseStart_5874396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874405 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_5874405 : Nat := 118140960795 + 5874405 * 2 ^ 59
def prefixEnd_5874405 : Nat := 4983230072969 + 3 ^ 40 * 5874405 * 2
def baseEnd_5874405 : Nat := 1005464441391731365707203

theorem tailTrace_5874405 : CollatzResearch.WordTrace tailWord_5874405 prefixEnd_5874405 1005464441391731365707203 := by
  unfold tailWord_5874405
  simp only [CollatzResearch.WordTrace]
  refine ⟨214257152283041428344824669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142838101522027618896549779 214257152283041428344824669)
  ·
    refine ⟨80346432106140535629309251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214257152283041428344824669 80346432106140535629309251)
    ·
      refine ⟨120519648159210803443963877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80346432106140535629309251 120519648159210803443963877)
      ·
        refine ⟨22597434029852025645743227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120519648159210803443963877 22597434029852025645743227)
        ·
          refine ⟨33896151044778038468614841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22597434029852025645743227 33896151044778038468614841)
          ·
            refine ⟨25422113283583528851461131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33896151044778038468614841 25422113283583528851461131)
            ·
              refine ⟨38133169925375293277191697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25422113283583528851461131 38133169925375293277191697)
              ·
                refine ⟨28599877444031469957893773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38133169925375293277191697 28599877444031469957893773)
                ·
                  refine ⟨10724954041511801234210165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28599877444031469957893773 10724954041511801234210165)
                  ·
                    refine ⟨1005464441391731365707203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10724954041511801234210165 1005464441391731365707203)
                    ·
                      rfl

theorem cell23_5874405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_5874405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874405 prefixEnd_5874405 := by exact prefixLift 5874405
  have htrace : WordTrace (prefixWord ++ tailWord_5874405) baseStart_5874405 baseEnd_5874405 := by
    simpa [prefixWord, tailWord_5874405, baseEnd_5874405] using wordTrace_append hprefix tailTrace_5874405
  have hstable : (prefixWord ++ tailWord_5874405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874405).length < 2 ^ (prefixWord ++ tailWord_5874405).sum := by decide
  have hdescent : baseEnd_5874405 < baseStart_5874405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874422 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_5874422 : Nat := 118140960795 + 5874422 * 2 ^ 59
def prefixEnd_5874422 : Nat := 4983230072969 + 3 ^ 40 * 5874422 * 2
def baseEnd_5874422 : Nat := 1005467351115440176869677

theorem tailTrace_5874422 : CollatzResearch.WordTrace tailWord_5874422 prefixEnd_5874422 1005467351115440176869677 := by
  unfold tailWord_5874422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391110770248740015512095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142838514882653226832129013 13391110770248740015512095)
  ·
    refine ⟨20086666155373110023268143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13391110770248740015512095 20086666155373110023268143)
    ·
      refine ⟨30129999233059665034902215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20086666155373110023268143 30129999233059665034902215)
      ·
        refine ⟨45194998849589497552353323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30129999233059665034902215 45194998849589497552353323)
        ·
          refine ⟨67792498274384246328529985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45194998849589497552353323 67792498274384246328529985)
          ·
            refine ⟨50844373705788184746397489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67792498274384246328529985 50844373705788184746397489)
            ·
              refine ⟨38133280279341138559798117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50844373705788184746397489 38133280279341138559798117)
              ·
                refine ⟨7149990052376463479962147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38133280279341138559798117 7149990052376463479962147)
                ·
                  refine ⟨10724985078564695219943221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149990052376463479962147 10724985078564695219943221)
                  ·
                    refine ⟨1005467351115440176869677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10724985078564695219943221 1005467351115440176869677)
                    ·
                      rfl

theorem cell23_5874422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_5874422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874422 prefixEnd_5874422 := by exact prefixLift 5874422
  have htrace : WordTrace (prefixWord ++ tailWord_5874422) baseStart_5874422 baseEnd_5874422 := by
    simpa [prefixWord, tailWord_5874422, baseEnd_5874422] using wordTrace_append hprefix tailTrace_5874422
  have hstable : (prefixWord ++ tailWord_5874422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874422).length < 2 ^ (prefixWord ++ tailWord_5874422).sum := by decide
  have hdescent : baseEnd_5874422 < baseStart_5874422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874435 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 4, 4]
def baseStart_5874435 : Nat := 118140960795 + 5874435 * 2 ^ 59
def prefixEnd_5874435 : Nat := 4983230072969 + 3 ^ 40 * 5874435 * 2
def baseEnd_5874435 : Nat := 1005469576198276326582157

theorem tailTrace_5874435 : CollatzResearch.WordTrace tailWord_5874435 prefixEnd_5874435 1005469576198276326582157 := by
  unfold tailWord_5874435
  simp only [CollatzResearch.WordTrace]
  refine ⟨214258246472932743468416759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142838830981955162312277839 214258246472932743468416759)
  ·
    refine ⟨321387369709399115202625139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214258246472932743468416759 321387369709399115202625139)
    ·
      refine ⟨482081054564098672803937709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321387369709399115202625139 482081054564098672803937709)
      ·
        refine ⟨180780395461537002301476641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 482081054564098672803937709 180780395461537002301476641)
        ·
          refine ⟨135585296596152751726107481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180780395461537002301476641 135585296596152751726107481)
          ·
            refine ⟨101688972447114563794580611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135585296596152751726107481 101688972447114563794580611)
            ·
              refine ⟨152533458670671845691870917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101688972447114563794580611 152533458670671845691870917)
              ·
                refine ⟨28600023500750971067225797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152533458670671845691870917 28600023500750971067225797)
                ·
                  refine ⟨5362504406390807075104837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28600023500750971067225797 5362504406390807075104837)
                  ·
                    refine ⟨1005469576198276326582157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362504406390807075104837 1005469576198276326582157)
                    ·
                      rfl

theorem cell23_5874435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 4].length) (baseStart_5874435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874435 prefixEnd_5874435 := by exact prefixLift 5874435
  have htrace : WordTrace (prefixWord ++ tailWord_5874435) baseStart_5874435 baseEnd_5874435 := by
    simpa [prefixWord, tailWord_5874435, baseEnd_5874435] using wordTrace_append hprefix tailTrace_5874435
  have hstable : (prefixWord ++ tailWord_5874435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874435).length < 2 ^ (prefixWord ++ tailWord_5874435).sum := by decide
  have hdescent : baseEnd_5874435 < baseStart_5874435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874436 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5874436 : Nat := 118140960795 + 5874436 * 2 ^ 59
def prefixEnd_5874436 : Nat := 4983230072969 + 3 ^ 40 * 5874436 * 2
def baseEnd_5874436 : Nat := 3016409242075483475833967

theorem tailTrace_5874436 : CollatzResearch.WordTrace tailWord_5874436 prefixEnd_5874436 3016409242075483475833967 := by
  unfold tailWord_5874436
  simp only [CollatzResearch.WordTrace]
  refine ⟨107129141472964560319601581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142838855297286080426135441 107129141472964560319601581)
  ·
    refine ⟨40173428052361710119850593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107129141472964560319601581 40173428052361710119850593)
    ·
      refine ⟨30130071039271282589887945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40173428052361710119850593 30130071039271282589887945)
      ·
        refine ⟨22597553279453461942415959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30130071039271282589887945 22597553279453461942415959)
        ·
          refine ⟨33896329919180192913623939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22597553279453461942415959 33896329919180192913623939)
          ·
            refine ⟨50844494878770289370435909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33896329919180192913623939 50844494878770289370435909)
            ·
              refine ⟨9533342789769429256956733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50844494878770289370435909 9533342789769429256956733)
              ·
                refine ⟨3575003546163535971358775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9533342789769429256956733 3575003546163535971358775)
                ·
                  refine ⟨5362505319245303957038163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575003546163535971358775 5362505319245303957038163)
                  ·
                    refine ⟨8043757978867955935557245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5362505319245303957038163 8043757978867955935557245)
                    ·
                      refine ⟨3016409242075483475833967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8043757978867955935557245 3016409242075483475833967)
                      ·
                        rfl

theorem cell23_5874436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5874436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874436 prefixEnd_5874436 := by exact prefixLift 5874436
  have htrace : WordTrace (prefixWord ++ tailWord_5874436) baseStart_5874436 baseEnd_5874436 := by
    simpa [prefixWord, tailWord_5874436, baseEnd_5874436] using wordTrace_append hprefix tailTrace_5874436
  have hstable : (prefixWord ++ tailWord_5874436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874436).length < 2 ^ (prefixWord ++ tailWord_5874436).sum := by decide
  have hdescent : baseEnd_5874436 < baseStart_5874436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874439 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 1, 5]
def baseStart_5874439 : Nat := 118140960795 + 5874439 * 2 ^ 59
def prefixEnd_5874439 : Nat := 4983230072969 + 3 ^ 40 * 5874439 * 2
def baseEnd_5874439 : Nat := 1005470260839148988032151

theorem tailTrace_5874439 : CollatzResearch.WordTrace tailWord_5874439 prefixEnd_5874439 1005470260839148988032151 := by
  unfold tailWord_5874439
  simp only [CollatzResearch.WordTrace]
  refine ⟨214258392364918252151562371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142838928243278834767708247 214258392364918252151562371)
  ·
    refine ⟨321387588547377378227343557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214258392364918252151562371 321387588547377378227343557)
    ·
      refine ⟨60260172852633258417626917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321387588547377378227343557 60260172852633258417626917)
      ·
        refine ⟨11298782409868735953305047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60260172852633258417626917 11298782409868735953305047)
        ·
          refine ⟨16948173614803103929957571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11298782409868735953305047 16948173614803103929957571)
          ·
            refine ⟨25422260422204655894936357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16948173614803103929957571 25422260422204655894936357)
            ·
              refine ⟨4766673829163372980300567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25422260422204655894936357 4766673829163372980300567)
              ·
                refine ⟨7150010743745059470450851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766673829163372980300567 7150010743745059470450851)
                ·
                  refine ⟨10725016115617589205676277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150010743745059470450851 10725016115617589205676277)
                  ·
                    refine ⟨1005470260839148988032151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10725016115617589205676277 1005470260839148988032151)
                    ·
                      rfl

theorem cell23_5874439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_5874439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874439 prefixEnd_5874439 := by exact prefixLift 5874439
  have htrace : WordTrace (prefixWord ++ tailWord_5874439) baseStart_5874439 baseEnd_5874439 := by
    simpa [prefixWord, tailWord_5874439, baseEnd_5874439] using wordTrace_append hprefix tailTrace_5874439
  have hstable : (prefixWord ++ tailWord_5874439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874439).length < 2 ^ (prefixWord ++ tailWord_5874439).sum := by decide
  have hdescent : baseEnd_5874439 < baseStart_5874439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874442 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_5874442 : Nat := 118140960795 + 5874442 * 2 ^ 59
def prefixEnd_5874442 : Nat := 4983230072969 + 3 ^ 40 * 5874442 * 2
def baseEnd_5874442 : Nat := 3016412322959410452358939

theorem tailTrace_5874442 : CollatzResearch.WordTrace tailWord_5874442 prefixEnd_5874442 3016412322959410452358939 := by
  unfold tailWord_5874442
  simp only [CollatzResearch.WordTrace]
  refine ⟨53564625445976845915980395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142839001189271589109281053 53564625445976845915980395)
  ·
    refine ⟨80346938168965268873970593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53564625445976845915980395 80346938168965268873970593)
    ·
      refine ⟨60260203626723951655477945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80346938168965268873970593 60260203626723951655477945)
      ·
        refine ⟨45195152720042963741608459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60260203626723951655477945 45195152720042963741608459)
        ·
          refine ⟨67792729080064445612412689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45195152720042963741608459 67792729080064445612412689)
          ·
            refine ⟨50844546810048334209309517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67792729080064445612412689 50844546810048334209309517)
            ·
              refine ⟨19066705053768125328491069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50844546810048334209309517 19066705053768125328491069)
              ·
                refine ⟨7150014395163046998184151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19066705053768125328491069 7150014395163046998184151)
                ·
                  refine ⟨10725021592744570497276227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150014395163046998184151 10725021592744570497276227)
                  ·
                    refine ⟨16087532389116855745914341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10725021592744570497276227 16087532389116855745914341)
                    ·
                      refine ⟨3016412322959410452358939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16087532389116855745914341 3016412322959410452358939)
                      ·
                        rfl

theorem cell23_5874442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_5874442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874442 prefixEnd_5874442 := by exact prefixLift 5874442
  have htrace : WordTrace (prefixWord ++ tailWord_5874442) baseStart_5874442 baseEnd_5874442 := by
    simpa [prefixWord, tailWord_5874442, baseEnd_5874442] using wordTrace_append hprefix tailTrace_5874442
  have hstable : (prefixWord ++ tailWord_5874442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874442).length < 2 ^ (prefixWord ++ tailWord_5874442).sum := by decide
  have hdescent : baseEnd_5874442 < baseStart_5874442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874469 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_5874469 : Nat := 118140960795 + 5874469 * 2 ^ 59
def prefixEnd_5874469 : Nat := 4983230072969 + 3 ^ 40 * 5874469 * 2
def baseEnd_5874469 : Nat := 1005475395645693948907105

theorem tailTrace_5874469 : CollatzResearch.WordTrace tailWord_5874469 prefixEnd_5874469 1005475395645693948907105 := by
  unfold tailWord_5874469
  simp only [CollatzResearch.WordTrace]
  refine ⟨214259486554809567275154461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142839657703206378183436307 214259486554809567275154461)
  ·
    refine ⟨80347307458053587728182923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214259486554809567275154461 80347307458053587728182923)
    ·
      refine ⟨120520961187080381592274385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80347307458053587728182923 120520961187080381592274385)
      ·
        refine ⟨90390720890310286194205789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120520961187080381592274385 90390720890310286194205789)
        ·
          refine ⟨33896520333866357322827171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90390720890310286194205789 33896520333866357322827171)
          ·
            refine ⟨50844780500799535984240757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33896520333866357322827171 50844780500799535984240757)
            ·
              refine ⟨4766698171949956498522571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50844780500799535984240757 4766698171949956498522571)
              ·
                refine ⟨7150047257924934747783857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766698171949956498522571 7150047257924934747783857)
                ·
                  refine ⟨5362535443443701060837893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7150047257924934747783857 5362535443443701060837893)
                  ·
                    refine ⟨1005475395645693948907105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362535443443701060837893 1005475395645693948907105)
                    ·
                      rfl

theorem cell23_5874469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_5874469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874469 prefixEnd_5874469 := by exact prefixLift 5874469
  have htrace : WordTrace (prefixWord ++ tailWord_5874469) baseStart_5874469 baseEnd_5874469 := by
    simpa [prefixWord, tailWord_5874469, baseEnd_5874469] using wordTrace_append hprefix tailTrace_5874469
  have hstable : (prefixWord ++ tailWord_5874469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874469).length < 2 ^ (prefixWord ++ tailWord_5874469).sum := by decide
  have hdescent : baseEnd_5874469 < baseStart_5874469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874536 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5874536 : Nat := 118140960795 + 5874536 * 2 ^ 59
def prefixEnd_5874536 : Nat := 4983230072969 + 3 ^ 40 * 5874536 * 2
def baseEnd_5874536 : Nat := 3016460590140933084583507

theorem tailTrace_5874536 : CollatzResearch.WordTrace tailWord_5874536 prefixEnd_5874536 3016460590140933084583507 := by
  unfold tailWord_5874536
  simp only [CollatzResearch.WordTrace]
  refine ⟨107130965122783418858921731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142841286830377891811895641 107130965122783418858921731)
  ·
    refine ⟨160696447684175128288382597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107130965122783418858921731 160696447684175128288382597)
    ·
      refine ⟨30130583940782836554071737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160696447684175128288382597 30130583940782836554071737)
      ·
        refine ⟨22597937955587127415553803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30130583940782836554071737 22597937955587127415553803)
        ·
          refine ⟨33896906933380691123330705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22597937955587127415553803 33896906933380691123330705)
          ·
            refine ⟨25422680200035518342498029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33896906933380691123330705 25422680200035518342498029)
            ·
              refine ⟨9533505075013319378436761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25422680200035518342498029 9533505075013319378436761)
              ·
                refine ⟨7150128806259989533827571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9533505075013319378436761 7150128806259989533827571)
                ·
                  refine ⟨10725193209389984300741357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150128806259989533827571 10725193209389984300741357)
                  ·
                    refine ⟨4021947453521244112778009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10725193209389984300741357 4021947453521244112778009)
                    ·
                      refine ⟨3016460590140933084583507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021947453521244112778009 3016460590140933084583507)
                      ·
                        rfl

theorem cell23_5874536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5874536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874536 prefixEnd_5874536 := by exact prefixLift 5874536
  have htrace : WordTrace (prefixWord ++ tailWord_5874536) baseStart_5874536 baseEnd_5874536 := by
    simpa [prefixWord, tailWord_5874536, baseEnd_5874536] using wordTrace_append hprefix tailTrace_5874536
  have hstable : (prefixWord ++ tailWord_5874536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874536).length < 2 ^ (prefixWord ++ tailWord_5874536).sum := by decide
  have hdescent : baseEnd_5874536 < baseStart_5874536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874549 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_5874549 : Nat := 118140960795 + 5874549 * 2 ^ 59
def prefixEnd_5874549 : Nat := 4983230072969 + 3 ^ 40 * 5874549 * 2
def baseEnd_5874549 : Nat := 3016467265389441533720947

theorem tailTrace_5874549 : CollatzResearch.WordTrace tailWord_5874549 prefixEnd_5874549 3016467265389441533720947 := by
  unfold tailWord_5874549
  simp only [CollatzResearch.WordTrace]
  refine ⟨214262404394519740938066701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142841602929679827292044467 214262404394519740938066701)
  ·
    refine ⟨80348401647944902851775013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214262404394519740938066701 80348401647944902851775013)
    ·
      refine ⟨15065325308989669284707815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80348401647944902851775013 15065325308989669284707815)
      ·
        refine ⟨22597987963484503927061723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065325308989669284707815 22597987963484503927061723)
        ·
          refine ⟨33896981945226755890592585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22597987963484503927061723 33896981945226755890592585)
          ·
            refine ⟨25422736458920066917944439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33896981945226755890592585 25422736458920066917944439)
            ·
              refine ⟨38134104688380100376916659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25422736458920066917944439 38134104688380100376916659)
              ·
                refine ⟨57201157032570150565374989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38134104688380100376916659 57201157032570150565374989)
                ·
                  refine ⟨21450433887213806462015621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57201157032570150565374989 21450433887213806462015621)
                  ·
                    refine ⟨4021956353852588711627929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21450433887213806462015621 4021956353852588711627929)
                    ·
                      refine ⟨3016467265389441533720947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4021956353852588711627929 3016467265389441533720947)
                      ·
                        rfl

theorem cell23_5874549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_5874549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874549 prefixEnd_5874549 := by exact prefixLift 5874549
  have htrace : WordTrace (prefixWord ++ tailWord_5874549) baseStart_5874549 baseEnd_5874549 := by
    simpa [prefixWord, tailWord_5874549, baseEnd_5874549] using wordTrace_append hprefix tailTrace_5874549
  have hstable : (prefixWord ++ tailWord_5874549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874549).length < 2 ^ (prefixWord ++ tailWord_5874549).sum := by decide
  have hdescent : baseEnd_5874549 < baseStart_5874549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874585 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_5874585 : Nat := 118140960795 + 5874585 * 2 ^ 59
def prefixEnd_5874585 : Nat := 4983230072969 + 3 ^ 40 * 5874585 * 2
def baseEnd_5874585 : Nat := 1005495250231001130956927

theorem tailTrace_5874585 : CollatzResearch.WordTrace tailWord_5874585 prefixEnd_5874585 1005495250231001130956927 := by
  unfold tailWord_5874585
  simp only [CollatzResearch.WordTrace]
  refine ⟨214263717422389319086377209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142842478281592879390918139 214263717422389319086377209)
  ·
    refine ⟨160697788066791989314782907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214263717422389319086377209 160697788066791989314782907)
    ·
      refine ⟨241046682100187983972174361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160697788066791989314782907 241046682100187983972174361)
      ·
        refine ⟨180785011575140987979130771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241046682100187983972174361 180785011575140987979130771)
        ·
          refine ⟨271177517362711481968696157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180785011575140987979130771 271177517362711481968696157)
          ·
            refine ⟨101691569011016805738261059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271177517362711481968696157 101691569011016805738261059)
            ·
              refine ⟨152537353516525208607391589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101691569011016805738261059 152537353516525208607391589)
              ·
                refine ⟨28600753784348476613885923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152537353516525208607391589 28600753784348476613885923)
                ·
                  refine ⟨42901130676522714920828885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28600753784348476613885923 42901130676522714920828885)
                  ·
                    refine ⟨1005495250231001130956927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42901130676522714920828885 1005495250231001130956927)
                    ·
                      rfl

theorem cell23_5874585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_5874585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874585 prefixEnd_5874585 := by exact prefixLift 5874585
  have htrace : WordTrace (prefixWord ++ tailWord_5874585) baseStart_5874585 baseEnd_5874585 := by
    simpa [prefixWord, tailWord_5874585, baseEnd_5874585] using wordTrace_append hprefix tailTrace_5874585
  have hstable : (prefixWord ++ tailWord_5874585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874585).length < 2 ^ (prefixWord ++ tailWord_5874585).sum := by decide
  have hdescent : baseEnd_5874585 < baseStart_5874585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874595 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_5874595 : Nat := 118140960795 + 5874595 * 2 ^ 59
def prefixEnd_5874595 : Nat := 4983230072969 + 3 ^ 40 * 5874595 * 2
def baseEnd_5874595 : Nat := 3016490885499548353745735

theorem tailTrace_5874595 : CollatzResearch.WordTrace tailWord_5874595 prefixEnd_5874595 3016490885499548353745735 := by
  unfold tailWord_5874595
  simp only [CollatzResearch.WordTrace]
  refine ⟨214264082152353090794241239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142842721434902060529494159 214264082152353090794241239)
  ·
    refine ⟨321396123228529636191361859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214264082152353090794241239 321396123228529636191361859)
    ·
      refine ⟨482094184842794454287042789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321396123228529636191361859 482094184842794454287042789)
      ·
        refine ⟨90392659658023960178820523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482094184842794454287042789 90392659658023960178820523)
        ·
          refine ⟨135588989487035940268230785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90392659658023960178820523 135588989487035940268230785)
          ·
            refine ⟨101691742115276955201173089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135588989487035940268230785 101691742115276955201173089)
            ·
              refine ⟨76268806586457716400879817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101691742115276955201173089 76268806586457716400879817)
              ·
                refine ⟨57201604939843287300659863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76268806586457716400879817 57201604939843287300659863)
                ·
                  refine ⟨85802407409764930950989795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57201604939843287300659863 85802407409764930950989795)
                  ·
                    refine ⟨128703611114647396426484693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85802407409764930950989795 128703611114647396426484693)
                    ·
                      refine ⟨3016490885499548353745735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128703611114647396426484693 3016490885499548353745735)
                      ·
                        rfl

theorem cell23_5874595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_5874595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874595 prefixEnd_5874595 := by exact prefixLift 5874595
  have htrace : WordTrace (prefixWord ++ tailWord_5874595) baseStart_5874595 baseEnd_5874595 := by
    simpa [prefixWord, tailWord_5874595, baseEnd_5874595] using wordTrace_append hprefix tailTrace_5874595
  have hstable : (prefixWord ++ tailWord_5874595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874595).length < 2 ^ (prefixWord ++ tailWord_5874595).sum := by decide
  have hdescent : baseEnd_5874595 < baseStart_5874595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874639 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 2, 4, 2]
def baseStart_5874639 : Nat := 118140960795 + 5874639 * 2 ^ 59
def prefixEnd_5874639 : Nat := 4983230072969 + 3 ^ 40 * 5874639 * 2
def baseEnd_5874639 : Nat := 3016513478648346181595533

theorem tailTrace_5874639 : CollatzResearch.WordTrace tailWord_5874639 prefixEnd_5874639 3016513478648346181595533 := by
  unfold tailWord_5874639
  simp only [CollatzResearch.WordTrace]
  refine ⟨214265686964193686308842971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142843791309462457539228647 214265686964193686308842971)
  ·
    refine ⟨321398530446290529463264457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214265686964193686308842971 321398530446290529463264457)
    ·
      refine ⟨241048897834717897097448343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321398530446290529463264457 241048897834717897097448343)
      ·
        refine ⟨361573346752076845646172515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241048897834717897097448343 361573346752076845646172515)
        ·
          refine ⟨542360020128115268469258773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361573346752076845646172515 542360020128115268469258773)
          ·
            refine ⟨25423125943505403209496505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 542360020128115268469258773 25423125943505403209496505)
            ·
              refine ⟨19067344457629052407122379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25423125943505403209496505 19067344457629052407122379)
              ·
                refine ⟨28601016686443578610683569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19067344457629052407122379 28601016686443578610683569)
                ·
                  refine ⟨21450762514832683958012677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28601016686443578610683569 21450762514832683958012677)
                  ·
                    refine ⟨4022017971531128242127377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21450762514832683958012677 4022017971531128242127377)
                    ·
                      refine ⟨3016513478648346181595533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022017971531128242127377 3016513478648346181595533)
                      ·
                        rfl

theorem cell23_5874639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4, 2].length) (baseStart_5874639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874639 prefixEnd_5874639 := by exact prefixLift 5874639
  have htrace : WordTrace (prefixWord ++ tailWord_5874639) baseStart_5874639 baseEnd_5874639 := by
    simpa [prefixWord, tailWord_5874639, baseEnd_5874639] using wordTrace_append hprefix tailTrace_5874639
  have hstable : (prefixWord ++ tailWord_5874639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874639).length < 2 ^ (prefixWord ++ tailWord_5874639).sum := by decide
  have hdescent : baseEnd_5874639 < baseStart_5874639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874649 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 3, 4]
def baseStart_5874649 : Nat := 118140960795 + 5874649 * 2 ^ 59
def prefixEnd_5874649 : Nat := 4983230072969 + 3 ^ 40 * 5874649 * 2
def baseEnd_5874649 : Nat := 1005506204484963714156829

theorem tailTrace_5874649 : CollatzResearch.WordTrace tailWord_5874649 prefixEnd_5874649 1005506204484963714156829 := by
  unfold tailWord_5874649
  simp only [CollatzResearch.WordTrace]
  refine ⟨214266051694157458016707001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142844034462771638677804667 214266051694157458016707001)
  ·
    refine ⟨160699538770618093512530251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214266051694157458016707001 160699538770618093512530251)
    ·
      refine ⟨241049308155927140268795377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160699538770618093512530251 241049308155927140268795377)
      ·
        refine ⟨180786981116945355201596533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241049308155927140268795377 180786981116945355201596533)
        ·
          refine ⟨16948779479713627050149675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180786981116945355201596533 16948779479713627050149675)
          ·
            refine ⟨25423169219570440575224513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16948779479713627050149675 25423169219570440575224513)
            ·
              refine ⟨19067376914677830431418385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25423169219570440575224513 19067376914677830431418385)
              ·
                refine ⟨14300532686008372823563789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19067376914677830431418385 14300532686008372823563789)
                ·
                  refine ⟨5362699757253139808836421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14300532686008372823563789 5362699757253139808836421)
                  ·
                    refine ⟨1005506204484963714156829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362699757253139808836421 1005506204484963714156829)
                    ·
                      rfl

theorem cell23_5874649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_5874649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874649 prefixEnd_5874649 := by exact prefixLift 5874649
  have htrace : WordTrace (prefixWord ++ tailWord_5874649) baseStart_5874649 baseEnd_5874649 := by
    simpa [prefixWord, tailWord_5874649, baseEnd_5874649] using wordTrace_append hprefix tailTrace_5874649
  have hstable : (prefixWord ++ tailWord_5874649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874649).length < 2 ^ (prefixWord ++ tailWord_5874649).sum := by decide
  have hdescent : baseEnd_5874649 < baseStart_5874649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874659 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5874659 : Nat := 118140960795 + 5874659 * 2 ^ 59
def prefixEnd_5874659 : Nat := 4983230072969 + 3 ^ 40 * 5874659 * 2
def baseEnd_5874659 : Nat := 3016523748261436103345441

theorem tailTrace_5874659 : CollatzResearch.WordTrace tailWord_5874659 prefixEnd_5874659 3016523748261436103345441 := by
  unfold tailWord_5874659
  simp only [CollatzResearch.WordTrace]
  refine ⟨214266416424121229724571031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142844277616080819816380687 214266416424121229724571031)
  ·
    refine ⟨321399624636181844586856547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214266416424121229724571031 321399624636181844586856547)
    ·
      refine ⟨482099436954272766880284821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321399624636181844586856547 482099436954272766880284821)
      ·
        refine ⟨22598411107231535947513351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 482099436954272766880284821 22598411107231535947513351)
        ·
          refine ⟨33897616660847303921270027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22598411107231535947513351 33897616660847303921270027)
          ·
            refine ⟨50846424991270955881905041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33897616660847303921270027 50846424991270955881905041)
            ·
              refine ⟨38134818743453216911428781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50846424991270955881905041 38134818743453216911428781)
              ·
                refine ⟨14300557028794956341785793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38134818743453216911428781 14300557028794956341785793)
                ·
                  refine ⟨10725417771596217256339345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14300557028794956341785793 10725417771596217256339345)
                  ·
                    refine ⟨8044063328697162942254509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10725417771596217256339345 8044063328697162942254509)
                    ·
                      refine ⟨3016523748261436103345441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8044063328697162942254509 3016523748261436103345441)
                      ·
                        rfl

theorem cell23_5874659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5874659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874659 prefixEnd_5874659 := by exact prefixLift 5874659
  have htrace : WordTrace (prefixWord ++ tailWord_5874659) baseStart_5874659 baseEnd_5874659 := by
    simpa [prefixWord, tailWord_5874659, baseEnd_5874659] using wordTrace_append hprefix tailTrace_5874659
  have hstable : (prefixWord ++ tailWord_5874659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874659).length < 2 ^ (prefixWord ++ tailWord_5874659).sum := by decide
  have hdescent : baseEnd_5874659 < baseStart_5874659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874696 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 6]
def baseStart_5874696 : Nat := 118140960795 + 5874696 * 2 ^ 59
def prefixEnd_5874696 : Nat := 4983230072969 + 3 ^ 40 * 5874696 * 2
def baseEnd_5874696 : Nat := 335171416338405828731419

theorem tailTrace_5874696 : CollatzResearch.WordTrace tailWord_5874696 prefixEnd_5874696 335171416338405828731419 := by
  unfold tailWord_5874696
  simp only [CollatzResearch.WordTrace]
  refine ⟨107133882962493592521833971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142845177283324790029111961 107133882962493592521833971)
  ·
    refine ⟨160700824443740388782750957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107133882962493592521833971 160700824443740388782750957)
    ·
      refine ⟨60262809166402645793531609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160700824443740388782750957 60262809166402645793531609)
      ·
        refine ⟨45197106874801984345148707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60262809166402645793531609 45197106874801984345148707)
        ·
          refine ⟨67795660312202976517723061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45197106874801984345148707 67795660312202976517723061)
          ·
            refine ⟨6355843154269029048536537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67795660312202976517723061 6355843154269029048536537)
            ·
              refine ⟨4766882365701771786402403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6355843154269029048536537 4766882365701771786402403)
              ·
                refine ⟨7150323548552657679603605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766882365701771786402403 7150323548552657679603605)
                ·
                  refine ⟨335171416338405828731419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7150323548552657679603605 335171416338405828731419)
                  ·
                    rfl

theorem cell23_5874696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 6].length) (baseStart_5874696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874696 prefixEnd_5874696 := by exact prefixLift 5874696
  have htrace : WordTrace (prefixWord ++ tailWord_5874696) baseStart_5874696 baseEnd_5874696 := by
    simpa [prefixWord, tailWord_5874696, baseEnd_5874696] using wordTrace_append hprefix tailTrace_5874696
  have hstable : (prefixWord ++ tailWord_5874696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874696).length < 2 ^ (prefixWord ++ tailWord_5874696).sum := by decide
  have hdescent : baseEnd_5874696 < baseStart_5874696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874709 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_5874709 : Nat := 118140960795 + 5874709 * 2 ^ 59
def prefixEnd_5874709 : Nat := 4983230072969 + 3 ^ 40 * 5874709 * 2
def baseEnd_5874709 : Nat := 1005516474098053635906737

theorem tailTrace_5874709 : CollatzResearch.WordTrace tailWord_5874709 prefixEnd_5874709 1005516474098053635906737 := by
  unfold tailWord_5874709
  simp only [CollatzResearch.WordTrace]
  refine ⟨214268240073940088263891181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142845493382626725509260787 214268240073940088263891181)
  ·
    refine ⟨80350590027727533098959193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214268240073940088263891181 80350590027727533098959193)
    ·
      refine ⟨60262942520795649824219395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80350590027727533098959193 60262942520795649824219395)
      ·
        refine ⟨90394413781193474736329093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60262942520795649824219395 90394413781193474736329093)
        ·
          refine ⟨16948952583973776513061705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90394413781193474736329093 16948952583973776513061705)
          ·
            refine ⟨12711714437980332384796279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16948952583973776513061705 12711714437980332384796279)
            ·
              refine ⟨19067571656970498577194419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12711714437980332384796279 19067571656970498577194419)
              ·
                refine ⟨28601357485455747865791629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19067571656970498577194419 28601357485455747865791629)
                ·
                  refine ⟨10725509057045905449671861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28601357485455747865791629 10725509057045905449671861)
                  ·
                    refine ⟨1005516474098053635906737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10725509057045905449671861 1005516474098053635906737)
                    ·
                      rfl

theorem cell23_5874709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_5874709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874709 prefixEnd_5874709 := by exact prefixLift 5874709
  have htrace : WordTrace (prefixWord ++ tailWord_5874709) baseStart_5874709 baseEnd_5874709 := by
    simpa [prefixWord, tailWord_5874709, baseEnd_5874709] using wordTrace_append hprefix tailTrace_5874709
  have hstable : (prefixWord ++ tailWord_5874709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874709).length < 2 ^ (prefixWord ++ tailWord_5874709).sum := by decide
  have hdescent : baseEnd_5874709 < baseStart_5874709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874759 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_5874759 : Nat := 118140960795 + 5874759 * 2 ^ 59
def prefixEnd_5874759 : Nat := 4983230072969 + 3 ^ 40 * 5874759 * 2
def baseEnd_5874759 : Nat := 3016575096326885712094981

theorem tailTrace_5874759 : CollatzResearch.WordTrace tailWord_5874759 prefixEnd_5874759 3016575096326885712094981 := by
  unfold tailWord_5874759
  simp only [CollatzResearch.WordTrace]
  refine ⟨214270063723758946803211331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142846709149172631202140887 214270063723758946803211331)
  ·
    refine ⟨321405095585638420204816997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214270063723758946803211331 321405095585638420204816997)
    ·
      refine ⟨60263455422307203788403187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321405095585638420204816997 60263455422307203788403187)
      ·
        refine ⟨90395183133460805682604781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60263455422307203788403187 90395183133460805682604781)
        ·
          refine ⟨33898193675047802130976793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90395183133460805682604781 33898193675047802130976793)
          ·
            refine ⟨25423645256285851598232595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33898193675047802130976793 25423645256285851598232595)
            ·
              refine ⟨38135467884428777397348893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25423645256285851598232595 38135467884428777397348893)
              ·
                refine ⟨14300800456660791524005835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38135467884428777397348893 14300800456660791524005835)
                ·
                  refine ⟨21451200684991187286008753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14300800456660791524005835 21451200684991187286008753)
                  ·
                    refine ⟨16088400513743390464506565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21451200684991187286008753 16088400513743390464506565)
                    ·
                      refine ⟨3016575096326885712094981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16088400513743390464506565 3016575096326885712094981)
                      ·
                        rfl

theorem cell23_5874759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_5874759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874759 prefixEnd_5874759 := by exact prefixLift 5874759
  have htrace : WordTrace (prefixWord ++ tailWord_5874759) baseStart_5874759 baseEnd_5874759 := by
    simpa [prefixWord, tailWord_5874759, baseEnd_5874759] using wordTrace_append hprefix tailTrace_5874759
  have hstable : (prefixWord ++ tailWord_5874759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874759).length < 2 ^ (prefixWord ++ tailWord_5874759).sum := by decide
  have hdescent : baseEnd_5874759 < baseStart_5874759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874766 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_5874766 : Nat := 118140960795 + 5874766 * 2 ^ 59
def prefixEnd_5874766 : Nat := 4983230072969 + 3 ^ 40 * 5874766 * 2
def baseEnd_5874766 : Nat := 3016578690691467184707449

theorem tailTrace_5874766 : CollatzResearch.WordTrace tailWord_5874766 prefixEnd_5874766 3016578690691467184707449 := by
  unfold tailWord_5874766
  simp only [CollatzResearch.WordTrace]
  refine ⟨26783789879341698374839519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142846879356489057999144101 26783789879341698374839519)
  ·
    refine ⟨40175684819012547562259279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26783789879341698374839519 40175684819012547562259279)
    ·
      refine ⟨60263527228518821343388919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40175684819012547562259279 60263527228518821343388919)
      ·
        refine ⟨90395290842778232015083379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60263527228518821343388919 90395290842778232015083379)
        ·
          refine ⟨135592936264167348022625069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90395290842778232015083379 135592936264167348022625069)
          ·
            refine ⟨50847351099062755508484401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135592936264167348022625069 50847351099062755508484401)
            ·
              refine ⟨38135513324297066631363301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50847351099062755508484401 38135513324297066631363301)
              ·
                refine ⟨7150408748305699993380619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38135513324297066631363301 7150408748305699993380619)
                ·
                  refine ⟨10725613122458549990070929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150408748305699993380619 10725613122458549990070929)
                  ·
                    refine ⟨8044209841843912492553197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10725613122458549990070929 8044209841843912492553197)
                    ·
                      refine ⟨3016578690691467184707449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8044209841843912492553197 3016578690691467184707449)
                      ·
                        rfl

theorem cell23_5874766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_5874766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874766 prefixEnd_5874766 := by exact prefixLift 5874766
  have htrace : WordTrace (prefixWord ++ tailWord_5874766) baseStart_5874766 baseEnd_5874766 := by
    simpa [prefixWord, tailWord_5874766, baseEnd_5874766] using wordTrace_append hprefix tailTrace_5874766
  have hstable : (prefixWord ++ tailWord_5874766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874766).length < 2 ^ (prefixWord ++ tailWord_5874766).sum := by decide
  have hdescent : baseEnd_5874766 < baseStart_5874766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874774 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5874774 : Nat := 118140960795 + 5874774 * 2 ^ 59
def prefixEnd_5874774 : Nat := 4983230072969 + 3 ^ 40 * 5874774 * 2
def baseEnd_5874774 : Nat := 3016582798536703153407413

theorem tailTrace_5874774 : CollatzResearch.WordTrace tailWord_5874774 prefixEnd_5874774 3016582798536703153407413 := by
  unfold tailWord_5874774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391913176169037772812961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142847073879136402910004917 13391913176169037772812961)
  ·
    refine ⟨10043934882126778329609721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13391913176169037772812961 10043934882126778329609721)
    ·
      refine ⟨7532951161595083747207291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10043934882126778329609721 7532951161595083747207291)
      ·
        refine ⟨11299426742392625620810937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7532951161595083747207291 11299426742392625620810937)
        ·
          refine ⟨8474570056794469215608203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11299426742392625620810937 8474570056794469215608203)
          ·
            refine ⟨12711855085191703823412305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474570056794469215608203 12711855085191703823412305)
            ·
              refine ⟨9533891313893777867559229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12711855085191703823412305 9533891313893777867559229)
              ·
                refine ⟨3575209242710166700334711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9533891313893777867559229 3575209242710166700334711)
                ·
                  refine ⟨5362813864065250050502067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575209242710166700334711 5362813864065250050502067)
                  ·
                    refine ⟨8044220796097875075753101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5362813864065250050502067 8044220796097875075753101)
                    ·
                      refine ⟨3016582798536703153407413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8044220796097875075753101 3016582798536703153407413)
                      ·
                        rfl

theorem cell23_5874774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5874774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874774 prefixEnd_5874774 := by exact prefixLift 5874774
  have htrace : WordTrace (prefixWord ++ tailWord_5874774) baseStart_5874774 baseEnd_5874774 := by
    simpa [prefixWord, tailWord_5874774, baseEnd_5874774] using wordTrace_append hprefix tailTrace_5874774
  have hstable : (prefixWord ++ tailWord_5874774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874774).length < 2 ^ (prefixWord ++ tailWord_5874774).sum := by decide
  have hdescent : baseEnd_5874774 < baseStart_5874774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874796 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_5874796 : Nat := 118140960795 + 5874796 * 2 ^ 59
def prefixEnd_5874796 : Nat := 4983230072969 + 3 ^ 40 * 5874796 * 2
def baseEnd_5874796 : Nat := 3016594095111102067332311

theorem tailTrace_5874796 : CollatzResearch.WordTrace tailWord_5874796 prefixEnd_5874796 3016594095111102067332311 := by
  unfold tailWord_5874796
  simp only [CollatzResearch.WordTrace]
  refine ⟨107135706612312451061154121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142847608816416601414872161 107135706612312451061154121)
  ·
    refine ⟨80351779959234338295865591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107135706612312451061154121 80351779959234338295865591)
    ·
      refine ⟨120527669938851507443798387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80351779959234338295865591 120527669938851507443798387)
      ·
        refine ⟨180791504908277261165697581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120527669938851507443798387 180791504908277261165697581)
        ·
          refine ⟨67796814340603972937136593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180791504908277261165697581 67796814340603972937136593)
          ·
            refine ⟨50847610755452979702852445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67796814340603972937136593 50847610755452979702852445)
            ·
              refine ⟨19067854033294867388569667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50847610755452979702852445 19067854033294867388569667)
              ·
                refine ⟨28601781049942301082854501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19067854033294867388569667 28601781049942301082854501)
                ·
                  refine ⟨5362833946864181453035219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28601781049942301082854501 5362833946864181453035219)
                  ·
                    refine ⟨8044250920296272179552829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5362833946864181453035219 8044250920296272179552829)
                    ·
                      refine ⟨3016594095111102067332311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8044250920296272179552829 3016594095111102067332311)
                      ·
                        rfl

theorem cell23_5874796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_5874796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874796 prefixEnd_5874796 := by exact prefixLift 5874796
  have htrace : WordTrace (prefixWord ++ tailWord_5874796) baseStart_5874796 baseEnd_5874796 := by
    simpa [prefixWord, tailWord_5874796, baseEnd_5874796] using wordTrace_append hprefix tailTrace_5874796
  have hstable : (prefixWord ++ tailWord_5874796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874796).length < 2 ^ (prefixWord ++ tailWord_5874796).sum := by decide
  have hdescent : baseEnd_5874796 < baseStart_5874796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874839 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5874839 : Nat := 118140960795 + 5874839 * 2 ^ 59
def prefixEnd_5874839 : Nat := 4983230072969 + 3 ^ 40 * 5874839 * 2
def baseEnd_5874839 : Nat := 3016616174779245399094613

theorem tailTrace_5874839 : CollatzResearch.WordTrace tailWord_5874839 prefixEnd_5874839 3016616174779245399094613 := by
  unfold tailWord_5874839
  simp only [CollatzResearch.WordTrace]
  refine ⟨214272981563469120466123571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142848654375646080310749047 214272981563469120466123571)
  ·
    refine ⟨321409472345203680699185357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214272981563469120466123571 321409472345203680699185357)
    ·
      refine ⟨120528552129451380262194509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321409472345203680699185357 120528552129451380262194509)
      ·
        refine ⟨45198207048544267598322941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120528552129451380262194509 45198207048544267598322941)
        ·
          refine ⟨16949327643204100349371103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45198207048544267598322941 16949327643204100349371103)
          ·
            refine ⟨25423991464806150524056655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16949327643204100349371103 25423991464806150524056655)
            ·
              refine ⟨38135987197209225786084983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25423991464806150524056655 38135987197209225786084983)
              ·
                refine ⟨57203980795813838679127475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38135987197209225786084983 57203980795813838679127475)
                ·
                  refine ⟨85805971193720758018691213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57203980795813838679127475 85805971193720758018691213)
                  ·
                    refine ⟨32177239197645284257009205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85805971193720758018691213 32177239197645284257009205)
                    ·
                      refine ⟨3016616174779245399094613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32177239197645284257009205 3016616174779245399094613)
                      ·
                        rfl

theorem cell23_5874839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5874839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874839 prefixEnd_5874839 := by exact prefixLift 5874839
  have htrace : WordTrace (prefixWord ++ tailWord_5874839) baseStart_5874839 baseEnd_5874839 := by
    simpa [prefixWord, tailWord_5874839, baseEnd_5874839] using wordTrace_append hprefix tailTrace_5874839
  have hstable : (prefixWord ++ tailWord_5874839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874839).length < 2 ^ (prefixWord ++ tailWord_5874839).sum := by decide
  have hdescent : baseEnd_5874839 < baseStart_5874839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874853 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 4, 2, 2]
def baseStart_5874853 : Nat := 118140960795 + 5874853 * 2 ^ 59
def prefixEnd_5874853 : Nat := 4983230072969 + 3 ^ 40 * 5874853 * 2
def baseEnd_5874853 : Nat := 3016623363508408344319549

theorem tailTrace_5874853 : CollatzResearch.WordTrace tailWord_5874853 prefixEnd_5874853 3016623363508408344319549 := by
  unfold tailWord_5874853
  simp only [CollatzResearch.WordTrace]
  refine ⟨214273492185418400857133213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142848994790278933904755475 214273492185418400857133213)
  ·
    refine ⟨80352559569531900321424955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214273492185418400857133213 80352559569531900321424955)
    ·
      refine ⟨120528839354297850482137433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80352559569531900321424955 120528839354297850482137433)
      ·
        refine ⟨90396629515723387861603075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120528839354297850482137433 90396629515723387861603075)
        ·
          refine ⟨135594944273585081792404613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90396629515723387861603075 135594944273585081792404613)
          ·
            refine ⟨25424052051297202836075865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135594944273585081792404613 25424052051297202836075865)
            ·
              refine ⟨19068039038472902127056899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25424052051297202836075865 19068039038472902127056899)
              ·
                refine ⟨28602058557709353190585349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19068039038472902127056899 28602058557709353190585349)
                ·
                  refine ⟨5362885979570503723234753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28602058557709353190585349 5362885979570503723234753)
                  ·
                    refine ⟨4022164484677877792426065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5362885979570503723234753 4022164484677877792426065)
                    ·
                      refine ⟨3016623363508408344319549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022164484677877792426065 3016623363508408344319549)
                      ·
                        rfl

theorem cell23_5874853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_5874853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874853 prefixEnd_5874853 := by exact prefixLift 5874853
  have htrace : WordTrace (prefixWord ++ tailWord_5874853) baseStart_5874853 baseEnd_5874853 := by
    simpa [prefixWord, tailWord_5874853, baseEnd_5874853] using wordTrace_append hprefix tailTrace_5874853
  have hstable : (prefixWord ++ tailWord_5874853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874853).length < 2 ^ (prefixWord ++ tailWord_5874853).sum := by decide
  have hdescent : baseEnd_5874853 < baseStart_5874853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874926 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_5874926 : Nat := 118140960795 + 5874926 * 2 ^ 59
def prefixEnd_5874926 : Nat := 4983230072969 + 3 ^ 40 * 5874926 * 2
def baseEnd_5874926 : Nat := 3016660847596186558706713

theorem tailTrace_5874926 : CollatzResearch.WordTrace tailWord_5874926 prefixEnd_5874926 3016660847596186558706713 := by
  unfold tailWord_5874926
  simp only [CollatzResearch.WordTrace]
  refine ⟨26784519339269241790567579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142850769809435956216360421 26784519339269241790567579)
  ·
    refine ⟨40176779008903862685851369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26784519339269241790567579 40176779008903862685851369)
    ·
      refine ⟨30132584256677897014388527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40176779008903862685851369 30132584256677897014388527)
      ·
        refine ⟨45198876385016845521582791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30132584256677897014388527 45198876385016845521582791)
        ·
          refine ⟨67798314577525268282374187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45198876385016845521582791 67798314577525268282374187)
          ·
            refine ⟨101697471866287902423561281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67798314577525268282374187 101697471866287902423561281)
            ·
              refine ⟨76273103899715926817670961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101697471866287902423561281 76273103899715926817670961)
              ·
                refine ⟨57204827924786945113253221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76273103899715926817670961 57204827924786945113253221)
                ·
                  refine ⟨10725905235897552208734979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57204827924786945113253221 10725905235897552208734979)
                  ·
                    refine ⟨16088857853846328313102469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10725905235897552208734979 16088857853846328313102469)
                    ·
                      refine ⟨3016660847596186558706713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16088857853846328313102469 3016660847596186558706713)
                      ·
                        rfl

theorem cell23_5874926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_5874926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874926 prefixEnd_5874926 := by exact prefixLift 5874926
  have htrace : WordTrace (prefixWord ++ tailWord_5874926) baseStart_5874926 baseEnd_5874926 := by
    simpa [prefixWord, tailWord_5874926, baseEnd_5874926] using wordTrace_append hprefix tailTrace_5874926
  have hstable : (prefixWord ++ tailWord_5874926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874926).length < 2 ^ (prefixWord ++ tailWord_5874926).sum := by decide
  have hdescent : baseEnd_5874926 < baseStart_5874926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874940 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_5874940 : Nat := 118140960795 + 5874940 * 2 ^ 59
def prefixEnd_5874940 : Nat := 4983230072969 + 3 ^ 40 * 5874940 * 2
def baseEnd_5874940 : Nat := 1005556012108449834643883

theorem tailTrace_5874940 : CollatzResearch.WordTrace tailWord_5874940 prefixEnd_5874940 1005556012108449834643883 := by
  unfold tailWord_5874940
  simp only [CollatzResearch.WordTrace]
  refine ⟨107138332668051607357775137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142851110224068809810366849 107138332668051607357775137)
  ·
    refine ⟨80353749501038705518331353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107138332668051607357775137 80353749501038705518331353)
    ·
      refine ⟨60265312125779029138748515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80353749501038705518331353 60265312125779029138748515)
      ·
        refine ⟨90397968188668543708122773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60265312125779029138748515 90397968188668543708122773)
        ·
          refine ⟨4237404758843837986318255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90397968188668543708122773 4237404758843837986318255)
          ·
            refine ⟨6356107138265756979477383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237404758843837986318255 6356107138265756979477383)
            ·
              refine ⟨9534160707398635469216075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6356107138265756979477383 9534160707398635469216075)
              ·
                refine ⟨14301241061097953203824113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534160707398635469216075 14301241061097953203824113)
                ·
                  refine ⟨10725930795823464902868085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301241061097953203824113 10725930795823464902868085)
                  ·
                    refine ⟨1005556012108449834643883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10725930795823464902868085 1005556012108449834643883)
                    ·
                      rfl

theorem cell23_5874940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_5874940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874940 prefixEnd_5874940 := by exact prefixLift 5874940
  have htrace : WordTrace (prefixWord ++ tailWord_5874940) baseStart_5874940 baseEnd_5874940 := by
    simpa [prefixWord, tailWord_5874940, baseEnd_5874940] using wordTrace_append hprefix tailTrace_5874940
  have hstable : (prefixWord ++ tailWord_5874940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874940).length < 2 ^ (prefixWord ++ tailWord_5874940).sum := by decide
  have hdescent : baseEnd_5874940 < baseStart_5874940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874943 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 4]
def baseStart_5874943 : Nat := 118140960795 + 5874943 * 2 ^ 59
def prefixEnd_5874943 : Nat := 4983230072969 + 3 ^ 40 * 5874943 * 2
def baseEnd_5874943 : Nat := 3016669576767312992194135

theorem tailTrace_5874943 : CollatzResearch.WordTrace tailWord_5874943 prefixEnd_5874943 3016669576767312992194135 := by
  unfold tailWord_5874943
  simp only [CollatzResearch.WordTrace]
  refine ⟨214276774755092346227909483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142851183170061564151939655 214276774755092346227909483)
  ·
    refine ⟨321415162132638519341864225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214276774755092346227909483 321415162132638519341864225)
    ·
      refine ⟨241061371599478889506398169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321415162132638519341864225 241061371599478889506398169)
      ·
        refine ⟨180796028699609167129798627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241061371599478889506398169 180796028699609167129798627)
        ·
          refine ⟨271194043049413750694697941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180796028699609167129798627 271194043049413750694697941)
          ·
            refine ⟨6356110383970634781906983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 271194043049413750694697941 6356110383970634781906983)
            ·
              refine ⟨9534165575955952172860475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6356110383970634781906983 9534165575955952172860475)
              ·
                refine ⟨14301248363933928259290713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534165575955952172860475 14301248363933928259290713)
                ·
                  refine ⟨10725936272950446194468035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301248363933928259290713 10725936272950446194468035)
                  ·
                    refine ⟨16088904409425669291702053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10725936272950446194468035 16088904409425669291702053)
                    ·
                      refine ⟨3016669576767312992194135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16088904409425669291702053 3016669576767312992194135)
                      ·
                        rfl

theorem cell23_5874943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_5874943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874943 prefixEnd_5874943 := by exact prefixLift 5874943
  have htrace : WordTrace (prefixWord ++ tailWord_5874943) baseStart_5874943 baseEnd_5874943 := by
    simpa [prefixWord, tailWord_5874943, baseEnd_5874943] using wordTrace_append hprefix tailTrace_5874943
  have hstable : (prefixWord ++ tailWord_5874943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874943).length < 2 ^ (prefixWord ++ tailWord_5874943).sum := by decide
  have hdescent : baseEnd_5874943 < baseStart_5874943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874949 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 8]
def baseStart_5874949 : Nat := 118140960795 + 5874949 * 2 ^ 59
def prefixEnd_5874949 : Nat := 4983230072969 + 3 ^ 40 * 5874949 * 2
def baseEnd_5874949 : Nat := 335185850850137774302123

theorem tailTrace_5874949 : CollatzResearch.WordTrace tailWord_5874949 prefixEnd_5874949 335185850850137774302123 := by
  unfold tailWord_5874949
  simp only [CollatzResearch.WordTrace]
  refine ⟨214276993593070609252627901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142851329062047072835085267 214276993593070609252627901)
  ·
    refine ⟨80353872597401478469735463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214276993593070609252627901 80353872597401478469735463)
    ·
      refine ⟨120530808896102217704603195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80353872597401478469735463 120530808896102217704603195)
      ·
        refine ⟨180796213344153326556904793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120530808896102217704603195 180796213344153326556904793)
        ·
          refine ⟨135597160008114994917678595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180796213344153326556904793 135597160008114994917678595)
          ·
            refine ⟨203395740012172492376517893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135597160008114994917678595 203395740012172492376517893)
            ·
              refine ⟨38136701252282342320597105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203395740012172492376517893 38136701252282342320597105)
              ·
                refine ⟨28602525939211756740447829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38136701252282342320597105 28602525939211756740447829)
                ·
                  refine ⟨335185850850137774302123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28602525939211756740447829 335185850850137774302123)
                  ·
                    rfl

theorem cell23_5874949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_5874949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874949 prefixEnd_5874949 := by exact prefixLift 5874949
  have htrace : WordTrace (prefixWord ++ tailWord_5874949) baseStart_5874949 baseEnd_5874949 := by
    simpa [prefixWord, tailWord_5874949, baseEnd_5874949] using wordTrace_append hprefix tailTrace_5874949
  have hstable : (prefixWord ++ tailWord_5874949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874949).length < 2 ^ (prefixWord ++ tailWord_5874949).sum := by decide
  have hdescent : baseEnd_5874949 < baseStart_5874949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5874970 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_5874970 : Nat := 118140960795 + 5874970 * 2 ^ 59
def prefixEnd_5874970 : Nat := 4983230072969 + 3 ^ 40 * 5874970 * 2
def baseEnd_5874970 : Nat := 1005561146914994795518837

theorem tailTrace_5874970 : CollatzResearch.WordTrace tailWord_5874970 prefixEnd_5874970 1005561146914994795518837 := by
  unfold tailWord_5874970
  simp only [CollatzResearch.WordTrace]
  refine ⟨53569439881498632459785591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142851839683996353226094909 53569439881498632459785591)
  ·
    refine ⟨80354159822247948689678387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53569439881498632459785591 80354159822247948689678387)
    ·
      refine ⟨120531239733371923034517581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80354159822247948689678387 120531239733371923034517581)
      ·
        refine ⟨45199214900014471137944093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120531239733371923034517581 45199214900014471137944093)
        ·
          refine ⟨16949705587505426676729035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45199214900014471137944093 16949705587505426676729035)
          ·
            refine ⟨25424558381258140015093553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16949705587505426676729035 25424558381258140015093553)
            ·
              refine ⟨19068418785943605011320165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25424558381258140015093553 19068418785943605011320165)
              ·
                refine ⟨3575328522364425939622531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19068418785943605011320165 3575328522364425939622531)
                ·
                  refine ⟨5362992783546638909433797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575328522364425939622531 5362992783546638909433797)
                  ·
                    refine ⟨1005561146914994795518837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362992783546638909433797 1005561146914994795518837)
                    ·
                      rfl

theorem cell23_5874970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_5874970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5874970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5874970 prefixEnd_5874970 := by exact prefixLift 5874970
  have htrace : WordTrace (prefixWord ++ tailWord_5874970) baseStart_5874970 baseEnd_5874970 := by
    simpa [prefixWord, tailWord_5874970, baseEnd_5874970] using wordTrace_append hprefix tailTrace_5874970
  have hstable : (prefixWord ++ tailWord_5874970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5874970).length < 2 ^ (prefixWord ++ tailWord_5874970).sum := by decide
  have hdescent : baseEnd_5874970 < baseStart_5874970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5874970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875014 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5875014 : Nat := 118140960795 + 5875014 * 2 ^ 59
def prefixEnd_5875014 : Nat := 4983230072969 + 3 ^ 40 * 5875014 * 2
def baseEnd_5875014 : Nat := 3016706033893782214406309

theorem tailTrace_5875014 : CollatzResearch.WordTrace tailWord_5875014 prefixEnd_5875014 3016706033893782214406309 := by
  unfold tailWord_5875014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6696230135557347667304503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142852909558556750235829397 6696230135557347667304503)
  ·
    refine ⟨10044345203336021500956755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6696230135557347667304503 10044345203336021500956755)
    ·
      refine ⟨15066517805004032251435133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10044345203336021500956755 15066517805004032251435133)
      ·
        refine ⟨5649944176876512094288175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15066517805004032251435133 5649944176876512094288175)
        ·
          refine ⟨8474916265314768141432263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649944176876512094288175 8474916265314768141432263)
          ·
            refine ⟨12712374397972152212148395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474916265314768141432263 12712374397972152212148395)
            ·
              refine ⟨19068561596958228318222593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12712374397972152212148395 19068561596958228318222593)
              ·
                refine ⟨14301421197718671238666945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19068561596958228318222593 14301421197718671238666945)
                ·
                  refine ⟨10726065898289003429000209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301421197718671238666945 10726065898289003429000209)
                  ·
                    refine ⟨8044549423716752571750157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10726065898289003429000209 8044549423716752571750157)
                    ·
                      refine ⟨3016706033893782214406309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8044549423716752571750157 3016706033893782214406309)
                      ·
                        rfl

theorem cell23_5875014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5875014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875014 prefixEnd_5875014 := by exact prefixLift 5875014
  have htrace : WordTrace (prefixWord ++ tailWord_5875014) baseStart_5875014 baseEnd_5875014 := by
    simpa [prefixWord, tailWord_5875014, baseEnd_5875014] using wordTrace_append hprefix tailTrace_5875014
  have hstable : (prefixWord ++ tailWord_5875014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875014).length < 2 ^ (prefixWord ++ tailWord_5875014).sum := by decide
  have hdescent : baseEnd_5875014 < baseStart_5875014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875016 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_5875016 : Nat := 118140960795 + 5875016 * 2 ^ 59
def prefixEnd_5875016 : Nat := 4983230072969 + 3 ^ 40 * 5875016 * 2
def baseEnd_5875016 : Nat := 3016707060855091206581299

theorem tailTrace_5875016 : CollatzResearch.WordTrace tailWord_5875016 prefixEnd_5875016 3016707060855091206581299 := by
  unfold tailWord_5875016
  simp only [CollatzResearch.WordTrace]
  refine ⟨107139718641913939847658451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142852958189218586463544601 107139718641913939847658451)
  ·
    refine ⟨160709577962870909771487677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107139718641913939847658451 160709577962870909771487677)
    ·
      refine ⟨60266091736076591164307879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160709577962870909771487677 60266091736076591164307879)
      ·
        refine ⟨90399137604114886746461819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60266091736076591164307879 90399137604114886746461819)
        ·
          refine ⟨135598706406172330119692729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90399137604114886746461819 135598706406172330119692729)
          ·
            refine ⟨101699029804629247589769547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135598706406172330119692729 101699029804629247589769547)
            ·
              refine ⟨152548544706943871384654321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101699029804629247589769547 152548544706943871384654321)
              ·
                refine ⟨114411408530207903538490741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152548544706943871384654321 114411408530207903538490741)
                ·
                  refine ⟨10726069549706990956733507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114411408530207903538490741 10726069549706990956733507)
                  ·
                    refine ⟨16089104324560486435100261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10726069549706990956733507 16089104324560486435100261)
                    ·
                      refine ⟨3016707060855091206581299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16089104324560486435100261 3016707060855091206581299)
                      ·
                        rfl

theorem cell23_5875016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_5875016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875016 prefixEnd_5875016 := by exact prefixLift 5875016
  have htrace : WordTrace (prefixWord ++ tailWord_5875016) baseStart_5875016 baseEnd_5875016 := by
    simpa [prefixWord, tailWord_5875016, baseEnd_5875016] using wordTrace_append hprefix tailTrace_5875016
  have hstable : (prefixWord ++ tailWord_5875016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875016).length < 2 ^ (prefixWord ++ tailWord_5875016).sum := by decide
  have hdescent : baseEnd_5875016 < baseStart_5875016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875020 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 2, 3, 2]
def baseStart_5875020 : Nat := 118140960795 + 5875020 * 2 ^ 59
def prefixEnd_5875020 : Nat := 4983230072969 + 3 ^ 40 * 5875020 * 2
def baseEnd_5875020 : Nat := 3016709114777709190931281

theorem tailTrace_5875020 : CollatzResearch.WordTrace tailWord_5875020 prefixEnd_5875020 3016709114777709190931281 := by
  unfold tailWord_5875020
  simp only [CollatzResearch.WordTrace]
  refine ⟨107139791587906694189231257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142853055450542258918975009 107139791587906694189231257)
  ·
    refine ⟨80354843690930020641923443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107139791587906694189231257 80354843690930020641923443)
    ·
      refine ⟨120532265536395030962885165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80354843690930020641923443 120532265536395030962885165)
      ·
        refine ⟨45199599576148136611081937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120532265536395030962885165 45199599576148136611081937)
        ·
          refine ⟨33899699682111102458311453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45199599576148136611081937 33899699682111102458311453)
          ·
            refine ⟨12712387380791663421866795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33899699682111102458311453 12712387380791663421866795)
            ·
              refine ⟨19068581071187495132800193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12712387380791663421866795 19068581071187495132800193)
              ·
                refine ⟨14301435803390621349600145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19068581071187495132800193 14301435803390621349600145)
                ·
                  refine ⟨10726076852542966012200109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301435803390621349600145 10726076852542966012200109)
                  ·
                    refine ⟨4022278819703612254575041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10726076852542966012200109 4022278819703612254575041)
                    ·
                      refine ⟨3016709114777709190931281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022278819703612254575041 3016709114777709190931281)
                      ·
                        rfl

theorem cell23_5875020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_5875020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875020 prefixEnd_5875020 := by exact prefixLift 5875020
  have htrace : WordTrace (prefixWord ++ tailWord_5875020) baseStart_5875020 baseEnd_5875020 := by
    simpa [prefixWord, tailWord_5875020, baseEnd_5875020] using wordTrace_append hprefix tailTrace_5875020
  have hstable : (prefixWord ++ tailWord_5875020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875020).length < 2 ^ (prefixWord ++ tailWord_5875020).sum := by decide
  have hdescent : baseEnd_5875020 < baseStart_5875020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875021 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_5875021 : Nat := 118140960795 + 5875021 * 2 ^ 59
def prefixEnd_5875021 : Nat := 4983230072969 + 3 ^ 40 * 5875021 * 2
def baseEnd_5875021 : Nat := 1005569876086121229006259

theorem tailTrace_5875021 : CollatzResearch.WordTrace tailWord_5875021 prefixEnd_5875021 1005569876086121229006259 := by
  unfold tailWord_5875021
  simp only [CollatzResearch.WordTrace]
  refine ⟨214279619648809765549248917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142853079765873177032832611 214279619648809765549248917)
  ·
    refine ⟨10044357171037957760121043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214279619648809765549248917 10044357171037957760121043)
    ·
      refine ⟨15066535756556936640181565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10044357171037957760121043 15066535756556936640181565)
      ·
        refine ⟨5649950908708851240068087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15066535756556936640181565 5649950908708851240068087)
        ·
          refine ⟨8474926363063276860102131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649950908708851240068087 8474926363063276860102131)
          ·
            refine ⟨12712389544594915290153197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474926363063276860102131 12712389544594915290153197)
            ·
              refine ⟨4767146079223093233807449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12712389544594915290153197 4767146079223093233807449)
              ·
                refine ⟨3575359559417319925355587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4767146079223093233807449 3575359559417319925355587)
                ·
                  refine ⟨5363039339125979888033381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575359559417319925355587 5363039339125979888033381)
                  ·
                    refine ⟨1005569876086121229006259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363039339125979888033381 1005569876086121229006259)
                    ·
                      rfl

theorem cell23_5875021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_5875021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875021 prefixEnd_5875021 := by exact prefixLift 5875021
  have htrace : WordTrace (prefixWord ++ tailWord_5875021) baseStart_5875021 baseEnd_5875021 := by
    simpa [prefixWord, tailWord_5875021, baseEnd_5875021] using wordTrace_append hprefix tailTrace_5875021
  have hstable : (prefixWord ++ tailWord_5875021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875021).length < 2 ^ (prefixWord ++ tailWord_5875021).sum := by decide
  have hdescent : baseEnd_5875021 < baseStart_5875021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875027 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 1, 1, 3]
def baseStart_5875027 : Nat := 118140960795 + 5875027 * 2 ^ 59
def prefixEnd_5875027 : Nat := 4983230072969 + 3 ^ 40 * 5875027 * 2
def baseEnd_5875027 : Nat := 3016712709142290663543749

theorem tailTrace_5875027 : CollatzResearch.WordTrace tailWord_5875027 prefixEnd_5875027 3016712709142290663543749 := by
  unfold tailWord_5875027
  simp only [CollatzResearch.WordTrace]
  refine ⟨214279838486788028573967335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142853225657858685715978223 214279838486788028573967335)
  ·
    refine ⟨321419757730182042860951003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214279838486788028573967335 321419757730182042860951003)
    ·
      refine ⟨482129636595273064291426505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321419757730182042860951003 482129636595273064291426505)
      ·
        refine ⟨361597227446454798218569879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482129636595273064291426505 361597227446454798218569879)
        ·
          refine ⟨542395841169682197327854819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361597227446454798218569879 542395841169682197327854819)
          ·
            refine ⟨813593761754523295991782229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542395841169682197327854819 813593761754523295991782229)
            ·
              refine ⟨4767150947780409937451849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 813593761754523295991782229 4767150947780409937451849)
              ·
                refine ⟨3575363210835307453088887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4767150947780409937451849 3575363210835307453088887)
                ·
                  refine ⟨5363044816252961179633331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575363210835307453088887 5363044816252961179633331)
                  ·
                    refine ⟨8044567224379441769449997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5363044816252961179633331 8044567224379441769449997)
                    ·
                      refine ⟨3016712709142290663543749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8044567224379441769449997 3016712709142290663543749)
                      ·
                        rfl

theorem cell23_5875027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 1, 3].length) (baseStart_5875027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875027 prefixEnd_5875027 := by exact prefixLift 5875027
  have htrace : WordTrace (prefixWord ++ tailWord_5875027) baseStart_5875027 baseEnd_5875027 := by
    simpa [prefixWord, tailWord_5875027, baseEnd_5875027] using wordTrace_append hprefix tailTrace_5875027
  have hstable : (prefixWord ++ tailWord_5875027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875027).length < 2 ^ (prefixWord ++ tailWord_5875027).sum := by decide
  have hdescent : baseEnd_5875027 < baseStart_5875027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875047 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 1, 5]
def baseStart_5875047 : Nat := 118140960795 + 5875047 * 2 ^ 59
def prefixEnd_5875047 : Nat := 4983230072969 + 3 ^ 40 * 5875047 * 2
def baseEnd_5875047 : Nat := 1005574326251793528431219

theorem tailTrace_5875047 : CollatzResearch.WordTrace tailWord_5875047 prefixEnd_5875047 1005574326251793528431219 := by
  unfold tailWord_5875047
  simp only [CollatzResearch.WordTrace]
  refine ⟨214280567946715571989695395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142853711964477047993130263 214280567946715571989695395)
  ·
    refine ⟨321420851920073357984543093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214280567946715571989695395 321420851920073357984543093)
    ·
      refine ⟨30133204867506877311050915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321420851920073357984543093 30133204867506877311050915)
      ·
        refine ⟨45199807301260315966576373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30133204867506877311050915 45199807301260315966576373)
        ·
          refine ⟨4237481934493154621866535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45199807301260315966576373 4237481934493154621866535)
          ·
            refine ⟨6356222901739731932799803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237481934493154621866535 6356222901739731932799803)
            ·
              refine ⟨9534334352609597899199705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6356222901739731932799803 9534334352609597899199705)
              ·
                refine ⟨7150750764457198424399779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9534334352609597899199705 7150750764457198424399779)
                ·
                  refine ⟨10726126146685797636599669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150750764457198424399779 10726126146685797636599669)
                  ·
                    refine ⟨1005574326251793528431219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10726126146685797636599669 1005574326251793528431219)
                    ·
                      rfl

theorem cell23_5875047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_5875047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875047 prefixEnd_5875047 := by exact prefixLift 5875047
  have htrace : WordTrace (prefixWord ++ tailWord_5875047) baseStart_5875047 baseEnd_5875047 := by
    simpa [prefixWord, tailWord_5875047, baseEnd_5875047] using wordTrace_append hprefix tailTrace_5875047
  have hstable : (prefixWord ++ tailWord_5875047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875047).length < 2 ^ (prefixWord ++ tailWord_5875047).sum := by decide
  have hdescent : baseEnd_5875047 < baseStart_5875047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875050 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5875050 : Nat := 118140960795 + 5875050 * 2 ^ 59
def prefixEnd_5875050 : Nat := 4983230072969 + 3 ^ 40 * 5875050 * 2
def baseEnd_5875050 : Nat := 3016724519197344073556143

theorem tailTrace_5875050 : CollatzResearch.WordTrace tailWord_5875050 prefixEnd_5875050 3016724519197344073556143 := by
  unfold tailWord_5875050
  simp only [CollatzResearch.WordTrace]
  refine ⟨53570169341426175875513651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142853784910469802334703069 53570169341426175875513651)
  ·
    refine ⟨80355254012139263813270477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53570169341426175875513651 80355254012139263813270477)
    ·
      refine ⟨30133220254552223929976429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80355254012139263813270477 30133220254552223929976429)
      ·
        refine ⟨11299957595457083973741161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30133220254552223929976429 11299957595457083973741161)
        ·
          refine ⟨8474968196592812980305871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11299957595457083973741161 8474968196592812980305871)
          ·
            refine ⟨12712452294889219470458807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474968196592812980305871 12712452294889219470458807)
            ·
              refine ⟨19068678442333829205688211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12712452294889219470458807 19068678442333829205688211)
              ·
                refine ⟨28603017663500743808532317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19068678442333829205688211 28603017663500743808532317)
                ·
                  refine ⟨10726131623812778928199619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28603017663500743808532317 10726131623812778928199619)
                  ·
                    refine ⟨16089197435719168392299429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10726131623812778928199619 16089197435719168392299429)
                    ·
                      refine ⟨3016724519197344073556143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16089197435719168392299429 3016724519197344073556143)
                      ·
                        rfl

theorem cell23_5875050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5875050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875050 prefixEnd_5875050 := by exact prefixLift 5875050
  have htrace : WordTrace (prefixWord ++ tailWord_5875050) baseStart_5875050 baseEnd_5875050 := by
    simpa [prefixWord, tailWord_5875050, baseEnd_5875050] using wordTrace_append hprefix tailTrace_5875050
  have hstable : (prefixWord ++ tailWord_5875050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875050).length < 2 ^ (prefixWord ++ tailWord_5875050).sum := by decide
  have hdescent : baseEnd_5875050 < baseStart_5875050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875054 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5875054 : Nat := 118140960795 + 5875054 * 2 ^ 59
def prefixEnd_5875054 : Nat := 4983230072969 + 3 ^ 40 * 5875054 * 2
def baseEnd_5875054 : Nat := 3016726573119962057906125

theorem tailTrace_5875054 : CollatzResearch.WordTrace tailWord_5875054 prefixEnd_5875054 3016726573119962057906125 := by
  unfold tailWord_5875054
  simp only [CollatzResearch.WordTrace]
  refine ⟨26785102907211276523150027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142853882171793474790133477 26785102907211276523150027)
  ·
    refine ⟨40177654360816914784725041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26785102907211276523150027 40177654360816914784725041)
    ·
      refine ⟨30133240770612686088543781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40177654360816914784725041 30133240770612686088543781)
      ·
        refine ⟨5649982644489878641601959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30133240770612686088543781 5649982644489878641601959)
        ·
          refine ⟨8474973966734817962402939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649982644489878641601959 8474973966734817962402939)
          ·
            refine ⟨12712460950102226943604409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474973966734817962402939 12712460950102226943604409)
            ·
              refine ⟨9534345712576670207703307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12712460950102226943604409 9534345712576670207703307)
              ·
                refine ⟨14301518568865005311554961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534345712576670207703307 14301518568865005311554961)
                ·
                  refine ⟨10726138926648753983666221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301518568865005311554961 10726138926648753983666221)
                  ·
                    refine ⟨4022302097493282743874833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10726138926648753983666221 4022302097493282743874833)
                    ·
                      refine ⟨3016726573119962057906125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022302097493282743874833 3016726573119962057906125)
                      ·
                        rfl

theorem cell23_5875054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5875054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875054 prefixEnd_5875054 := by exact prefixLift 5875054
  have htrace : WordTrace (prefixWord ++ tailWord_5875054) baseStart_5875054 baseEnd_5875054 := by
    simpa [prefixWord, tailWord_5875054, baseEnd_5875054] using wordTrace_append hprefix tailTrace_5875054
  have hstable : (prefixWord ++ tailWord_5875054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875054).length < 2 ^ (prefixWord ++ tailWord_5875054).sum := by decide
  have hdescent : baseEnd_5875054 < baseStart_5875054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875067 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 1, 2, 2]
def baseStart_5875067 : Nat := 118140960795 + 5875067 * 2 ^ 59
def prefixEnd_5875067 : Nat := 4983230072969 + 3 ^ 40 * 5875067 * 2
def baseEnd_5875067 : Nat := 3016733248368470507043565

theorem tailTrace_5875067 : CollatzResearch.WordTrace tailWord_5875067 prefixEnd_5875067 3016733248368470507043565 := by
  unfold tailWord_5875067
  simp only [CollatzResearch.WordTrace]
  refine ⟨214281297406643115405423455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142854198271095410270282303 214281297406643115405423455)
  ·
    refine ⟨321421946109964673108135183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214281297406643115405423455 321421946109964673108135183)
    ·
      refine ⟨482132919164947009662202775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321421946109964673108135183 482132919164947009662202775)
      ·
        refine ⟨723199378747420514493304163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482132919164947009662202775 723199378747420514493304163)
        ·
          refine ⟨1084799068121130771739956245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723199378747420514493304163 1084799068121130771739956245)
          ·
            refine ⟨50849956318178004925310449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1084799068121130771739956245 50849956318178004925310449)
            ·
              refine ⟨38137467238633503693982837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50849956318178004925310449 38137467238633503693982837)
              ·
                refine ⟨3575387553621890971310891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38137467238633503693982837 3575387553621890971310891)
                ·
                  refine ⟨5363081330432836456966337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575387553621890971310891 5363081330432836456966337)
                  ·
                    refine ⟨4022310997824627342724753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363081330432836456966337 4022310997824627342724753)
                    ·
                      refine ⟨3016733248368470507043565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022310997824627342724753 3016733248368470507043565)
                      ·
                        rfl

theorem cell23_5875067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 2, 2].length) (baseStart_5875067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875067 prefixEnd_5875067 := by exact prefixLift 5875067
  have htrace : WordTrace (prefixWord ++ tailWord_5875067) baseStart_5875067 baseEnd_5875067 := by
    simpa [prefixWord, tailWord_5875067, baseEnd_5875067] using wordTrace_append hprefix tailTrace_5875067
  have hstable : (prefixWord ++ tailWord_5875067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875067).length < 2 ^ (prefixWord ++ tailWord_5875067).sum := by decide
  have hdescent : baseEnd_5875067 < baseStart_5875067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875073 : List Nat := [1, 2, 4, 3, 3, 10]
def baseStart_5875073 : Nat := 118140960795 + 5875073 * 2 ^ 59
def prefixEnd_5875073 : Nat := 4983230072969 + 3 ^ 40 * 5875073 * 2
def baseEnd_5875073 : Nat := 12414552795277355899459

theorem tailTrace_5875073 : CollatzResearch.WordTrace tailWord_5875073 prefixEnd_5875073 12414552795277355899459 := by
  unfold tailWord_5875073
  simp only [CollatzResearch.WordTrace]
  refine ⟨214281516244621378430141873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142854344163080918953427915 214281516244621378430141873)
  ·
    refine ⟨160711137183466033822606405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214281516244621378430141873 160711137183466033822606405)
    ·
      refine ⟨30133338221899881341738701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160711137183466033822606405 30133338221899881341738701)
      ·
        refine ⟨11300001833212455503152013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30133338221899881341738701 11300001833212455503152013)
        ·
          refine ⟨4237500687454670813682005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11300001833212455503152013 4237500687454670813682005)
          ·
            refine ⟨12414552795277355899459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4237500687454670813682005 12414552795277355899459)
            ·
              rfl

theorem cell23_5875073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 10].length) (baseStart_5875073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875073 prefixEnd_5875073 := by exact prefixLift 5875073
  have htrace : WordTrace (prefixWord ++ tailWord_5875073) baseStart_5875073 baseEnd_5875073 := by
    simpa [prefixWord, tailWord_5875073, baseEnd_5875073] using wordTrace_append hprefix tailTrace_5875073
  have hstable : (prefixWord ++ tailWord_5875073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875073).length < 2 ^ (prefixWord ++ tailWord_5875073).sum := by decide
  have hdescent : baseEnd_5875073 < baseStart_5875073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875197 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 5]
def baseStart_5875197 : Nat := 118140960795 + 5875197 * 2 ^ 59
def prefixEnd_5875197 : Nat := 4983230072969 + 3 ^ 40 * 5875197 * 2
def baseEnd_5875197 : Nat := 335200000094839444268663

theorem tailTrace_5875197 : CollatzResearch.WordTrace tailWord_5875197 prefixEnd_5875197 335200000094839444268663 := by
  unfold tailWord_5875197
  simp only [CollatzResearch.WordTrace]
  refine ⟨214286038896172147607655845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142857359264114765071770563 214286038896172147607655845)
  ·
    refine ⟨40178632293032277676435471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214286038896172147607655845 40178632293032277676435471)
    ·
      refine ⟨60267948439548416514653207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40178632293032277676435471 60267948439548416514653207)
      ·
        refine ⟨90401922659322624771979811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60267948439548416514653207 90401922659322624771979811)
        ·
          refine ⟨135602883988983937157969717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90401922659322624771979811 135602883988983937157969717)
          ·
            refine ⟨12712770373967244108559661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135602883988983937157969717 12712770373967244108559661)
            ·
              refine ⟨4767288890237716540709873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12712770373967244108559661 4767288890237716540709873)
              ·
                refine ⟨3575466667678287405532405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4767288890237716540709873 3575466667678287405532405)
                ·
                  refine ⟨335200000094839444268663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3575466667678287405532405 335200000094839444268663)
                  ·
                    rfl

theorem cell23_5875197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_5875197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875197 prefixEnd_5875197 := by exact prefixLift 5875197
  have htrace : WordTrace (prefixWord ++ tailWord_5875197) baseStart_5875197 baseEnd_5875197 := by
    simpa [prefixWord, tailWord_5875197, baseEnd_5875197] using wordTrace_append hprefix tailTrace_5875197
  have hstable : (prefixWord ++ tailWord_5875197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875197).length < 2 ^ (prefixWord ++ tailWord_5875197).sum := by decide
  have hdescent : baseEnd_5875197 < baseStart_5875197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875313 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_5875313 : Nat := 118140960795 + 5875313 * 2 ^ 59
def prefixEnd_5875313 : Nat := 4983230072969 + 3 ^ 40 * 5875313 * 2
def baseEnd_5875313 : Nat := 1005619854869825514855811

theorem tailTrace_5875313 : CollatzResearch.WordTrace tailWord_5875313 prefixEnd_5875313 1005619854869825514855811 := by
  unfold tailWord_5875313
  simp only [CollatzResearch.WordTrace]
  refine ⟨214290269763751899418878593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142860179842501266279252395 214290269763751899418878593)
  ·
    refine ⟨160717702322813924564158945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214290269763751899418878593 160717702322813924564158945)
    ·
      refine ⟨120538276742110443423119209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160717702322813924564158945 120538276742110443423119209)
      ·
        refine ⟨90403707556582832567339407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120538276742110443423119209 90403707556582832567339407)
        ·
          refine ⟨135605561334874248851009111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90403707556582832567339407 135605561334874248851009111)
          ·
            refine ⟨203408342002311373276513667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135605561334874248851009111 203408342002311373276513667)
            ·
              refine ⟨305112513003467059914770501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203408342002311373276513667 305112513003467059914770501)
              ·
                refine ⟨57208596188150073734019469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305112513003467059914770501 57208596188150073734019469)
                ·
                  refine ⟨21453223570556277650257301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57208596188150073734019469 21453223570556277650257301)
                  ·
                    refine ⟨1005619854869825514855811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21453223570556277650257301 1005619854869825514855811)
                    ·
                      rfl

theorem cell23_5875313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_5875313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875313 prefixEnd_5875313 := by exact prefixLift 5875313
  have htrace : WordTrace (prefixWord ++ tailWord_5875313) baseStart_5875313 baseEnd_5875313 := by
    simpa [prefixWord, tailWord_5875313, baseEnd_5875313] using wordTrace_append hprefix tailTrace_5875313
  have hstable : (prefixWord ++ tailWord_5875313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875313).length < 2 ^ (prefixWord ++ tailWord_5875313).sum := by decide
  have hdescent : baseEnd_5875313 < baseStart_5875313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875314 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_5875314 : Nat := 118140960795 + 5875314 * 2 ^ 59
def prefixEnd_5875314 : Nat := 4983230072969 + 3 ^ 40 * 5875314 * 2
def baseEnd_5875314 : Nat := 3016860078090131040654929

theorem tailTrace_5875314 : CollatzResearch.WordTrace tailWord_5875314 prefixEnd_5875314 3016860078090131040654929 := by
  unfold tailWord_5875314
  simp only [CollatzResearch.WordTrace]
  refine ⟨53572576559187069147416249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142860204157832184393109997 53572576559187069147416249)
  ·
    refine ⟨40179432419390301860562187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53572576559187069147416249 40179432419390301860562187)
    ·
      refine ⟨60269148629085452790843281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40179432419390301860562187 60269148629085452790843281)
      ·
        refine ⟨45201861471814089593132461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60269148629085452790843281 45201861471814089593132461)
        ·
          refine ⟨16950698051930283597424673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45201861471814089593132461 16950698051930283597424673)
          ·
            refine ⟨12713023538947712698068505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16950698051930283597424673 12713023538947712698068505)
            ·
              refine ⟨9534767654210784523551379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12713023538947712698068505 9534767654210784523551379)
              ·
                refine ⟨14302151481316176785327069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534767654210784523551379 14302151481316176785327069)
                ·
                  refine ⟨5363306805493566294497651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14302151481316176785327069 5363306805493566294497651)
                  ·
                    refine ⟨8044960208240349441746477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5363306805493566294497651 8044960208240349441746477)
                    ·
                      refine ⟨3016860078090131040654929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8044960208240349441746477 3016860078090131040654929)
                      ·
                        rfl

theorem cell23_5875314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_5875314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875314 prefixEnd_5875314 := by exact prefixLift 5875314
  have htrace : WordTrace (prefixWord ++ tailWord_5875314) baseStart_5875314 baseEnd_5875314 := by
    simpa [prefixWord, tailWord_5875314, baseEnd_5875314] using wordTrace_append hprefix tailTrace_5875314
  have hstable : (prefixWord ++ tailWord_5875314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875314).length < 2 ^ (prefixWord ++ tailWord_5875314).sum := by decide
  have hdescent : baseEnd_5875314 < baseStart_5875314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875320 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 6, 2]
def baseStart_5875320 : Nat := 118140960795 + 5875320 * 2 ^ 59
def prefixEnd_5875320 : Nat := 4983230072969 + 3 ^ 40 * 5875320 * 2
def baseEnd_5875320 : Nat := 3016863158974058017179901

theorem tailTrace_5875320 : CollatzResearch.WordTrace tailWord_5875320 prefixEnd_5875320 3016863158974058017179901 := by
  unfold tailWord_5875320
  simp only [CollatzResearch.WordTrace]
  refine ⟨107145262537363269807191707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142860350049817693076255609 107145262537363269807191707)
  ·
    refine ⟨160717893806044904710787561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107145262537363269807191707 160717893806044904710787561)
    ·
      refine ⟨120538420354533678533090671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160717893806044904710787561 120538420354533678533090671)
      ·
        refine ⟨180807630531800517799636007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120538420354533678533090671 180807630531800517799636007)
        ·
          refine ⟨271211445797700776699454011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180807630531800517799636007 271211445797700776699454011)
          ·
            refine ⟨406817168696551165049181017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271211445797700776699454011 406817168696551165049181017)
            ·
              refine ⟨305112876522413373786885763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406817168696551165049181017 305112876522413373786885763)
              ·
                refine ⟨457669314783620060680328645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305112876522413373786885763 457669314783620060680328645)
                ·
                  refine ⟨85812996521928761377561621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457669314783620060680328645 85812996521928761377561621)
                  ·
                    refine ⟨4022484211965410689573201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85812996521928761377561621 4022484211965410689573201)
                    ·
                      refine ⟨3016863158974058017179901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022484211965410689573201 3016863158974058017179901)
                      ·
                        rfl

theorem cell23_5875320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_5875320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875320 prefixEnd_5875320 := by exact prefixLift 5875320
  have htrace : WordTrace (prefixWord ++ tailWord_5875320) baseStart_5875320 baseEnd_5875320 := by
    simpa [prefixWord, tailWord_5875320, baseEnd_5875320] using wordTrace_append hprefix tailTrace_5875320
  have hstable : (prefixWord ++ tailWord_5875320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875320).length < 2 ^ (prefixWord ++ tailWord_5875320).sum := by decide
  have hdescent : baseEnd_5875320 < baseStart_5875320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875360 : List Nat := [2, 1, 1, 4, 3, 3, 9]
def baseStart_5875360 : Nat := 118140960795 + 5875360 * 2 ^ 59
def prefixEnd_5875360 : Nat := 4983230072969 + 3 ^ 40 * 5875360 * 2
def baseEnd_5875360 : Nat := 37245477755558492107157

theorem tailTrace_5875360 : CollatzResearch.WordTrace tailWord_5875360 prefixEnd_5875360 37245477755558492107157 := by
  unfold tailWord_5875360
  simp only [CollatzResearch.WordTrace]
  refine ⟨107145991997290813222919767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142861322663054417630559689 107145991997290813222919767)
  ·
    refine ⟨160718987995936219834379651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107145991997290813222919767 160718987995936219834379651)
    ·
      refine ⟨241078481993904329751569477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160718987995936219834379651 241078481993904329751569477)
      ·
        refine ⟨45202215373857061828419277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241078481993904329751569477 45202215373857061828419277)
        ·
          refine ⟨16950830765196398185657229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45202215373857061828419277 16950830765196398185657229)
          ·
            refine ⟨6356561536948649319621461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16950830765196398185657229 6356561536948649319621461)
            ·
              refine ⟨37245477755558492107157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6356561536948649319621461 37245477755558492107157)
              ·
                rfl

theorem cell23_5875360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 9].length) (baseStart_5875360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875360 prefixEnd_5875360 := by exact prefixLift 5875360
  have htrace : WordTrace (prefixWord ++ tailWord_5875360) baseStart_5875360 baseEnd_5875360 := by
    simpa [prefixWord, tailWord_5875360, baseEnd_5875360] using wordTrace_append hprefix tailTrace_5875360
  have hstable : (prefixWord ++ tailWord_5875360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875360).length < 2 ^ (prefixWord ++ tailWord_5875360).sum := by decide
  have hdescent : baseEnd_5875360 < baseStart_5875360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875397 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 3, 3, 2]
def baseStart_5875397 : Nat := 118140960795 + 5875397 * 2 ^ 59
def prefixEnd_5875397 : Nat := 4983230072969 + 3 ^ 40 * 5875397 * 2
def baseEnd_5875397 : Nat := 3016902696984454215917047

theorem tailTrace_5875397 : CollatzResearch.WordTrace tailWord_5875397 prefixEnd_5875397 3016902696984454215917047 := by
  unfold tailWord_5875397
  simp only [CollatzResearch.WordTrace]
  refine ⟨214293333495447581764936445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142862222330298387843290963 214293333495447581764936445)
  ·
    refine ⟨80360000060792843161851167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214293333495447581764936445 80360000060792843161851167)
    ·
      refine ⟨120540000091189264742776751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80360000060792843161851167 120540000091189264742776751)
      ·
        refine ⟨180810000136783897114165127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120540000091189264742776751 180810000136783897114165127)
        ·
          refine ⟨271215000205175845671247691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180810000136783897114165127 271215000205175845671247691)
          ·
            refine ⟨406822500307763768506871537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271215000205175845671247691 406822500307763768506871537)
            ·
              refine ⟨305116875230822826380153653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406822500307763768506871537 305116875230822826380153653)
              ·
                refine ⟨28604707052889639973139405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305116875230822826380153653 28604707052889639973139405)
                ·
                  refine ⟨10726765144833614989927277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28604707052889639973139405 10726765144833614989927277)
                  ·
                    refine ⟨4022536929312605621222729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10726765144833614989927277 4022536929312605621222729)
                    ·
                      refine ⟨3016902696984454215917047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022536929312605621222729 3016902696984454215917047)
                      ·
                        rfl

theorem cell23_5875397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_5875397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875397 prefixEnd_5875397 := by exact prefixLift 5875397
  have htrace : WordTrace (prefixWord ++ tailWord_5875397) baseStart_5875397 baseEnd_5875397 := by
    simpa [prefixWord, tailWord_5875397, baseEnd_5875397] using wordTrace_append hprefix tailTrace_5875397
  have hstable : (prefixWord ++ tailWord_5875397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875397).length < 2 ^ (prefixWord ++ tailWord_5875397).sum := by decide
  have hdescent : baseEnd_5875397 < baseStart_5875397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875404 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5875404 : Nat := 118140960795 + 5875404 * 2 ^ 59
def prefixEnd_5875404 : Nat := 4983230072969 + 3 ^ 40 * 5875404 * 2
def baseEnd_5875404 : Nat := 3016906291349035688529515

theorem tailTrace_5875404 : CollatzResearch.WordTrace tailWord_5875404 prefixEnd_5875404 3016906291349035688529515 := by
  unfold tailWord_5875404
  simp only [CollatzResearch.WordTrace]
  refine ⟨107146794403211110980220633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142862392537614814640294177 107146794403211110980220633)
  ·
    refine ⟨80360095802408333235165475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107146794403211110980220633 80360095802408333235165475)
    ·
      refine ⟨120540143703612499852748213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80360095802408333235165475 120540143703612499852748213)
      ·
        refine ⟨11300638472213671861195145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120540143703612499852748213 11300638472213671861195145)
        ·
          refine ⟨8475478854160253895896359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11300638472213671861195145 8475478854160253895896359)
          ·
            refine ⟨12713218281240380843844539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8475478854160253895896359 12713218281240380843844539)
            ·
              refine ⟨19069827421860571265766809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12713218281240380843844539 19069827421860571265766809)
              ·
                refine ⟨14302370566395428449325107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19069827421860571265766809 14302370566395428449325107)
                ·
                  refine ⟨21453555849593142673987661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14302370566395428449325107 21453555849593142673987661)
                  ·
                    refine ⟨8045083443597428502745373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21453555849593142673987661 8045083443597428502745373)
                    ·
                      refine ⟨3016906291349035688529515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045083443597428502745373 3016906291349035688529515)
                      ·
                        rfl

theorem cell23_5875404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5875404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875404 prefixEnd_5875404 := by exact prefixLift 5875404
  have htrace : WordTrace (prefixWord ++ tailWord_5875404) baseStart_5875404 baseEnd_5875404 := by
    simpa [prefixWord, tailWord_5875404, baseEnd_5875404] using wordTrace_append hprefix tailTrace_5875404
  have hstable : (prefixWord ++ tailWord_5875404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875404).length < 2 ^ (prefixWord ++ tailWord_5875404).sum := by decide
  have hdescent : baseEnd_5875404 < baseStart_5875404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875437 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_5875437 : Nat := 118140960795 + 5875437 * 2 ^ 59
def prefixEnd_5875437 : Nat := 4983230072969 + 3 ^ 40 * 5875437 * 2
def baseEnd_5875437 : Nat := 1005641078736878019805621

theorem tailTrace_5875437 : CollatzResearch.WordTrace tailWord_5875437 prefixEnd_5875437 1005641078736878019805621 := by
  unfold tailWord_5875437
  simp only [CollatzResearch.WordTrace]
  refine ⟨214294792415302668596392565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142863194943535112397595043 214294792415302668596392565)
  ·
    refine ⟨20090136788934625180911803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214294792415302668596392565 20090136788934625180911803)
    ·
      refine ⟨30135205183401937771367705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20090136788934625180911803 30135205183401937771367705)
      ·
        refine ⟨22601403887551453328525779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30135205183401937771367705 22601403887551453328525779)
        ·
          refine ⟨33902105831327179992788669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22601403887551453328525779 33902105831327179992788669)
          ·
            refine ⟨12713289686747692497295751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33902105831327179992788669 12713289686747692497295751)
            ·
              refine ⟨19069934530121538745943627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12713289686747692497295751 19069934530121538745943627)
              ·
                refine ⟨28604901795182308118915441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19069934530121538745943627 28604901795182308118915441)
                ·
                  refine ⟨21453676346386731089186581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28604901795182308118915441 21453676346386731089186581)
                  ·
                    refine ⟨1005641078736878019805621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21453676346386731089186581 1005641078736878019805621)
                    ·
                      rfl

theorem cell23_5875437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_5875437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875437 prefixEnd_5875437 := by exact prefixLift 5875437
  have htrace : WordTrace (prefixWord ++ tailWord_5875437) baseStart_5875437 baseEnd_5875437 := by
    simpa [prefixWord, tailWord_5875437, baseEnd_5875437] using wordTrace_append hprefix tailTrace_5875437
  have hstable : (prefixWord ++ tailWord_5875437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875437).length < 2 ^ (prefixWord ++ tailWord_5875437).sum := by decide
  have hdescent : baseEnd_5875437 < baseStart_5875437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875467 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 5]
def baseStart_5875467 : Nat := 118140960795 + 5875467 * 2 ^ 59
def prefixEnd_5875467 : Nat := 4983230072969 + 3 ^ 40 * 5875467 * 2
def baseEnd_5875467 : Nat := 335215404514474326893525

theorem tailTrace_5875467 : CollatzResearch.WordTrace tailWord_5875467 prefixEnd_5875467 335215404514474326893525 := by
  unfold tailWord_5875467
  simp only [CollatzResearch.WordTrace]
  refine ⟨214295886605193983719984655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142863924403462655813323103 214295886605193983719984655)
  ·
    refine ⟨321443829907790975579976983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214295886605193983719984655 321443829907790975579976983)
    ·
      refine ⟨482165744861686463369965475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321443829907790975579976983 482165744861686463369965475)
      ·
        refine ⟨723248617292529695054948213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482165744861686463369965475 723248617292529695054948213)
        ·
          refine ⟨67804557871174658911401395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 723248617292529695054948213 67804557871174658911401395)
          ·
            refine ⟨101706836806761988367102093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67804557871174658911401395 101706836806761988367102093)
            ·
              refine ⟨38140063802535745637663285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101706836806761988367102093 38140063802535745637663285)
              ·
                refine ⟨3575630981487726153530933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38140063802535745637663285 3575630981487726153530933)
                ·
                  refine ⟨335215404514474326893525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3575630981487726153530933 335215404514474326893525)
                  ·
                    rfl

theorem cell23_5875467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 5].length) (baseStart_5875467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875467 prefixEnd_5875467 := by exact prefixLift 5875467
  have htrace : WordTrace (prefixWord ++ tailWord_5875467) baseStart_5875467 baseEnd_5875467 := by
    simpa [prefixWord, tailWord_5875467, baseEnd_5875467] using wordTrace_append hprefix tailTrace_5875467
  have hstable : (prefixWord ++ tailWord_5875467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875467).length < 2 ^ (prefixWord ++ tailWord_5875467).sum := by decide
  have hdescent : baseEnd_5875467 < baseStart_5875467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875474 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5875474 : Nat := 118140960795 + 5875474 * 2 ^ 59
def prefixEnd_5875474 : Nat := 4983230072969 + 3 ^ 40 * 5875474 * 2
def baseEnd_5875474 : Nat := 3016942234994850414654193

theorem tailTrace_5875474 : CollatzResearch.WordTrace tailWord_5875474 prefixEnd_5875474 3016942234994850414654193 := by
  unfold tailWord_5875474
  simp only [CollatzResearch.WordTrace]
  refine ⟨53574035479042155978872369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142864094610779082610326317 53574035479042155978872369)
  ·
    refine ⟨40180526609281616984154277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53574035479042155978872369 40180526609281616984154277)
    ·
      refine ⟨7533848739240303184528927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40180526609281616984154277 7533848739240303184528927)
      ·
        refine ⟨11300773108860454776793391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7533848739240303184528927 11300773108860454776793391)
        ·
          refine ⟨16951159663290682165190087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11300773108860454776793391 16951159663290682165190087)
          ·
            refine ⟨25426739494936023247785131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16951159663290682165190087 25426739494936023247785131)
            ·
              refine ⟨38140109242404034871677697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25426739494936023247785131 38140109242404034871677697)
              ·
                refine ⟨28605081931803026153758273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38140109242404034871677697 28605081931803026153758273)
                ·
                  refine ⟨21453811448852269615318705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28605081931803026153758273 21453811448852269615318705)
                  ·
                    refine ⟨16090358586639202211489029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21453811448852269615318705 16090358586639202211489029)
                    ·
                      refine ⟨3016942234994850414654193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16090358586639202211489029 3016942234994850414654193)
                      ·
                        rfl

theorem cell23_5875474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5875474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875474 prefixEnd_5875474 := by exact prefixLift 5875474
  have htrace : WordTrace (prefixWord ++ tailWord_5875474) baseStart_5875474 baseEnd_5875474 := by
    simpa [prefixWord, tailWord_5875474, baseEnd_5875474] using wordTrace_append hprefix tailTrace_5875474
  have hstable : (prefixWord ++ tailWord_5875474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875474).length < 2 ^ (prefixWord ++ tailWord_5875474).sum := by decide
  have hdescent : baseEnd_5875474 < baseStart_5875474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875477 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_5875477 : Nat := 118140960795 + 5875477 * 2 ^ 59
def prefixEnd_5875477 : Nat := 4983230072969 + 3 ^ 40 * 5875477 * 2
def baseEnd_5875477 : Nat := 3016943775436813902916679

theorem tailTrace_5875477 : CollatzResearch.WordTrace tailWord_5875477 prefixEnd_5875477 3016943775436813902916679 := by
  unfold tailWord_5875477
  simp only [CollatzResearch.WordTrace]
  refine ⟨214296251335157755427848685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142864167556771836951899123 214296251335157755427848685)
  ·
    refine ⟨80361094250684158285443257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214296251335157755427848685 80361094250684158285443257)
    ·
      refine ⟨60270820688013118714082443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80361094250684158285443257 60270820688013118714082443)
      ·
        refine ⟨90406231032019678071123665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60270820688013118714082443 90406231032019678071123665)
        ·
          refine ⟨67804673274014758553342749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90406231032019678071123665 67804673274014758553342749)
          ·
            refine ⟨25426752477755534457503531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67804673274014758553342749 25426752477755534457503531)
            ·
              refine ⟨38140128716633301686255297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25426752477755534457503531 38140128716633301686255297)
              ·
                refine ⟨28605096537474976264691473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38140128716633301686255297 28605096537474976264691473)
                ·
                  refine ⟨21453822403106232198518605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28605096537474976264691473 21453822403106232198518605)
                  ·
                    refine ⟨8045183401164837074444477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21453822403106232198518605 8045183401164837074444477)
                    ·
                      refine ⟨3016943775436813902916679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045183401164837074444477 3016943775436813902916679)
                      ·
                        rfl

theorem cell23_5875477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_5875477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875477 prefixEnd_5875477 := by exact prefixLift 5875477
  have htrace : WordTrace (prefixWord ++ tailWord_5875477) baseStart_5875477 baseEnd_5875477 := by
    simpa [prefixWord, tailWord_5875477, baseEnd_5875477] using wordTrace_append hprefix tailTrace_5875477
  have hstable : (prefixWord ++ tailWord_5875477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875477).length < 2 ^ (prefixWord ++ tailWord_5875477).sum := by decide
  have hdescent : baseEnd_5875477 < baseStart_5875477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875520 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_5875520 : Nat := 118140960795 + 5875520 * 2 ^ 59
def prefixEnd_5875520 : Nat := 4983230072969 + 3 ^ 40 * 5875520 * 2
def baseEnd_5875520 : Nat := 3016965855104957234678981

theorem tailTrace_5875520 : CollatzResearch.WordTrace tailWord_5875520 prefixEnd_5875520 3016965855104957234678981 := by
  unfold tailWord_5875520
  simp only [CollatzResearch.WordTrace]
  refine ⟨107148909837000986885832007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142865213116001315847776009 107148909837000986885832007)
  ·
    refine ⟨160723364755501480328748011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107148909837000986885832007 160723364755501480328748011)
    ·
      refine ⟨241085047133252220493122017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160723364755501480328748011 241085047133252220493122017)
      ·
        refine ⟨180813785349939165369841513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241085047133252220493122017 180813785349939165369841513)
        ·
          refine ⟨135610339012454374027381135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180813785349939165369841513 135610339012454374027381135)
          ·
            refine ⟨203415508518681561041071703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135610339012454374027381135 203415508518681561041071703)
            ·
              refine ⟨305123262778022341561607555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203415508518681561041071703 305123262778022341561607555)
              ·
                refine ⟨457684894167033512342411333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305123262778022341561607555 457684894167033512342411333)
                ·
                  refine ⟨85815917656318783564202125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457684894167033512342411333 85815917656318783564202125)
                  ·
                    refine ⟨32180969121119543836575797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85815917656318783564202125 32180969121119543836575797)
                    ·
                      refine ⟨3016965855104957234678981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32180969121119543836575797 3016965855104957234678981)
                      ·
                        rfl

theorem cell23_5875520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_5875520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875520 prefixEnd_5875520 := by exact prefixLift 5875520
  have htrace : WordTrace (prefixWord ++ tailWord_5875520) baseStart_5875520 baseEnd_5875520 := by
    simpa [prefixWord, tailWord_5875520, baseEnd_5875520] using wordTrace_append hprefix tailTrace_5875520
  have hstable : (prefixWord ++ tailWord_5875520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875520).length < 2 ^ (prefixWord ++ tailWord_5875520).sum := by decide
  have hdescent : baseEnd_5875520 < baseStart_5875520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875527 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 5, 4]
def baseStart_5875527 : Nat := 118140960795 + 5875527 * 2 ^ 59
def prefixEnd_5875527 : Nat := 4983230072969 + 3 ^ 40 * 5875527 * 2
def baseEnd_5875527 : Nat := 1005656483156512902430483

theorem tailTrace_5875527 : CollatzResearch.WordTrace tailWord_5875527 prefixEnd_5875527 1005656483156512902430483 := by
  unfold tailWord_5875527
  simp only [CollatzResearch.WordTrace]
  refine ⟨214298074984976613967168835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142865383323317742644779223 214298074984976613967168835)
  ·
    refine ⟨321447112477464920950753253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214298074984976613967168835 321447112477464920950753253)
    ·
      refine ⟨60271333589524672678266235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321447112477464920950753253 60271333589524672678266235)
      ·
        refine ⟨90407000384287009017399353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60271333589524672678266235 90407000384287009017399353)
        ·
          refine ⟨67805250288215256763049515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90407000384287009017399353 67805250288215256763049515)
          ·
            refine ⟨101707875432322885144574273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67805250288215256763049515 101707875432322885144574273)
            ·
              refine ⟨76280906574242163858430705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101707875432322885144574273 76280906574242163858430705)
              ·
                refine ⟨57210679930681622893823029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76280906574242163858430705 57210679930681622893823029)
                ·
                  refine ⟨5363501243501402146295909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57210679930681622893823029 5363501243501402146295909)
                  ·
                    refine ⟨1005656483156512902430483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363501243501402146295909 1005656483156512902430483)
                    ·
                      rfl

theorem cell23_5875527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_5875527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875527 prefixEnd_5875527 := by exact prefixLift 5875527
  have htrace : WordTrace (prefixWord ++ tailWord_5875527) baseStart_5875527 baseEnd_5875527 := by
    simpa [prefixWord, tailWord_5875527, baseEnd_5875527] using wordTrace_append hprefix tailTrace_5875527
  have hstable : (prefixWord ++ tailWord_5875527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875527).length < 2 ^ (prefixWord ++ tailWord_5875527).sum := by decide
  have hdescent : baseEnd_5875527 < baseStart_5875527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875604 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5875604 : Nat := 118140960795 + 5875604 * 2 ^ 59
def prefixEnd_5875604 : Nat := 4983230072969 + 3 ^ 40 * 5875604 * 2
def baseEnd_5875604 : Nat := 1005669662493311635342865

theorem tailTrace_5875604 : CollatzResearch.WordTrace tailWord_5875604 prefixEnd_5875604 1005669662493311635342865 := by
  unfold tailWord_5875604
  simp only [CollatzResearch.WordTrace]
  refine ⟨107150441702848828058860933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142867255603798437411814577 107150441702848828058860933)
  ·
    refine ⟨20090707819284155261036425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107150441702848828058860933 20090707819284155261036425)
    ·
      refine ⟨15068030864463116445777319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20090707819284155261036425 15068030864463116445777319)
      ·
        refine ⟨22602046296694674668665979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068030864463116445777319 22602046296694674668665979)
        ·
          refine ⟨33903069445042012002998969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22602046296694674668665979 33903069445042012002998969)
          ·
            refine ⟨25427302083781509002249227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33903069445042012002998969 25427302083781509002249227)
            ·
              refine ⟨38140953125672263503373841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25427302083781509002249227 38140953125672263503373841)
              ·
                refine ⟨28605714844254197627530381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38140953125672263503373841 28605714844254197627530381)
                ·
                  refine ⟨10727143066595324110323893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28605714844254197627530381 10727143066595324110323893)
                  ·
                    refine ⟨1005669662493311635342865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10727143066595324110323893 1005669662493311635342865)
                    ·
                      rfl

theorem cell23_5875604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5875604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875604 prefixEnd_5875604 := by exact prefixLift 5875604
  have htrace : WordTrace (prefixWord ++ tailWord_5875604) baseStart_5875604 baseEnd_5875604 := by
    simpa [prefixWord, tailWord_5875604, baseEnd_5875604] using wordTrace_append hprefix tailTrace_5875604
  have hstable : (prefixWord ++ tailWord_5875604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875604).length < 2 ^ (prefixWord ++ tailWord_5875604).sum := by decide
  have hdescent : baseEnd_5875604 < baseStart_5875604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875618 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5875618 : Nat := 118140960795 + 5875618 * 2 ^ 59
def prefixEnd_5875618 : Nat := 4983230072969 + 3 ^ 40 * 5875618 * 2
def baseEnd_5875618 : Nat := 3017016176209097851253531

theorem tailTrace_5875618 : CollatzResearch.WordTrace tailWord_5875618 prefixEnd_5875618 3017016176209097851253531 := by
  unfold tailWord_5875618
  simp only [CollatzResearch.WordTrace]
  refine ⟨53575348506911734127182877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142867596018431291005821005 53575348506911734127182877)
  ·
    refine ⟨20090755690091900297693579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53575348506911734127182877 20090755690091900297693579)
    ·
      refine ⟨30136133535137850446540369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20090755690091900297693579 30136133535137850446540369)
      ·
        refine ⟨22602100151353387834905277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30136133535137850446540369 22602100151353387834905277)
        ·
          refine ⟨8475787556757520438089479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22602100151353387834905277 8475787556757520438089479)
          ·
            refine ⟨12713681335136280657134219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8475787556757520438089479 12713681335136280657134219)
            ·
              refine ⟨19070522002704420985701329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12713681335136280657134219 19070522002704420985701329)
              ·
                refine ⟨14302891502028315739275997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19070522002704420985701329 14302891502028315739275997)
                ·
                  refine ⟨5363584313260618402228499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14302891502028315739275997 5363584313260618402228499)
                  ·
                    refine ⟨8045376469890927603342749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5363584313260618402228499 8045376469890927603342749)
                    ·
                      refine ⟨3017016176209097851253531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045376469890927603342749 3017016176209097851253531)
                      ·
                        rfl

theorem cell23_5875618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5875618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875618 prefixEnd_5875618 := by exact prefixLift 5875618
  have htrace : WordTrace (prefixWord ++ tailWord_5875618) baseStart_5875618 baseEnd_5875618 := by
    simpa [prefixWord, tailWord_5875618, baseEnd_5875618] using wordTrace_append hprefix tailTrace_5875618
  have hstable : (prefixWord ++ tailWord_5875618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875618).length < 2 ^ (prefixWord ++ tailWord_5875618).sum := by decide
  have hdescent : baseEnd_5875618 < baseStart_5875618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875641 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 5, 2, 2]
def baseStart_5875641 : Nat := 118140960795 + 5875641 * 2 ^ 59
def prefixEnd_5875641 : Nat := 4983230072969 + 3 ^ 40 * 5875641 * 2
def baseEnd_5875641 : Nat := 3017027986264151261265925

theorem tailTrace_5875641 : CollatzResearch.WordTrace tailWord_5875641 prefixEnd_5875641 3017027986264151261265925 := by
  unfold tailWord_5875641
  simp only [CollatzResearch.WordTrace]
  refine ⟨214302232906563611436818777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142868155271042407624545851 214302232906563611436818777)
  ·
    refine ⟨160726674679922708577614083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214302232906563611436818777 160726674679922708577614083)
    ·
      refine ⟨241090012019884062866421125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160726674679922708577614083 241090012019884062866421125)
      ·
        refine ⟨45204377253728261787453961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241090012019884062866421125 45204377253728261787453961)
        ·
          refine ⟨33903282940296196340590471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45204377253728261787453961 33903282940296196340590471)
          ·
            refine ⟨50854924410444294510885707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33903282940296196340590471 50854924410444294510885707)
            ·
              refine ⟨76282386615666441766328561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50854924410444294510885707 76282386615666441766328561)
              ·
                refine ⟨57211789961749831324746421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76282386615666441766328561 57211789961749831324746421)
                ·
                  refine ⟨5363605308914046686694977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57211789961749831324746421 5363605308914046686694977)
                  ·
                    refine ⟨4022703981685535015021233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363605308914046686694977 4022703981685535015021233)
                    ·
                      refine ⟨3017027986264151261265925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022703981685535015021233 3017027986264151261265925)
                      ·
                        rfl

theorem cell23_5875641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_5875641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875641 prefixEnd_5875641 := by exact prefixLift 5875641
  have htrace : WordTrace (prefixWord ++ tailWord_5875641) baseStart_5875641 baseEnd_5875641 := by
    simpa [prefixWord, tailWord_5875641, baseEnd_5875641] using wordTrace_append hprefix tailTrace_5875641
  have hstable : (prefixWord ++ tailWord_5875641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875641).length < 2 ^ (prefixWord ++ tailWord_5875641).sum := by decide
  have hdescent : baseEnd_5875641 < baseStart_5875641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875668 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5875668 : Nat := 118140960795 + 5875668 * 2 ^ 59
def prefixEnd_5875668 : Nat := 4983230072969 + 3 ^ 40 * 5875668 * 2
def baseEnd_5875668 : Nat := 1005680616747274218542767

theorem tailTrace_5875668 : CollatzResearch.WordTrace tailWord_5875668 prefixEnd_5875668 1005680616747274218542767 := by
  unfold tailWord_5875668
  simp only [CollatzResearch.WordTrace]
  refine ⟨107151608838732897524025829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142868811784977196698701105 107151608838732897524025829)
  ·
    refine ⟨20090926657262418285754843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107151608838732897524025829 20090926657262418285754843)
    ·
      refine ⟨30136389985893627428632265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20090926657262418285754843 30136389985893627428632265)
      ·
        refine ⟨22602292489420220571474199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30136389985893627428632265 22602292489420220571474199)
        ·
          refine ⟨33903438734130330857211299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22602292489420220571474199 33903438734130330857211299)
          ·
            refine ⟨50855158101195496285816949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33903438734130330857211299 50855158101195496285816949)
            ·
              refine ⟨4767671071987077776795339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50855158101195496285816949 4767671071987077776795339)
              ·
                refine ⟨7151506607980616665193009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767671071987077776795339 7151506607980616665193009)
                ·
                  refine ⟨5363629955985462498894757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7151506607980616665193009 5363629955985462498894757)
                  ·
                    refine ⟨1005680616747274218542767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363629955985462498894757 1005680616747274218542767)
                    ·
                      rfl

theorem cell23_5875668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5875668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875668 prefixEnd_5875668 := by exact prefixLift 5875668
  have htrace : WordTrace (prefixWord ++ tailWord_5875668) baseStart_5875668 baseEnd_5875668 := by
    simpa [prefixWord, tailWord_5875668, baseEnd_5875668] using wordTrace_append hprefix tailTrace_5875668
  have hstable : (prefixWord ++ tailWord_5875668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875668).length < 2 ^ (prefixWord ++ tailWord_5875668).sum := by decide
  have hdescent : baseEnd_5875668 < baseStart_5875668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875707 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 4, 6]
def baseStart_5875707 : Nat := 118140960795 + 5875707 * 2 ^ 59
def prefixEnd_5875707 : Nat := 4983230072969 + 3 ^ 40 * 5875707 * 2
def baseEnd_5875707 : Nat := 1005687291995782667680207

theorem tailTrace_5875707 : CollatzResearch.WordTrace tailWord_5875707 prefixEnd_5875707 1005687291995782667680207 := by
  unfold tailWord_5875707
  simp only [CollatzResearch.WordTrace]
  refine ⟨214304640124324504708721375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142869760082883003139147583 214304640124324504708721375)
  ·
    refine ⟨321456960186486757063082063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214304640124324504708721375 321456960186486757063082063)
    ·
      refine ⟨482185440279730135594623095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321456960186486757063082063 482185440279730135594623095)
      ·
        refine ⟨723278160419595203391934643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482185440279730135594623095 723278160419595203391934643)
        ·
          refine ⟨1084917240629392805087901965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723278160419595203391934643 1084917240629392805087901965)
          ·
            refine ⟨406843965236022301907963237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084917240629392805087901965 406843965236022301907963237)
            ·
              refine ⟨76283243481754181607743107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406843965236022301907963237 76283243481754181607743107)
              ·
                refine ⟨114424865222631272411614661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76283243481754181607743107 114424865222631272411614661)
                ·
                  refine ⟨21454662229243363577177749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114424865222631272411614661 21454662229243363577177749)
                  ·
                    refine ⟨1005687291995782667680207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21454662229243363577177749 1005687291995782667680207)
                    ·
                      rfl

theorem cell23_5875707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_5875707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875707 prefixEnd_5875707 := by exact prefixLift 5875707
  have htrace : WordTrace (prefixWord ++ tailWord_5875707) baseStart_5875707 baseEnd_5875707 := by
    simpa [prefixWord, tailWord_5875707, baseEnd_5875707] using wordTrace_append hprefix tailTrace_5875707
  have hstable : (prefixWord ++ tailWord_5875707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875707).length < 2 ^ (prefixWord ++ tailWord_5875707).sum := by decide
  have hdescent : baseEnd_5875707 < baseStart_5875707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875737 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 9]
def baseStart_5875737 : Nat := 118140960795 + 5875737 * 2 ^ 59
def prefixEnd_5875737 : Nat := 4983230072969 + 3 ^ 40 * 5875737 * 2
def baseEnd_5875737 : Nat := 335230808934109209518387

theorem tailTrace_5875737 : CollatzResearch.WordTrace tailWord_5875737 prefixEnd_5875737 335230808934109209518387 := by
  unfold tailWord_5875737
  simp only [CollatzResearch.WordTrace]
  refine ⟨214305734314215819832313465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142870489542810546554875643 214305734314215819832313465)
  ·
    refine ⟨160729300735661864874235099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214305734314215819832313465 160729300735661864874235099)
    ·
      refine ⟨241093951103492797311352649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160729300735661864874235099 241093951103492797311352649)
      ·
        refine ⟨180820463327619597983514487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241093951103492797311352649 180820463327619597983514487)
        ·
          refine ⟨271230694991429396975271731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180820463327619597983514487 271230694991429396975271731)
          ·
            refine ⟨406846042487144095462907597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271230694991429396975271731 406846042487144095462907597)
            ·
              refine ⟨152567265932679035798590349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406846042487144095462907597 152567265932679035798590349)
              ·
                refine ⟨57212724724754638424471381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152567265932679035798590349 57212724724754638424471381)
                ·
                  refine ⟨335230808934109209518387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57212724724754638424471381 335230808934109209518387)
                  ·
                    rfl

theorem cell23_5875737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_5875737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875737 prefixEnd_5875737 := by exact prefixLift 5875737
  have htrace : WordTrace (prefixWord ++ tailWord_5875737) baseStart_5875737 baseEnd_5875737 := by
    simpa [prefixWord, tailWord_5875737, baseEnd_5875737] using wordTrace_append hprefix tailTrace_5875737
  have hstable : (prefixWord ++ tailWord_5875737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875737).length < 2 ^ (prefixWord ++ tailWord_5875737).sum := by decide
  have hdescent : baseEnd_5875737 < baseStart_5875737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875782 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5875782 : Nat := 118140960795 + 5875782 * 2 ^ 59
def prefixEnd_5875782 : Nat := 4983230072969 + 3 ^ 40 * 5875782 * 2
def baseEnd_5875782 : Nat := 3017100387036435209602777

theorem tailTrace_5875782 : CollatzResearch.WordTrace tailWord_5875782 prefixEnd_5875782 3017100387036435209602777 := by
  unfold tailWord_5875782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697105487470399766178175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142871583732701861678467733 6697105487470399766178175)
  ·
    refine ⟨10045658231205599649267263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6697105487470399766178175 10045658231205599649267263)
    ·
      refine ⟨15068487346808399473900895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10045658231205599649267263 15068487346808399473900895)
      ·
        refine ⟨22602731020212599210851343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068487346808399473900895 22602731020212599210851343)
        ·
          refine ⟨33904096530318898816277015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22602731020212599210851343 33904096530318898816277015)
          ·
            refine ⟨50856144795478348224415523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33904096530318898816277015 50856144795478348224415523)
            ·
              refine ⟨76284217193217522336623285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50856144795478348224415523 76284217193217522336623285)
              ·
                refine ⟨7151645361864142719058433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76284217193217522336623285 7151645361864142719058433)
                ·
                  refine ⟨5363734021398107039293825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7151645361864142719058433 5363734021398107039293825)
                  ·
                    refine ⟨4022800516048580279470369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363734021398107039293825 4022800516048580279470369)
                    ·
                      refine ⟨3017100387036435209602777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022800516048580279470369 3017100387036435209602777)
                      ·
                        rfl

theorem cell23_5875782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5875782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875782 prefixEnd_5875782 := by exact prefixLift 5875782
  have htrace : WordTrace (prefixWord ++ tailWord_5875782) baseStart_5875782 baseEnd_5875782 := by
    simpa [prefixWord, tailWord_5875782, baseEnd_5875782] using wordTrace_append hprefix tailTrace_5875782
  have hstable : (prefixWord ++ tailWord_5875782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875782).length < 2 ^ (prefixWord ++ tailWord_5875782).sum := by decide
  have hdescent : baseEnd_5875782 < baseStart_5875782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875805 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 5]
def baseStart_5875805 : Nat := 118140960795 + 5875805 * 2 ^ 59
def prefixEnd_5875805 : Nat := 4983230072969 + 3 ^ 40 * 5875805 * 2
def baseEnd_5875805 : Nat := 335234688565720957735019

theorem tailTrace_5875805 : CollatzResearch.WordTrace tailWord_5875805 prefixEnd_5875805 335234688565720957735019 := by
  unfold tailWord_5875805
  simp only [CollatzResearch.WordTrace]
  refine ⟨214308214477969467445788869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142872142985312978297192579 214308214477969467445788869)
  ·
    refine ⟨40182790214619275146085413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214308214477969467445788869 40182790214619275146085413)
    ·
      refine ⟨7534273165241114089891015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40182790214619275146085413 7534273165241114089891015)
      ·
        refine ⟨11301409747861671134836523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534273165241114089891015 11301409747861671134836523)
        ·
          refine ⟨16952114621792506702254785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11301409747861671134836523 16952114621792506702254785)
          ·
            refine ⟨12714085966344380026691089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16952114621792506702254785 12714085966344380026691089)
            ·
              refine ⟨9535564474758285020018317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12714085966344380026691089 9535564474758285020018317)
              ·
                refine ⟨3575836678034356882506869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9535564474758285020018317 3575836678034356882506869)
                ·
                  refine ⟨335234688565720957735019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3575836678034356882506869 335234688565720957735019)
                  ·
                    rfl

theorem cell23_5875805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_5875805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875805 prefixEnd_5875805 := by exact prefixLift 5875805
  have htrace : WordTrace (prefixWord ++ tailWord_5875805) baseStart_5875805 baseEnd_5875805 := by
    simpa [prefixWord, tailWord_5875805, baseEnd_5875805] using wordTrace_append hprefix tailTrace_5875805
  have hstable : (prefixWord ++ tailWord_5875805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875805).length < 2 ^ (prefixWord ++ tailWord_5875805).sum := by decide
  have hdescent : baseEnd_5875805 < baseStart_5875805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875821 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5875821 : Nat := 118140960795 + 5875821 * 2 ^ 59
def prefixEnd_5875821 : Nat := 4983230072969 + 3 ^ 40 * 5875821 * 2
def baseEnd_5875821 : Nat := 3017120412781960557015097

theorem tailTrace_5875821 : CollatzResearch.WordTrace tailWord_5875821 prefixEnd_5875821 3017120412781960557015097 := by
  unfold tailWord_5875821
  simp only [CollatzResearch.WordTrace]
  refine ⟨214308798045911502178371317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142872532030607668118914211 214308798045911502178371317)
  ·
    refine ⟨20091449816804203329222311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214308798045911502178371317 20091449816804203329222311)
    ·
      refine ⟨30137174725206304993833467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20091449816804203329222311 30137174725206304993833467)
      ·
        refine ⟨45205762087809457490750201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30137174725206304993833467 45205762087809457490750201)
        ·
          refine ⟨33904321565857093118062651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45205762087809457490750201 33904321565857093118062651)
          ·
            refine ⟨50856482348785639677093977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33904321565857093118062651 50856482348785639677093977)
            ·
              refine ⟨38142361761589229757820483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50856482348785639677093977 38142361761589229757820483)
              ·
                refine ⟨57213542642383844636730725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38142361761589229757820483 57213542642383844636730725)
                ·
                  refine ⟨10727539245446970869387011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57213542642383844636730725 10727539245446970869387011)
                  ·
                    refine ⟨16091308868170456304080517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10727539245446970869387011 16091308868170456304080517)
                    ·
                      refine ⟨3017120412781960557015097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16091308868170456304080517 3017120412781960557015097)
                      ·
                        rfl

theorem cell23_5875821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5875821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875821 prefixEnd_5875821 := by exact prefixLift 5875821
  have htrace : WordTrace (prefixWord ++ tailWord_5875821) baseStart_5875821 baseEnd_5875821 := by
    simpa [prefixWord, tailWord_5875821, baseEnd_5875821] using wordTrace_append hprefix tailTrace_5875821
  have hstable : (prefixWord ++ tailWord_5875821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875821).length < 2 ^ (prefixWord ++ tailWord_5875821).sum := by decide
  have hdescent : baseEnd_5875821 < baseStart_5875821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875831 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 3, 4]
def baseStart_5875831 : Nat := 118140960795 + 5875831 * 2 ^ 59
def prefixEnd_5875831 : Nat := 4983230072969 + 3 ^ 40 * 5875831 * 2
def baseEnd_5875831 : Nat := 1005708515862835172630017

theorem tailTrace_5875831 : CollatzResearch.WordTrace tailWord_5875831 prefixEnd_5875831 1005708515862835172630017 := by
  unfold tailWord_5875831
  simp only [CollatzResearch.WordTrace]
  refine ⟨214309162775875273886235347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142872775183916849257490231 214309162775875273886235347)
  ·
    refine ⟨321463744163812910829353021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214309162775875273886235347 321463744163812910829353021)
    ·
      refine ⟨120548904061429841561007383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321463744163812910829353021 120548904061429841561007383)
      ·
        refine ⟨180823356092144762341511075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120548904061429841561007383 180823356092144762341511075)
        ·
          refine ⟨271235034138217143512266613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180823356092144762341511075 271235034138217143512266613)
          ·
            refine ⟨25428284450457857204274995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271235034138217143512266613 25428284450457857204274995)
            ·
              refine ⟨38142426675686785806412493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25428284450457857204274995 38142426675686785806412493)
              ·
                refine ⟨14303410003382544677404685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38142426675686785806412493 14303410003382544677404685)
                ·
                  refine ⟨5363778751268454254026757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14303410003382544677404685 5363778751268454254026757)
                  ·
                    refine ⟨1005708515862835172630017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363778751268454254026757 1005708515862835172630017)
                    ·
                      rfl

theorem cell23_5875831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_5875831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875831 prefixEnd_5875831 := by exact prefixLift 5875831
  have htrace : WordTrace (prefixWord ++ tailWord_5875831) baseStart_5875831 baseEnd_5875831 := by
    simpa [prefixWord, tailWord_5875831, baseEnd_5875831] using wordTrace_append hprefix tailTrace_5875831
  have hstable : (prefixWord ++ tailWord_5875831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875831).length < 2 ^ (prefixWord ++ tailWord_5875831).sum := by decide
  have hdescent : baseEnd_5875831 < baseStart_5875831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875848 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 3, 4]
def baseStart_5875848 : Nat := 118140960795 + 5875848 * 2 ^ 59
def prefixEnd_5875848 : Nat := 4983230072969 + 3 ^ 40 * 5875848 * 2
def baseEnd_5875848 : Nat := 1005711425586543983792491

theorem tailTrace_5875848 : CollatzResearch.WordTrace tailWord_5875848 prefixEnd_5875848 1005711425586543983792491 := by
  unfold tailWord_5875848
  simp only [CollatzResearch.WordTrace]
  refine ⟨107154891408406842894802099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142873188544542457193069465 107154891408406842894802099)
  ·
    refine ⟨160732337112610264342203149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107154891408406842894802099 160732337112610264342203149)
    ·
      refine ⟨60274626417228849128326181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160732337112610264342203149 60274626417228849128326181)
      ·
        refine ⟨11301492453230409211561159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60274626417228849128326181 11301492453230409211561159)
        ·
          refine ⟨16952238679845613817341739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11301492453230409211561159 16952238679845613817341739)
          ·
            refine ⟨25428358019768420726012609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16952238679845613817341739 25428358019768420726012609)
            ·
              refine ⟨19071268514826315544509457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25428358019768420726012609 19071268514826315544509457)
              ·
                refine ⟨14303451386119736658382093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19071268514826315544509457 14303451386119736658382093)
                ·
                  refine ⟨5363794269794901246893285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14303451386119736658382093 5363794269794901246893285)
                  ·
                    refine ⟨1005711425586543983792491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363794269794901246893285 1005711425586543983792491)
                    ·
                      rfl

theorem cell23_5875848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_5875848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875848 prefixEnd_5875848 := by exact prefixLift 5875848
  have htrace : WordTrace (prefixWord ++ tailWord_5875848) baseStart_5875848 baseEnd_5875848 := by
    simpa [prefixWord, tailWord_5875848, baseEnd_5875848] using wordTrace_append hprefix tailTrace_5875848
  have hstable : (prefixWord ++ tailWord_5875848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875848).length < 2 ^ (prefixWord ++ tailWord_5875848).sum := by decide
  have hdescent : baseEnd_5875848 < baseStart_5875848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875858 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5875858 : Nat := 118140960795 + 5875858 * 2 ^ 59
def prefixEnd_5875858 : Nat := 4983230072969 + 3 ^ 40 * 5875858 * 2
def baseEnd_5875858 : Nat := 3017139411566176912252427

theorem tailTrace_5875858 : CollatzResearch.WordTrace tailWord_5875858 prefixEnd_5875858 3017139411566176912252427 := by
  unfold tailWord_5875858
  simp only [CollatzResearch.WordTrace]
  refine ⟨53577536886694364374367057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142873431697851638331645485 53577536886694364374367057)
  ·
    refine ⟨40183152665020773280775293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53577536886694364374367057 40183152665020773280775293)
    ·
      refine ⟨15068682249382789980290735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40183152665020773280775293 15068682249382789980290735)
      ·
        refine ⟨22603023374074184970436103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068682249382789980290735 22603023374074184970436103)
        ·
          refine ⟨33904535061111277455654155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22603023374074184970436103 33904535061111277455654155)
          ·
            refine ⟨50856802591666916183481233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33904535061111277455654155 50856802591666916183481233)
            ·
              refine ⟨38142601943750187137610925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50856802591666916183481233 38142601943750187137610925)
              ·
                refine ⟨14303475728906320176604097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38142601943750187137610925 14303475728906320176604097)
                ·
                  refine ⟨10727606796679740132453073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14303475728906320176604097 10727606796679740132453073)
                  ·
                    refine ⟨8045705097509805099339805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10727606796679740132453073 8045705097509805099339805)
                    ·
                      refine ⟨3017139411566176912252427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045705097509805099339805 3017139411566176912252427)
                      ·
                        rfl

theorem cell23_5875858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5875858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875858 prefixEnd_5875858 := by exact prefixLift 5875858
  have htrace : WordTrace (prefixWord ++ tailWord_5875858) baseStart_5875858 baseEnd_5875858 := by
    simpa [prefixWord, tailWord_5875858, baseEnd_5875858] using wordTrace_append hprefix tailTrace_5875858
  have hstable : (prefixWord ++ tailWord_5875858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875858).length < 2 ^ (prefixWord ++ tailWord_5875858).sum := by decide
  have hdescent : baseEnd_5875858 < baseStart_5875858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875882 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5875882 : Nat := 118140960795 + 5875882 * 2 ^ 59
def prefixEnd_5875882 : Nat := 4983230072969 + 3 ^ 40 * 5875882 * 2
def baseEnd_5875882 : Nat := 1005717245033961606117439

theorem tailTrace_5875882 : CollatzResearch.WordTrace tailWord_5875882 prefixEnd_5875882 1005717245033961606117439 := by
  unfold tailWord_5875882
  simp only [CollatzResearch.WordTrace]
  refine ⟨53577755724672627399085475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142874015265793673064227933 53577755724672627399085475)
  ·
    refine ⟨80366633587008941098628213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53577755724672627399085475 80366633587008941098628213)
    ·
      refine ⟨7534371898782088227996395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80366633587008941098628213 7534371898782088227996395)
      ·
        refine ⟨11301557848173132341994593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534371898782088227996395 11301557848173132341994593)
        ·
          refine ⟨8476168386129849256495945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11301557848173132341994593 8476168386129849256495945)
          ·
            refine ⟨6357126289597386942371959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8476168386129849256495945 6357126289597386942371959)
            ·
              refine ⟨9535689434396080413557939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357126289597386942371959 9535689434396080413557939)
              ·
                refine ⟨14303534151594120620336909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9535689434396080413557939 14303534151594120620336909)
                ·
                  refine ⟨5363825306847795232626341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14303534151594120620336909 5363825306847795232626341)
                  ·
                    refine ⟨1005717245033961606117439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363825306847795232626341 1005717245033961606117439)
                    ·
                      rfl

theorem cell23_5875882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5875882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875882 prefixEnd_5875882 := by exact prefixLift 5875882
  have htrace : WordTrace (prefixWord ++ tailWord_5875882) baseStart_5875882 baseEnd_5875882 := by
    simpa [prefixWord, tailWord_5875882, baseEnd_5875882] using wordTrace_append hprefix tailTrace_5875882
  have hstable : (prefixWord ++ tailWord_5875882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875882).length < 2 ^ (prefixWord ++ tailWord_5875882).sum := by decide
  have hdescent : baseEnd_5875882 < baseStart_5875882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875908 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5875908 : Nat := 118140960795 + 5875908 * 2 ^ 59
def prefixEnd_5875908 : Nat := 4983230072969 + 3 ^ 40 * 5875908 * 2
def baseEnd_5875908 : Nat := 1005721695199633905542399

theorem tailTrace_5875908 : CollatzResearch.WordTrace tailWord_5875908 prefixEnd_5875908 1005721695199633905542399 := by
  unfold tailWord_5875908
  simp only [CollatzResearch.WordTrace]
  refine ⟨107155985598298158018394189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142874647464397544024525585 107155985598298158018394189)
  ·
    refine ⟨40183494599361809256897821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107155985598298158018394189 40183494599361809256897821)
    ·
      refine ⟨15068810474760678471336683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40183494599361809256897821 15068810474760678471336683)
      ·
        refine ⟨22603215712141017707005025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068810474760678471336683 22603215712141017707005025)
        ·
          refine ⟨16952411784105763280253769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22603215712141017707005025 16952411784105763280253769)
          ·
            refine ⟨12714308838079322460190327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16952411784105763280253769 12714308838079322460190327)
            ·
              refine ⟨19071463257118983690285491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714308838079322460190327 19071463257118983690285491)
              ·
                refine ⟨28607194885678475535428237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19071463257118983690285491 28607194885678475535428237)
                ·
                  refine ⟨10727698082129428325785589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28607194885678475535428237 10727698082129428325785589)
                  ·
                    refine ⟨1005721695199633905542399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10727698082129428325785589 1005721695199633905542399)
                    ·
                      rfl

theorem cell23_5875908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5875908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875908 prefixEnd_5875908 := by exact prefixLift 5875908
  have htrace : WordTrace (prefixWord ++ tailWord_5875908) baseStart_5875908 baseEnd_5875908 := by
    simpa [prefixWord, tailWord_5875908, baseEnd_5875908] using wordTrace_append hprefix tailTrace_5875908
  have hstable : (prefixWord ++ tailWord_5875908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875908).length < 2 ^ (prefixWord ++ tailWord_5875908).sum := by decide
  have hdescent : baseEnd_5875908 < baseStart_5875908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875921 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 6, 4]
def baseStart_5875921 : Nat := 118140960795 + 5875921 * 2 ^ 59
def prefixEnd_5875921 : Nat := 4983230072969 + 3 ^ 40 * 5875921 * 2
def baseEnd_5875921 : Nat := 1005723920282470055254879

theorem tailTrace_5875921 : CollatzResearch.WordTrace tailWord_5875921 prefixEnd_5875921 1005723920282470055254879 := by
  unfold tailWord_5875921
  simp only [CollatzResearch.WordTrace]
  refine ⟨214312445345549219257011617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142874963563699479504674411 214312445345549219257011617)
  ·
    refine ⟨160734334009161914442758713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214312445345549219257011617 160734334009161914442758713)
    ·
      refine ⟨120550750506871435832069035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160734334009161914442758713 120550750506871435832069035)
      ·
        refine ⟨180826125760307153748103553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120550750506871435832069035 180826125760307153748103553)
        ·
          refine ⟨135619594320230365311077665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180826125760307153748103553 135619594320230365311077665)
          ·
            refine ⟨101714695740172773983308249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135619594320230365311077665 101714695740172773983308249)
            ·
              refine ⟨76286021805129580487481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101714695740172773983308249 76286021805129580487481187)
              ·
                refine ⟨114429032707694370731221781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76286021805129580487481187 114429032707694370731221781)
                ·
                  refine ⟨5363860908173173628026021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114429032707694370731221781 5363860908173173628026021)
                  ·
                    refine ⟨1005723920282470055254879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363860908173173628026021 1005723920282470055254879)
                    ·
                      rfl

theorem cell23_5875921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_5875921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875921 prefixEnd_5875921 := by exact prefixLift 5875921
  have htrace : WordTrace (prefixWord ++ tailWord_5875921) baseStart_5875921 baseEnd_5875921 := by
    simpa [prefixWord, tailWord_5875921, baseEnd_5875921] using wordTrace_append hprefix tailTrace_5875921
  have hstable : (prefixWord ++ tailWord_5875921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875921).length < 2 ^ (prefixWord ++ tailWord_5875921).sum := by decide
  have hdescent : baseEnd_5875921 < baseStart_5875921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875931 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 3]
def baseStart_5875931 : Nat := 118140960795 + 5875931 * 2 ^ 59
def prefixEnd_5875931 : Nat := 4983230072969 + 3 ^ 40 * 5875931 * 2
def baseEnd_5875931 : Nat := 3017176895653955126639591

theorem tailTrace_5875931 : CollatzResearch.WordTrace tailWord_5875931 prefixEnd_5875931 3017176895653955126639591 := by
  unfold tailWord_5875931
  simp only [CollatzResearch.WordTrace]
  refine ⟨214312810075512990964875647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142875206717008660643250431 214312810075512990964875647)
  ·
    refine ⟨321469215113269486447313471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214312810075512990964875647 321469215113269486447313471)
    ·
      refine ⟨482203822669904229670970207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321469215113269486447313471 482203822669904229670970207)
      ·
        refine ⟨723305734004856344506455311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482203822669904229670970207 723305734004856344506455311)
        ·
          refine ⟨1084958601007284516759682967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723305734004856344506455311 1084958601007284516759682967)
          ·
            refine ⟨1627437901510926775139524451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084958601007284516759682967 1627437901510926775139524451)
            ·
              refine ⟨2441156852266390162709286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1627437901510926775139524451 2441156852266390162709286677)
              ·
                refine ⟨114429227449987038876997813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2441156852266390162709286677 114429227449987038876997813)
                ·
                  refine ⟨10727740073436284894718545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114429227449987038876997813 10727740073436284894718545)
                  ·
                    refine ⟨8045805055077213671038909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10727740073436284894718545 8045805055077213671038909)
                    ·
                      refine ⟨3017176895653955126639591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045805055077213671038909 3017176895653955126639591)
                      ·
                        rfl

theorem cell23_5875931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 3].length) (baseStart_5875931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875931 prefixEnd_5875931 := by exact prefixLift 5875931
  have htrace : WordTrace (prefixWord ++ tailWord_5875931) baseStart_5875931 baseEnd_5875931 := by
    simpa [prefixWord, tailWord_5875931, baseEnd_5875931] using wordTrace_append hprefix tailTrace_5875931
  have hstable : (prefixWord ++ tailWord_5875931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875931).length < 2 ^ (prefixWord ++ tailWord_5875931).sum := by decide
  have hdescent : baseEnd_5875931 < baseStart_5875931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875934 : List Nat := [4, 19]
def baseStart_5875934 : Nat := 118140960795 + 5875934 * 2 ^ 59
def prefixEnd_5875934 : Nat := 4983230072969 + 3 ^ 40 * 5875934 * 2
def baseEnd_5875934 : Nat := 153288545246960250719

theorem tailTrace_5875934 : CollatzResearch.WordTrace tailWord_5875934 prefixEnd_5875934 153288545246960250719 := by
  unfold tailWord_5875934
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789114936812765309654357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142875279663001414984823237 26789114936812765309654357)
  ·
    refine ⟨153288545246960250719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 19 26789114936812765309654357 153288545246960250719)
    ·
      rfl

theorem cell23_5875934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 19].length) (baseStart_5875934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875934 prefixEnd_5875934 := by exact prefixLift 5875934
  have htrace : WordTrace (prefixWord ++ tailWord_5875934) baseStart_5875934 baseEnd_5875934 := by
    simpa [prefixWord, tailWord_5875934, baseEnd_5875934] using wordTrace_append hprefix tailTrace_5875934
  have hstable : (prefixWord ++ tailWord_5875934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875934).length < 2 ^ (prefixWord ++ tailWord_5875934).sum := by decide
  have hdescent : baseEnd_5875934 < baseStart_5875934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875939 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5875939 : Nat := 118140960795 + 5875939 * 2 ^ 59
def prefixEnd_5875939 : Nat := 4983230072969 + 3 ^ 40 * 5875939 * 2
def baseEnd_5875939 : Nat := 3017181003499191095339555

theorem tailTrace_5875939 : CollatzResearch.WordTrace tailWord_5875939 prefixEnd_5875939 3017181003499191095339555 := by
  unfold tailWord_5875939
  simp only [CollatzResearch.WordTrace]
  refine ⟨214313101859484008331166871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142875401239656005554111247 214313101859484008331166871)
  ·
    refine ⟨321469652789226012496750307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214313101859484008331166871 321469652789226012496750307)
    ·
      refine ⟨482204479183839018745125461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321469652789226012496750307 482204479183839018745125461)
      ·
        refine ⟨5650833740435613500919439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 482204479183839018745125461 5650833740435613500919439)
        ·
          refine ⟨8476250610653420251379159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5650833740435613500919439 8476250610653420251379159)
          ·
            refine ⟨12714375915980130377068739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8476250610653420251379159 12714375915980130377068739)
            ·
              refine ⟨19071563873970195565603109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714375915980130377068739 19071563873970195565603109)
              ·
                refine ⟨3575918226369411668550583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19071563873970195565603109 3575918226369411668550583)
                ·
                  refine ⟨5363877339554117502825875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575918226369411668550583 5363877339554117502825875)
                  ·
                    refine ⟨8045816009331176254238813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5363877339554117502825875 8045816009331176254238813)
                    ·
                      refine ⟨3017181003499191095339555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045816009331176254238813 3017181003499191095339555)
                      ·
                        rfl

theorem cell23_5875939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5875939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875939 prefixEnd_5875939 := by exact prefixLift 5875939
  have htrace : WordTrace (prefixWord ++ tailWord_5875939) baseStart_5875939 baseEnd_5875939 := by
    simpa [prefixWord, tailWord_5875939, baseEnd_5875939] using wordTrace_append hprefix tailTrace_5875939
  have hstable : (prefixWord ++ tailWord_5875939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875939).length < 2 ^ (prefixWord ++ tailWord_5875939).sum := by decide
  have hdescent : baseEnd_5875939 < baseStart_5875939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875951 : List Nat := [1, 1, 2, 1, 6, 1, 3, 8]
def baseStart_5875951 : Nat := 118140960795 + 5875951 * 2 ^ 59
def prefixEnd_5875951 : Nat := 4983230072969 + 3 ^ 40 * 5875951 * 2
def baseEnd_5875951 : Nat := 111747672787668335125537

theorem tailTrace_5875951 : CollatzResearch.WordTrace tailWord_5875951 prefixEnd_5875951 111747672787668335125537 := by
  unfold tailWord_5875951
  simp only [CollatzResearch.WordTrace]
  refine ⟨214313539535440534380603707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142875693023627022920402471 214313539535440534380603707)
  ·
    refine ⟨321470309303160801570905561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214313539535440534380603707 321470309303160801570905561)
    ·
      refine ⟨241102731977370601178179171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321470309303160801570905561 241102731977370601178179171)
      ·
        refine ⟨361654097966055901767268757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241102731977370601178179171 361654097966055901767268757)
        ·
          refine ⟨16952535842158870395340723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 361654097966055901767268757 16952535842158870395340723)
          ·
            refine ⟨25428803763238305593011085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16952535842158870395340723 25428803763238305593011085)
            ·
              refine ⟨9535801411214364597379157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25428803763238305593011085 9535801411214364597379157)
              ·
                refine ⟨111747672787668335125537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9535801411214364597379157 111747672787668335125537)
                ·
                  rfl

theorem cell23_5875951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 8].length) (baseStart_5875951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875951 prefixEnd_5875951 := by exact prefixLift 5875951
  have htrace : WordTrace (prefixWord ++ tailWord_5875951) baseStart_5875951 baseEnd_5875951 := by
    simpa [prefixWord, tailWord_5875951, baseEnd_5875951] using wordTrace_append hprefix tailTrace_5875951
  have hstable : (prefixWord ++ tailWord_5875951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875951).length < 2 ^ (prefixWord ++ tailWord_5875951).sum := by decide
  have hdescent : baseEnd_5875951 < baseStart_5875951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875958 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5875958 : Nat := 118140960795 + 5875958 * 2 ^ 59
def prefixEnd_5875958 : Nat := 4983230072969 + 3 ^ 40 * 5875958 * 2
def baseEnd_5875958 : Nat := 3017190759631626521001967

theorem tailTrace_5875958 : CollatzResearch.WordTrace tailWord_5875958 prefixEnd_5875958 3017190759631626521001967 := by
  unfold tailWord_5875958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13394612177900948411006783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142875863230943449717405685 13394612177900948411006783)
  ·
    refine ⟨20091918266851422616510175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13394612177900948411006783 20091918266851422616510175)
    ·
      refine ⟨30137877400277133924765263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20091918266851422616510175 30137877400277133924765263)
      ·
        refine ⟨45206816100415700887147895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30137877400277133924765263 45206816100415700887147895)
        ·
          refine ⟨67810224150623551330721843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45206816100415700887147895 67810224150623551330721843)
          ·
            refine ⟨101715336225935326996082765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67810224150623551330721843 101715336225935326996082765)
            ·
              refine ⟨38143251084725747623531037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101715336225935326996082765 38143251084725747623531037)
              ·
                refine ⟨14303719156772155358824139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38143251084725747623531037 14303719156772155358824139)
                ·
                  refine ⟨21455578735158233038236209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14303719156772155358824139 21455578735158233038236209)
                  ·
                    refine ⟨16091684051368674778677157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21455578735158233038236209 16091684051368674778677157)
                    ·
                      refine ⟨3017190759631626521001967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16091684051368674778677157 3017190759631626521001967)
                      ·
                        rfl

theorem cell23_5875958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5875958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875958 prefixEnd_5875958 := by exact prefixLift 5875958
  have htrace : WordTrace (prefixWord ++ tailWord_5875958) baseStart_5875958 baseEnd_5875958 := by
    simpa [prefixWord, tailWord_5875958, baseEnd_5875958] using wordTrace_append hprefix tailTrace_5875958
  have hstable : (prefixWord ++ tailWord_5875958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875958).length < 2 ^ (prefixWord ++ tailWord_5875958).sum := by decide
  have hdescent : baseEnd_5875958 < baseStart_5875958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875978 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_5875978 : Nat := 118140960795 + 5875978 * 2 ^ 59
def prefixEnd_5875978 : Nat := 4983230072969 + 3 ^ 40 * 5875978 * 2
def baseEnd_5875978 : Nat := 3017201029244716442751875

theorem tailTrace_5875978 : CollatzResearch.WordTrace tailWord_5875978 prefixEnd_5875978 3017201029244716442751875 := by
  unfold tailWord_5875978
  simp only [CollatzResearch.WordTrace]
  refine ⟨53578631076585679497959147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142876349537561811994557725 53578631076585679497959147)
  ·
    refine ⟨80367946614878519246938721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53578631076585679497959147 80367946614878519246938721)
    ·
      refine ⟨60275959961158889435204041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80367946614878519246938721 60275959961158889435204041)
      ·
        refine ⟨45206969970869167076403031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60275959961158889435204041 45206969970869167076403031)
        ·
          refine ⟨67810454956303750614604547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45206969970869167076403031 67810454956303750614604547)
          ·
            refine ⟨101715682434455625921906821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67810454956303750614604547 101715682434455625921906821)
            ·
              refine ⟨19071690456460429860357529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101715682434455625921906821 19071690456460429860357529)
              ·
                refine ⟨14303767842345322395268147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19071690456460429860357529 14303767842345322395268147)
                ·
                  refine ⟨21455651763517983592902221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14303767842345322395268147 21455651763517983592902221)
                  ·
                    refine ⟨8045869411319243847338333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21455651763517983592902221 8045869411319243847338333)
                    ·
                      refine ⟨3017201029244716442751875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045869411319243847338333 3017201029244716442751875)
                      ·
                        rfl

theorem cell23_5875978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_5875978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875978 prefixEnd_5875978 := by exact prefixLift 5875978
  have htrace : WordTrace (prefixWord ++ tailWord_5875978) baseStart_5875978 baseEnd_5875978 := by
    simpa [prefixWord, tailWord_5875978, baseEnd_5875978] using wordTrace_append hprefix tailTrace_5875978
  have hstable : (prefixWord ++ tailWord_5875978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875978).length < 2 ^ (prefixWord ++ tailWord_5875978).sum := by decide
  have hdescent : baseEnd_5875978 < baseStart_5875978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5875995 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 3]
def baseStart_5875995 : Nat := 118140960795 + 5875995 * 2 ^ 59
def prefixEnd_5875995 : Nat := 4983230072969 + 3 ^ 40 * 5875995 * 2
def baseEnd_5875995 : Nat := 3017209758415842876239297

theorem tailTrace_5875995 : CollatzResearch.WordTrace tailWord_5875995 prefixEnd_5875995 3017209758415842876239297 := by
  unfold tailWord_5875995
  simp only [CollatzResearch.WordTrace]
  refine ⟨214315144347281129895205439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142876762898187419930136959 214315144347281129895205439)
  ·
    refine ⟨321472716520921694842808159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214315144347281129895205439 321472716520921694842808159)
    ·
      refine ⟨482209074781382542264212239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321472716520921694842808159 482209074781382542264212239)
      ·
        refine ⟨723313612172073813396318359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482209074781382542264212239 723313612172073813396318359)
        ·
          refine ⟨1084970418258110720094477539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723313612172073813396318359 1084970418258110720094477539)
          ·
            refine ⟨1627455627387166080141716309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084970418258110720094477539 1627455627387166080141716309)
            ·
              refine ⟨9535872816721676250830369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1627455627387166080141716309 9535872816721676250830369)
              ·
                refine ⟨7151904612541257188122777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9535872816721676250830369 7151904612541257188122777)
                ·
                  refine ⟨5363928459405942891092083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7151904612541257188122777 5363928459405942891092083)
                  ·
                    refine ⟨8045892689108914336638125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5363928459405942891092083 8045892689108914336638125)
                    ·
                      refine ⟨3017209758415842876239297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045892689108914336638125 3017209758415842876239297)
                      ·
                        rfl

theorem cell23_5875995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 3].length) (baseStart_5875995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5875995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5875995 prefixEnd_5875995 := by exact prefixLift 5875995
  have htrace : WordTrace (prefixWord ++ tailWord_5875995) baseStart_5875995 baseEnd_5875995 := by
    simpa [prefixWord, tailWord_5875995, baseEnd_5875995] using wordTrace_append hprefix tailTrace_5875995
  have hstable : (prefixWord ++ tailWord_5875995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5875995).length < 2 ^ (prefixWord ++ tailWord_5875995).sum := by decide
  have hdescent : baseEnd_5875995 < baseStart_5875995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5875995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876001 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5876001 : Nat := 118140960795 + 5876001 * 2 ^ 59
def prefixEnd_5876001 : Nat := 4983230072969 + 3 ^ 40 * 5876001 * 2
def baseEnd_5876001 : Nat := 3017212839299769852764269

theorem tailTrace_5876001 : CollatzResearch.WordTrace tailWord_5876001 prefixEnd_5876001 3017212839299769852764269 := by
  unfold tailWord_5876001
  simp only [CollatzResearch.WordTrace]
  refine ⟨214315363185259392919923857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142876908790172928613282571 214315363185259392919923857)
  ·
    refine ⟨160736522388944544689942893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214315363185259392919923857 160736522388944544689942893)
    ·
      refine ⟨60276195895854204258728585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160736522388944544689942893 60276195895854204258728585)
      ·
        refine ⟨45207146921890653194046439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60276195895854204258728585 45207146921890653194046439)
        ·
          refine ⟨67810720382835979791069659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45207146921890653194046439 67810720382835979791069659)
          ·
            refine ⟨101716080574253969686604489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67810720382835979791069659 101716080574253969686604489)
            ·
              refine ⟨76287060430690477264953367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101716080574253969686604489 76287060430690477264953367)
              ·
                refine ⟨114430590646035715897430051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76287060430690477264953367 114430590646035715897430051)
                ·
                  refine ⟨171645885969053573846145077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114430590646035715897430051 171645885969053573846145077)
                  ·
                    refine ⟨16091801809598772548076101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 171645885969053573846145077 16091801809598772548076101)
                    ·
                      refine ⟨3017212839299769852764269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16091801809598772548076101 3017212839299769852764269)
                      ·
                        rfl

theorem cell23_5876001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5876001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876001 prefixEnd_5876001 := by exact prefixLift 5876001
  have htrace : WordTrace (prefixWord ++ tailWord_5876001) baseStart_5876001 baseEnd_5876001 := by
    simpa [prefixWord, tailWord_5876001, baseEnd_5876001] using wordTrace_append hprefix tailTrace_5876001
  have hstable : (prefixWord ++ tailWord_5876001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876001).length < 2 ^ (prefixWord ++ tailWord_5876001).sum := by decide
  have hdescent : baseEnd_5876001 < baseStart_5876001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876035 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 4, 2, 2]
def baseStart_5876035 : Nat := 118140960795 + 5876035 * 2 ^ 59
def prefixEnd_5876035 : Nat := 4983230072969 + 3 ^ 40 * 5876035 * 2
def baseEnd_5876035 : Nat := 3017230297642022719739113

theorem tailTrace_5876035 : CollatzResearch.WordTrace tailWord_5876035 prefixEnd_5876035 3017230297642022719739113 := by
  unfold tailWord_5876035
  simp only [CollatzResearch.WordTrace]
  refine ⟨214316603267136216726661559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142877735511424144484441039 214316603267136216726661559)
  ·
    refine ⟨321474904900704325089992339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214316603267136216726661559 321474904900704325089992339)
    ·
      refine ⟨482212357351056487634988509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321474904900704325089992339 482212357351056487634988509)
      ·
        refine ⟨180829634006646182863120691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 482212357351056487634988509 180829634006646182863120691)
        ·
          refine ⟨271244451009969274294681037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180829634006646182863120691 271244451009969274294681037)
          ·
            refine ⟨101716669128738477860505389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271244451009969274294681037 101716669128738477860505389)
            ·
              refine ⟨38143750923276929197689521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101716669128738477860505389 38143750923276929197689521)
              ·
                refine ⟨28607813192457696898267141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38143750923276929197689521 28607813192457696898267141)
                ·
                  refine ⟨5363964973585818168425089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28607813192457696898267141 5363964973585818168425089)
                  ·
                    refine ⟨4022973730189363626318817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363964973585818168425089 4022973730189363626318817)
                    ·
                      refine ⟨3017230297642022719739113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022973730189363626318817 3017230297642022719739113)
                      ·
                        rfl

theorem cell23_5876035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_5876035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876035 prefixEnd_5876035 := by exact prefixLift 5876035
  have htrace : WordTrace (prefixWord ++ tailWord_5876035) baseStart_5876035 baseEnd_5876035 := by
    simpa [prefixWord, tailWord_5876035, baseEnd_5876035] using wordTrace_append hprefix tailTrace_5876035
  have hstable : (prefixWord ++ tailWord_5876035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876035).length < 2 ^ (prefixWord ++ tailWord_5876035).sum := by decide
  have hdescent : baseEnd_5876035 < baseStart_5876035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876052 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_5876052 : Nat := 118140960795 + 5876052 * 2 ^ 59
def prefixEnd_5876052 : Nat := 4983230072969 + 3 ^ 40 * 5876052 * 2
def baseEnd_5876052 : Nat := 3017239026813149153226535

theorem tailTrace_5876052 : CollatzResearch.WordTrace tailWord_5876052 prefixEnd_5876052 3017239026813149153226535 := by
  unfold tailWord_5876052
  simp only [CollatzResearch.WordTrace]
  refine ⟨107158611654037314315015205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142878148872049752420020273 107158611654037314315015205)
  ·
    refine ⟨20092239685131996434065351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107158611654037314315015205 20092239685131996434065351)
    ·
      refine ⟨30138359527697994651098027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20092239685131996434065351 30138359527697994651098027)
      ·
        refine ⟨45207539291546991976647041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30138359527697994651098027 45207539291546991976647041)
        ·
          refine ⟨33905654468660243982485281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45207539291546991976647041 33905654468660243982485281)
          ·
            refine ⟨25429240851495182986863961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33905654468660243982485281 25429240851495182986863961)
            ·
              refine ⟨19071930638621387240147971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25429240851495182986863961 19071930638621387240147971)
              ·
                refine ⟨28607895957932080860221957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19071930638621387240147971 28607895957932080860221957)
                ·
                  refine ⟨5363980492112265161291617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28607895957932080860221957 5363980492112265161291617)
                  ·
                    refine ⟨4022985369084198870968713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363980492112265161291617 4022985369084198870968713)
                    ·
                      refine ⟨3017239026813149153226535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022985369084198870968713 3017239026813149153226535)
                      ·
                        rfl

theorem cell23_5876052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_5876052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876052 prefixEnd_5876052 := by exact prefixLift 5876052
  have htrace : WordTrace (prefixWord ++ tailWord_5876052) baseStart_5876052 baseEnd_5876052 := by
    simpa [prefixWord, tailWord_5876052, baseEnd_5876052] using wordTrace_append hprefix tailTrace_5876052
  have hstable : (prefixWord ++ tailWord_5876052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876052).length < 2 ^ (prefixWord ++ tailWord_5876052).sum := by decide
  have hdescent : baseEnd_5876052 < baseStart_5876052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876068 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_5876068 : Nat := 118140960795 + 5876068 * 2 ^ 59
def prefixEnd_5876068 : Nat := 4983230072969 + 3 ^ 40 * 5876068 * 2
def baseEnd_5876068 : Nat := 3017247242503621090626461

theorem tailTrace_5876068 : CollatzResearch.WordTrace tailWord_5876068 prefixEnd_5876068 3017247242503621090626461 := by
  unfold tailWord_5876068
  simp only [CollatzResearch.WordTrace]
  refine ⟨107158903438008331681306429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142878537917344442241741905 107158903438008331681306429)
  ·
    refine ⟨40184588789253124380489911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107158903438008331681306429 40184588789253124380489911)
    ·
      refine ⟨60276883183879686570734867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40184588789253124380489911 60276883183879686570734867)
      ·
        refine ⟨90415324775819529856102301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60276883183879686570734867 90415324775819529856102301)
        ·
          refine ⟨33905746790932323696038363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90415324775819529856102301 33905746790932323696038363)
          ·
            refine ⟨50858620186398485544057545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33905746790932323696038363 50858620186398485544057545)
            ·
              refine ⟨38143965139798864158043159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50858620186398485544057545 38143965139798864158043159)
              ·
                refine ⟨57215947709698296237064739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38143965139798864158043159 57215947709698296237064739)
                ·
                  refine ⟨85823921564547444355597109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57215947709698296237064739 85823921564547444355597109)
                  ·
                    refine ⟨8045992646676322908337229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85823921564547444355597109 8045992646676322908337229)
                    ·
                      refine ⟨3017247242503621090626461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8045992646676322908337229 3017247242503621090626461)
                      ·
                        rfl

theorem cell23_5876068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_5876068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876068 prefixEnd_5876068 := by exact prefixLift 5876068
  have htrace : WordTrace (prefixWord ++ tailWord_5876068) baseStart_5876068 baseEnd_5876068 := by
    simpa [prefixWord, tailWord_5876068, baseEnd_5876068] using wordTrace_append hprefix tailTrace_5876068
  have hstable : (prefixWord ++ tailWord_5876068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876068).length < 2 ^ (prefixWord ++ tailWord_5876068).sum := by decide
  have hdescent : baseEnd_5876068 < baseStart_5876068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876069 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 2, 2, 2]
def baseStart_5876069 : Nat := 118140960795 + 5876069 * 2 ^ 59
def prefixEnd_5876069 : Nat := 4983230072969 + 3 ^ 40 * 5876069 * 2
def baseEnd_5876069 : Nat := 3017247755984275586713957

theorem tailTrace_5876069 : CollatzResearch.WordTrace tailWord_5876069 prefixEnd_5876069 3017247755984275586713957 := by
  unfold tailWord_5876069
  simp only [CollatzResearch.WordTrace]
  refine ⟨214317843349013040533399261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142878562232675360355599507 214317843349013040533399261)
  ·
    refine ⟨80369191255879890200024723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214317843349013040533399261 80369191255879890200024723)
    ·
      refine ⟨120553786883819835300037085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80369191255879890200024723 120553786883819835300037085)
      ·
        refine ⟨45207670081432438237513907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120553786883819835300037085 45207670081432438237513907)
        ·
          refine ⟨67811505122148657356270861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45207670081432438237513907 67811505122148657356270861)
          ·
            refine ⟨25429314420805746508601573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67811505122148657356270861 25429314420805746508601573)
            ·
              refine ⟨4767996453901077470362795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25429314420805746508601573 4767996453901077470362795)
              ·
                refine ⟨7151994680851616205544193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767996453901077470362795 7151994680851616205544193)
                ·
                  refine ⟨5363996010638712154158145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7151994680851616205544193 5363996010638712154158145)
                  ·
                    refine ⟨4022997007979034115618609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363996010638712154158145 4022997007979034115618609)
                    ·
                      refine ⟨3017247755984275586713957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4022997007979034115618609 3017247755984275586713957)
                      ·
                        rfl

theorem cell23_5876069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_5876069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876069 prefixEnd_5876069 := by exact prefixLift 5876069
  have htrace : WordTrace (prefixWord ++ tailWord_5876069) baseStart_5876069 baseEnd_5876069 := by
    simpa [prefixWord, tailWord_5876069, baseEnd_5876069] using wordTrace_append hprefix tailTrace_5876069
  have hstable : (prefixWord ++ tailWord_5876069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876069).length < 2 ^ (prefixWord ++ tailWord_5876069).sum := by decide
  have hdescent : baseEnd_5876069 < baseStart_5876069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876081 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_5876081 : Nat := 118140960795 + 5876081 * 2 ^ 59
def prefixEnd_5876081 : Nat := 4983230072969 + 3 ^ 40 * 5876081 * 2
def baseEnd_5876081 : Nat := 3017253917752129539763901

theorem tailTrace_5876081 : CollatzResearch.WordTrace tailWord_5876081 prefixEnd_5876081 3017253917752129539763901 := by
  unfold tailWord_5876081
  simp only [CollatzResearch.WordTrace]
  refine ⟨214318281024969566582836097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142878854016646377721890731 214318281024969566582836097)
  ·
    refine ⟨160738710768727174937127073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214318281024969566582836097 160738710768727174937127073)
    ·
      refine ⟨120554033076545381202845305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160738710768727174937127073 120554033076545381202845305)
      ·
        refine ⟨90415524807409035902133979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120554033076545381202845305 90415524807409035902133979)
        ·
          refine ⟨135623287211113553853200969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90415524807409035902133979 135623287211113553853200969)
          ·
            refine ⟨101717465408335165389900727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135623287211113553853200969 101717465408335165389900727)
            ·
              refine ⟨152576198112502748084851091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101717465408335165389900727 152576198112502748084851091)
              ·
                refine ⟨228864297168754122127276637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152576198112502748084851091 228864297168754122127276637)
                ·
                  refine ⟨85824111438282795797728739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228864297168754122127276637 85824111438282795797728739)
                  ·
                    refine ⟨128736167157424193696593109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85824111438282795797728739 128736167157424193696593109)
                    ·
                      refine ⟨3017253917752129539763901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128736167157424193696593109 3017253917752129539763901)
                      ·
                        rfl

theorem cell23_5876081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_5876081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876081 prefixEnd_5876081 := by exact prefixLift 5876081
  have htrace : WordTrace (prefixWord ++ tailWord_5876081) baseStart_5876081 baseEnd_5876081 := by
    simpa [prefixWord, tailWord_5876081, baseEnd_5876081] using wordTrace_append hprefix tailTrace_5876081
  have hstable : (prefixWord ++ tailWord_5876081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876081).length < 2 ^ (prefixWord ++ tailWord_5876081).sum := by decide
  have hdescent : baseEnd_5876081 < baseStart_5876081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876135 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5876135 : Nat := 118140960795 + 5876135 * 2 ^ 59
def prefixEnd_5876135 : Nat := 4983230072969 + 3 ^ 40 * 5876135 * 2
def baseEnd_5876135 : Nat := 1005760548569157442829551

theorem tailTrace_5876135 : CollatzResearch.WordTrace tailWord_5876135 prefixEnd_5876135 1005760548569157442829551 := by
  unfold tailWord_5876135
  simp only [CollatzResearch.WordTrace]
  refine ⟨214320250566773933805301859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142880167044515955870201239 214320250566773933805301859)
  ·
    refine ⟨321480375850160900707952789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214320250566773933805301859 321480375850160900707952789)
    ·
      refine ⟨15069392617976292220685287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 321480375850160900707952789 15069392617976292220685287)
      ·
        refine ⟨22604088926964438331027931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15069392617976292220685287 22604088926964438331027931)
        ·
          refine ⟨33906133390446657496541897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22604088926964438331027931 33906133390446657496541897)
          ·
            refine ⟨25429600042834993122406423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33906133390446657496541897 25429600042834993122406423)
            ·
              refine ⟨38144400064252489683609635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25429600042834993122406423 38144400064252489683609635)
              ·
                refine ⟨57216600096378734525414453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38144400064252489683609635 57216600096378734525414453)
                ·
                  refine ⟨5364056259035506361757605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57216600096378734525414453 5364056259035506361757605)
                  ·
                    refine ⟨1005760548569157442829551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364056259035506361757605 1005760548569157442829551)
                    ·
                      rfl

theorem cell23_5876135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5876135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876135 prefixEnd_5876135 := by exact prefixLift 5876135
  have htrace : WordTrace (prefixWord ++ tailWord_5876135) baseStart_5876135 baseEnd_5876135 := by
    simpa [prefixWord, tailWord_5876135, baseEnd_5876135] using wordTrace_append hprefix tailTrace_5876135
  have hstable : (prefixWord ++ tailWord_5876135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876135).length < 2 ^ (prefixWord ++ tailWord_5876135).sum := by decide
  have hdescent : baseEnd_5876135 < baseStart_5876135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876145 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_5876145 : Nat := 118140960795 + 5876145 * 2 ^ 59
def prefixEnd_5876145 : Nat := 4983230072969 + 3 ^ 40 * 5876145 * 2
def baseEnd_5876145 : Nat := 3017286780514017289363607

theorem tailTrace_5876145 : CollatzResearch.WordTrace tailWord_5876145 prefixEnd_5876145 3017286780514017289363607 := by
  unfold tailWord_5876145
  simp only [CollatzResearch.WordTrace]
  refine ⟨214320615296737705513165889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142880410197825137008777259 214320615296737705513165889)
  ·
    refine ⟨160740461472553279134874417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214320615296737705513165889 160740461472553279134874417)
    ·
      refine ⟨120555346104414959351155813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160740461472553279134874417 120555346104414959351155813)
      ·
        refine ⟨22604127394577804878341715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120555346104414959351155813 22604127394577804878341715)
        ·
          refine ⟨33906191091866707317512573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22604127394577804878341715 33906191091866707317512573)
          ·
            refine ⟨12714821659450015244067215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33906191091866707317512573 12714821659450015244067215)
            ·
              refine ⟨19072232489175022866100823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714821659450015244067215 19072232489175022866100823)
              ·
                refine ⟨28608348733762534299151235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19072232489175022866100823 28608348733762534299151235)
                ·
                  refine ⟨42912523100643801448726853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28608348733762534299151235 42912523100643801448726853)
                  ·
                    refine ⟨8046098081370712771636285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42912523100643801448726853 8046098081370712771636285)
                    ·
                      refine ⟨3017286780514017289363607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8046098081370712771636285 3017286780514017289363607)
                      ·
                        rfl

theorem cell23_5876145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_5876145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876145 prefixEnd_5876145 := by exact prefixLift 5876145
  have htrace : WordTrace (prefixWord ++ tailWord_5876145) baseStart_5876145 baseEnd_5876145 := by
    simpa [prefixWord, tailWord_5876145, baseEnd_5876145] using wordTrace_append hprefix tailTrace_5876145
  have hstable : (prefixWord ++ tailWord_5876145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876145).length < 2 ^ (prefixWord ++ tailWord_5876145).sum := by decide
  have hdescent : baseEnd_5876145 < baseStart_5876145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876168 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_5876168 : Nat := 118140960795 + 5876168 * 2 ^ 59
def prefixEnd_5876168 : Nat := 4983230072969 + 3 ^ 40 * 5876168 * 2
def baseEnd_5876168 : Nat := 3017298590569070699376001

theorem tailTrace_5876168 : CollatzResearch.WordTrace tailWord_5876168 prefixEnd_5876168 3017298590569070699376001 := by
  unfold tailWord_5876168
  simp only [CollatzResearch.WordTrace]
  refine ⟨107160727087827190220626579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142880969450436253627502105 107160727087827190220626579)
  ·
    refine ⟨160741090631740785330939869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107160727087827190220626579 160741090631740785330939869)
    ·
      refine ⟨60277908986902794499102451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160741090631740785330939869 60277908986902794499102451)
      ·
        refine ⟨90416863480354191748653677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60277908986902794499102451 90416863480354191748653677)
        ·
          refine ⟨33906323805132821905745129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90416863480354191748653677 33906323805132821905745129)
          ·
            refine ⟨25429742853849616429308847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33906323805132821905745129 25429742853849616429308847)
            ·
              refine ⟨38144614280774424643963271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25429742853849616429308847 38144614280774424643963271)
              ·
                refine ⟨57216921421161636965944907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38144614280774424643963271 57216921421161636965944907)
                ·
                  refine ⟨85825382131742455448917361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57216921421161636965944907 85825382131742455448917361)
                  ·
                    refine ⟨64369036598806841586688021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85825382131742455448917361 64369036598806841586688021)
                    ·
                      refine ⟨3017298590569070699376001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64369036598806841586688021 3017298590569070699376001)
                      ·
                        rfl

theorem cell23_5876168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_5876168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876168 prefixEnd_5876168 := by exact prefixLift 5876168
  have htrace : WordTrace (prefixWord ++ tailWord_5876168) baseStart_5876168 baseEnd_5876168 := by
    simpa [prefixWord, tailWord_5876168, baseEnd_5876168] using wordTrace_append hprefix tailTrace_5876168
  have hstable : (prefixWord ++ tailWord_5876168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876168).length < 2 ^ (prefixWord ++ tailWord_5876168).sum := by decide
  have hdescent : baseEnd_5876168 < baseStart_5876168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876185 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 3, 5, 2]
def baseStart_5876185 : Nat := 118140960795 + 5876185 * 2 ^ 59
def prefixEnd_5876185 : Nat := 4983230072969 + 3 ^ 40 * 5876185 * 2
def baseEnd_5876185 : Nat := 3017307319740197132863423

theorem tailTrace_5876185 : CollatzResearch.WordTrace tailWord_5876185 prefixEnd_5876185 3017307319740197132863423 := by
  unfold tailWord_5876185
  simp only [CollatzResearch.WordTrace]
  refine ⟨214322074216592792344622009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142881382811061861563081339 214322074216592792344622009)
  ·
    refine ⟨160741555662444594258466507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214322074216592792344622009 160741555662444594258466507)
    ·
      refine ⟨241112333493666891387699761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160741555662444594258466507 241112333493666891387699761)
      ·
        refine ⟨180834250120250168540774821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241112333493666891387699761 180834250120250168540774821)
        ·
          refine ⟨33906421897546906601395279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180834250120250168540774821 33906421897546906601395279)
          ·
            refine ⟨50859632846320359902092919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33906421897546906601395279 50859632846320359902092919)
            ·
              refine ⟨76289449269480539853139379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50859632846320359902092919 76289449269480539853139379)
              ·
                refine ⟨114434173904220809779709069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76289449269480539853139379 114434173904220809779709069)
                ·
                  refine ⟨42912815214082803667390901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114434173904220809779709069 42912815214082803667390901)
                  ·
                    refine ⟨4023076426320262843817897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42912815214082803667390901 4023076426320262843817897)
                    ·
                      refine ⟨3017307319740197132863423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023076426320262843817897 3017307319740197132863423)
                      ·
                        rfl

theorem cell23_5876185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_5876185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876185 prefixEnd_5876185 := by exact prefixLift 5876185
  have htrace : WordTrace (prefixWord ++ tailWord_5876185) baseStart_5876185 baseEnd_5876185 := by
    simpa [prefixWord, tailWord_5876185, baseEnd_5876185] using wordTrace_append hprefix tailTrace_5876185
  have hstable : (prefixWord ++ tailWord_5876185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876185).length < 2 ^ (prefixWord ++ tailWord_5876185).sum := by decide
  have hdescent : baseEnd_5876185 < baseStart_5876185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876202 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_5876202 : Nat := 118140960795 + 5876202 * 2 ^ 59
def prefixEnd_5876202 : Nat := 4983230072969 + 3 ^ 40 * 5876202 * 2
def baseEnd_5876202 : Nat := 3017316048911323566350845

theorem tailTrace_5876202 : CollatzResearch.WordTrace tailWord_5876202 prefixEnd_5876202 3017316048911323566350845 := by
  unfold tailWord_5876202
  simp only [CollatzResearch.WordTrace]
  refine ⟨53580673564382801061997715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142881796171687469498660573 53580673564382801061997715)
  ·
    refine ⟨80371010346574201592996573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53580673564382801061997715 80371010346574201592996573)
    ·
      refine ⟨30139128879965325597373715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80371010346574201592996573 30139128879965325597373715)
      ·
        refine ⟨45208693319947988396060573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30139128879965325597373715 45208693319947988396060573)
        ·
          refine ⟨16953259994980495648522715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45208693319947988396060573 16953259994980495648522715)
          ·
            refine ⟨25429889992470743472784073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953259994980495648522715 25429889992470743472784073)
            ·
              refine ⟨19072417494353057604588055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25429889992470743472784073 19072417494353057604588055)
              ·
                refine ⟨28608626241529586406882083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19072417494353057604588055 28608626241529586406882083)
                ·
                  refine ⟨42912939362294379610323125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28608626241529586406882083 42912939362294379610323125)
                  ·
                    refine ⟨4023088065215098088467793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42912939362294379610323125 4023088065215098088467793)
                    ·
                      refine ⟨3017316048911323566350845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023088065215098088467793 3017316048911323566350845)
                      ·
                        rfl

theorem cell23_5876202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_5876202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876202 prefixEnd_5876202 := by exact prefixLift 5876202
  have htrace : WordTrace (prefixWord ++ tailWord_5876202) baseStart_5876202 baseEnd_5876202 := by
    simpa [prefixWord, tailWord_5876202, baseEnd_5876202] using wordTrace_append hprefix tailTrace_5876202
  have hstable : (prefixWord ++ tailWord_5876202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876202).length < 2 ^ (prefixWord ++ tailWord_5876202).sum := by decide
  have hdescent : baseEnd_5876202 < baseStart_5876202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876208 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_5876208 : Nat := 118140960795 + 5876208 * 2 ^ 59
def prefixEnd_5876208 : Nat := 4983230072969 + 3 ^ 40 * 5876208 * 2
def baseEnd_5876208 : Nat := 1005773043265083514291939

theorem tailTrace_5876208 : CollatzResearch.WordTrace tailWord_5876208 prefixEnd_5876208 1005773043265083514291939 := by
  unfold tailWord_5876208
  simp only [CollatzResearch.WordTrace]
  refine ⟨107161456547754733636354639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142881942063672978181806185 107161456547754733636354639)
  ·
    refine ⟨160742184821632100454531959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107161456547754733636354639 160742184821632100454531959)
    ·
      refine ⟨241113277232448150681797939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160742184821632100454531959 241113277232448150681797939)
      ·
        refine ⟨361669915848672226022696909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241113277232448150681797939 361669915848672226022696909)
        ·
          refine ⟨135626218443252084758511341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361669915848672226022696909 135626218443252084758511341)
          ·
            refine ⟨50859831916219531784441753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135626218443252084758511341 50859831916219531784441753)
            ·
              refine ⟨38144873937164648838331315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50859831916219531784441753 38144873937164648838331315)
              ·
                refine ⟨57217310905746973257496973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38144873937164648838331315 57217310905746973257496973)
                ·
                  refine ⟨21456491589655114971561365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57217310905746973257496973 21456491589655114971561365)
                  ·
                    refine ⟨1005773043265083514291939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21456491589655114971561365 1005773043265083514291939)
                    ·
                      rfl

theorem cell23_5876208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_5876208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876208 prefixEnd_5876208 := by exact prefixLift 5876208
  have htrace : WordTrace (prefixWord ++ tailWord_5876208) baseStart_5876208 baseEnd_5876208 := by
    simpa [prefixWord, tailWord_5876208, baseEnd_5876208] using wordTrace_append hprefix tailTrace_5876208
  have hstable : (prefixWord ++ tailWord_5876208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876208).length < 2 ^ (prefixWord ++ tailWord_5876208).sum := by decide
  have hdescent : baseEnd_5876208 < baseStart_5876208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876235 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5]
def baseStart_5876235 : Nat := 118140960795 + 5876235 * 2 ^ 59
def prefixEnd_5876235 : Nat := 4983230072969 + 3 ^ 40 * 5876235 * 2
def baseEnd_5876235 : Nat := 3017332993772921937238193

theorem tailTrace_5876235 : CollatzResearch.WordTrace tailWord_5876235 prefixEnd_5876235 3017332993772921937238193 := by
  unfold tailWord_5876235
  simp only [CollatzResearch.WordTrace]
  refine ⟨214323897866411650883942159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142882598577607767255961439 214323897866411650883942159)
  ·
    refine ⟨321485846799617476325913239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214323897866411650883942159 321485846799617476325913239)
    ·
      refine ⟨482228770199426214488869859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321485846799617476325913239 482228770199426214488869859)
      ·
        refine ⟨723343155299139321733304789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482228770199426214488869859 723343155299139321733304789)
        ·
          refine ⟨16953355202323577853124331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 723343155299139321733304789 16953355202323577853124331)
          ·
            refine ⟨25430032803485366779686497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953355202323577853124331 25430032803485366779686497)
            ·
              refine ⟨19072524602614025084764873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25430032803485366779686497 19072524602614025084764873)
              ·
                refine ⟨14304393451960518813573655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19072524602614025084764873 14304393451960518813573655)
                ·
                  refine ⟨21456590177940778220360483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14304393451960518813573655 21456590177940778220360483)
                  ·
                    refine ⟨32184885266911167330540725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21456590177940778220360483 32184885266911167330540725)
                    ·
                      refine ⟨3017332993772921937238193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32184885266911167330540725 3017332993772921937238193)
                      ·
                        rfl

theorem cell23_5876235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].length) (baseStart_5876235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876235 prefixEnd_5876235 := by exact prefixLift 5876235
  have htrace : WordTrace (prefixWord ++ tailWord_5876235) baseStart_5876235 baseEnd_5876235 := by
    simpa [prefixWord, tailWord_5876235, baseEnd_5876235] using wordTrace_append hprefix tailTrace_5876235
  have hstable : (prefixWord ++ tailWord_5876235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876235).length < 2 ^ (prefixWord ++ tailWord_5876235).sum := by decide
  have hdescent : baseEnd_5876235 < baseStart_5876235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876245 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_5876245 : Nat := 118140960795 + 5876245 * 2 ^ 59
def prefixEnd_5876245 : Nat := 4983230072969 + 3 ^ 40 * 5876245 * 2
def baseEnd_5876245 : Nat := 3017338128579466898113147

theorem tailTrace_5876245 : CollatzResearch.WordTrace tailWord_5876245 prefixEnd_5876245 3017338128579466898113147 := by
  unfold tailWord_5876245
  simp only [CollatzResearch.WordTrace]
  refine ⟨214324262596375422591806189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142882841730916948394537459 214324262596375422591806189)
  ·
    refine ⟨80371598473640783471927321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214324262596375422591806189 80371598473640783471927321)
    ·
      refine ⟨60278698855230587603945491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80371598473640783471927321 60278698855230587603945491)
      ·
        refine ⟨90418048282845881405918237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60278698855230587603945491 90418048282845881405918237)
        ·
          refine ⟨33906768106067205527219339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90418048282845881405918237 33906768106067205527219339)
          ·
            refine ⟨50860152159100808290829009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33906768106067205527219339 50860152159100808290829009)
            ·
              refine ⟨38145114119325606218121757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50860152159100808290829009 38145114119325606218121757)
              ·
                refine ⟨14304417794747102331795659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38145114119325606218121757 14304417794747102331795659)
                ·
                  refine ⟨21456626692120653497693489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14304417794747102331795659 21456626692120653497693489)
                  ·
                    refine ⟨16092470019090490123270117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21456626692120653497693489 16092470019090490123270117)
                    ·
                      refine ⟨3017338128579466898113147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16092470019090490123270117 3017338128579466898113147)
                      ·
                        rfl

theorem cell23_5876245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_5876245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876245 prefixEnd_5876245 := by exact prefixLift 5876245
  have htrace : WordTrace (prefixWord ++ tailWord_5876245) baseStart_5876245 baseEnd_5876245 := by
    simpa [prefixWord, tailWord_5876245, baseEnd_5876245] using wordTrace_append hprefix tailTrace_5876245
  have hstable : (prefixWord ++ tailWord_5876245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876245).length < 2 ^ (prefixWord ++ tailWord_5876245).sum := by decide
  have hdescent : baseEnd_5876245 < baseStart_5876245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876252 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5876252 : Nat := 118140960795 + 5876252 * 2 ^ 59
def prefixEnd_5876252 : Nat := 4983230072969 + 3 ^ 40 * 5876252 * 2
def baseEnd_5876252 : Nat := 3017341722944048370725615

theorem tailTrace_5876252 : CollatzResearch.WordTrace tailWord_5876252 prefixEnd_5876252 3017341722944048370725615 := by
  unfold tailWord_5876252
  simp only [CollatzResearch.WordTrace]
  refine ⟨107162258953675031393655505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142883011938233375191540673 107162258953675031393655505)
  ·
    refine ⟨80371694215256273545241629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107162258953675031393655505 80371694215256273545241629)
    ·
      refine ⟨30139385330721102579465611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80371694215256273545241629 30139385330721102579465611)
      ·
        refine ⟨45209077996081653869198417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30139385330721102579465611 45209077996081653869198417)
        ·
          refine ⟨33906808497061240401898813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45209077996081653869198417 33906808497061240401898813)
          ·
            refine ⟨12715053186397965150712055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33906808497061240401898813 12715053186397965150712055)
            ·
              refine ⟨19072579779596947726068083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12715053186397965150712055 19072579779596947726068083)
              ·
                refine ⟨28608869669395421589102125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19072579779596947726068083 28608869669395421589102125)
                ·
                  refine ⟨10728326126023283095913297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28608869669395421589102125 10728326126023283095913297)
                  ·
                    refine ⟨8046244594517462321934973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10728326126023283095913297 8046244594517462321934973)
                    ·
                      refine ⟨3017341722944048370725615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8046244594517462321934973 3017341722944048370725615)
                      ·
                        rfl

theorem cell23_5876252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5876252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876252 prefixEnd_5876252 := by exact prefixLift 5876252
  have htrace : WordTrace (prefixWord ++ tailWord_5876252) baseStart_5876252 baseEnd_5876252 := by
    simpa [prefixWord, tailWord_5876252, baseEnd_5876252] using wordTrace_append hprefix tailTrace_5876252
  have hstable : (prefixWord ++ tailWord_5876252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876252).length < 2 ^ (prefixWord ++ tailWord_5876252).sum := by decide
  have hdescent : baseEnd_5876252 < baseStart_5876252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876268 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_5876268 : Nat := 118140960795 + 5876268 * 2 ^ 59
def prefixEnd_5876268 : Nat := 4983230072969 + 3 ^ 40 * 5876268 * 2
def baseEnd_5876268 : Nat := 1005783312878173436041847

theorem tailTrace_5876268 : CollatzResearch.WordTrace tailWord_5876268 prefixEnd_5876268 1005783312878173436041847 := by
  unfold tailWord_5876268
  simp only [CollatzResearch.WordTrace]
  refine ⟨107162550737646048759946729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142883400983528065013262305 107162550737646048759946729)
  ·
    refine ⟨80371913053234536569960047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107162550737646048759946729 80371913053234536569960047)
    ·
      refine ⟨120557869579851804854940071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80371913053234536569960047 120557869579851804854940071)
      ·
        refine ⟨180836804369777707282410107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120557869579851804854940071 180836804369777707282410107)
        ·
          refine ⟨271255206554666560923615161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180836804369777707282410107 271255206554666560923615161)
          ·
            refine ⟨203441404915999920692711371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271255206554666560923615161 203441404915999920692711371)
            ·
              refine ⟨305162107373999881039067057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203441404915999920692711371 305162107373999881039067057)
              ·
                refine ⟨228871580530499910779300293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305162107373999881039067057 228871580530499910779300293)
                ·
                  refine ⟨42913421349468733271118805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228871580530499910779300293 42913421349468733271118805)
                  ·
                    refine ⟨1005783312878173436041847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42913421349468733271118805 1005783312878173436041847)
                    ·
                      rfl

theorem cell23_5876268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_5876268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876268 prefixEnd_5876268 := by exact prefixLift 5876268
  have htrace : WordTrace (prefixWord ++ tailWord_5876268) baseStart_5876268 baseEnd_5876268 := by
    simpa [prefixWord, tailWord_5876268, baseEnd_5876268] using wordTrace_append hprefix tailTrace_5876268
  have hstable : (prefixWord ++ tailWord_5876268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876268).length < 2 ^ (prefixWord ++ tailWord_5876268).sum := by decide
  have hdescent : baseEnd_5876268 < baseStart_5876268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876285 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_5876285 : Nat := 118140960795 + 5876285 * 2 ^ 59
def prefixEnd_5876285 : Nat := 4983230072969 + 3 ^ 40 * 5876285 * 2
def baseEnd_5876285 : Nat := 1005786222601882247204321

theorem tailTrace_5876285 : CollatzResearch.WordTrace tailWord_5876285 prefixEnd_5876285 1005786222601882247204321 := by
  unfold tailWord_5876285
  simp only [CollatzResearch.WordTrace]
  refine ⟨214325721516230509423262309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142883814344153672948841539 214325721516230509423262309)
  ·
    refine ⟨40186072784293220516861683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214325721516230509423262309 40186072784293220516861683)
    ·
      refine ⟨60279109176439830775292525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40186072784293220516861683 60279109176439830775292525)
      ·
        refine ⟨22604665941164936540734697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60279109176439830775292525 22604665941164936540734697)
        ·
          refine ⟨16953499455873702405551023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22604665941164936540734697 16953499455873702405551023)
          ·
            refine ⟨25430249183810553608326535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953499455873702405551023 25430249183810553608326535)
            ·
              refine ⟨38145373775715830412489803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25430249183810553608326535 38145373775715830412489803)
              ·
                refine ⟨57218060663573745618734705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38145373775715830412489803 57218060663573745618734705)
                ·
                  refine ⟨42913545497680309214051029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57218060663573745618734705 42913545497680309214051029)
                  ·
                    refine ⟨1005786222601882247204321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42913545497680309214051029 1005786222601882247204321)
                    ·
                      rfl

theorem cell23_5876285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_5876285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876285 prefixEnd_5876285 := by exact prefixLift 5876285
  have htrace : WordTrace (prefixWord ++ tailWord_5876285) baseStart_5876285 baseEnd_5876285 := by
    simpa [prefixWord, tailWord_5876285, baseEnd_5876285] using wordTrace_append hprefix tailTrace_5876285
  have hstable : (prefixWord ++ tailWord_5876285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876285).length < 2 ^ (prefixWord ++ tailWord_5876285).sum := by decide
  have hdescent : baseEnd_5876285 < baseStart_5876285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876335 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_5876335 : Nat := 118140960795 + 5876335 * 2 ^ 59
def prefixEnd_5876335 : Nat := 4983230072969 + 3 ^ 40 * 5876335 * 2
def baseEnd_5876335 : Nat := 3017384341838371545987733

theorem tailTrace_5876335 : CollatzResearch.WordTrace tailWord_5876335 prefixEnd_5876335 3017384341838371545987733 := by
  unfold tailWord_5876335
  simp only [CollatzResearch.WordTrace]
  refine ⟨214327545166049367962582459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142885030110699578641721639 214327545166049367962582459)
  ·
    refine ⟨321491317749074051943873689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214327545166049367962582459 321491317749074051943873689)
    ·
      refine ⟨241118488311805538957905267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321491317749074051943873689 241118488311805538957905267)
      ·
        refine ⟨361677732467708308436857901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241118488311805538957905267 361677732467708308436857901)
        ·
          refine ⟨135629149675390615663821713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361677732467708308436857901 135629149675390615663821713)
          ·
            refine ⟨101721862256542961747866285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135629149675390615663821713 101721862256542961747866285)
            ·
              refine ⟨38145698346203610655449857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101721862256542961747866285 38145698346203610655449857)
              ·
                refine ⟨28609273759652707991587393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38145698346203610655449857 28609273759652707991587393)
                ·
                  refine ⟨21456955319739530993690545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28609273759652707991587393 21456955319739530993690545)
                  ·
                    refine ⟨16092716489804648245267909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21456955319739530993690545 16092716489804648245267909)
                    ·
                      refine ⟨3017384341838371545987733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16092716489804648245267909 3017384341838371545987733)
                      ·
                        rfl

theorem cell23_5876335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_5876335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876335 prefixEnd_5876335 := by exact prefixLift 5876335
  have htrace : WordTrace (prefixWord ++ tailWord_5876335) baseStart_5876335 baseEnd_5876335 := by
    simpa [prefixWord, tailWord_5876335, baseEnd_5876335] using wordTrace_append hprefix tailTrace_5876335
  have hstable : (prefixWord ++ tailWord_5876335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876335).length < 2 ^ (prefixWord ++ tailWord_5876335).sum := by decide
  have hdescent : baseEnd_5876335 < baseStart_5876335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876339 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 2, 2, 2]
def baseStart_5876339 : Nat := 118140960795 + 5876339 * 2 ^ 59
def prefixEnd_5876339 : Nat := 4983230072969 + 3 ^ 40 * 5876339 * 2
def baseEnd_5876339 : Nat := 3017386395760989530337715

theorem tailTrace_5876339 : CollatzResearch.WordTrace tailWord_5876339 prefixEnd_5876339 3017386395760989530337715 := by
  unfold tailWord_5876339
  simp only [CollatzResearch.WordTrace]
  refine ⟨214327691058034876645728071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142885127372023251097152047 214327691058034876645728071)
  ·
    refine ⟨321491536587052314968592107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214327691058034876645728071 321491536587052314968592107)
    ·
      refine ⟨482237304880578472452888161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321491536587052314968592107 482237304880578472452888161)
      ·
        refine ⟨361677978660433854339666121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482237304880578472452888161 361677978660433854339666121)
        ·
          refine ⟨271258483995325390754749591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361677978660433854339666121 271258483995325390754749591)
          ·
            refine ⟨406887725992988086132124387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271258483995325390754749591 406887725992988086132124387)
            ·
              refine ⟨610331588989482129198186581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406887725992988086132124387 610331588989482129198186581)
              ·
                refine ⟨7152323308470493701541249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 610331588989482129198186581 7152323308470493701541249)
                ·
                  refine ⟨5364242481352870276155937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7152323308470493701541249 5364242481352870276155937)
                  ·
                    refine ⟨4023181861014652707116953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5364242481352870276155937 4023181861014652707116953)
                    ·
                      refine ⟨3017386395760989530337715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023181861014652707116953 3017386395760989530337715)
                      ·
                        rfl

theorem cell23_5876339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 2, 2].length) (baseStart_5876339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876339 prefixEnd_5876339 := by exact prefixLift 5876339
  have htrace : WordTrace (prefixWord ++ tailWord_5876339) baseStart_5876339 baseEnd_5876339 := by
    simpa [prefixWord, tailWord_5876339, baseEnd_5876339] using wordTrace_append hprefix tailTrace_5876339
  have hstable : (prefixWord ++ tailWord_5876339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876339).length < 2 ^ (prefixWord ++ tailWord_5876339).sum := by decide
  have hdescent : baseEnd_5876339 < baseStart_5876339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876345 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 7]
def baseStart_5876345 : Nat := 118140960795 + 5876345 * 2 ^ 59
def prefixEnd_5876345 : Nat := 4983230072969 + 3 ^ 40 * 5876345 * 2
def baseEnd_5876345 : Nat := 335265497404990722984743

theorem tailTrace_5876345 : CollatzResearch.WordTrace tailWord_5876345 prefixEnd_5876345 335265497404990722984743 := by
  unfold tailWord_5876345
  simp only [CollatzResearch.WordTrace]
  refine ⟨214327909896013139670446489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142885273264008759780297659 214327909896013139670446489)
  ·
    refine ⟨160745932422009854752834867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214327909896013139670446489 160745932422009854752834867)
    ·
      refine ⟨241118898633014782129252301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160745932422009854752834867 241118898633014782129252301)
      ·
        refine ⟨90419586987380543298469613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241118898633014782129252301 90419586987380543298469613)
        ·
          refine ⟨33907345120267703736926105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90419586987380543298469613 33907345120267703736926105)
          ·
            refine ⟨25430508840200777802694579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33907345120267703736926105 25430508840200777802694579)
            ·
              refine ⟨38145763260301166704041869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25430508840200777802694579 38145763260301166704041869)
              ·
                refine ⟨14304661222612937514015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38145763260301166704041869 14304661222612937514015701)
                ·
                  refine ⟨335265497404990722984743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14304661222612937514015701 335265497404990722984743)
                  ·
                    rfl

theorem cell23_5876345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_5876345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876345 prefixEnd_5876345 := by exact prefixLift 5876345
  have htrace : WordTrace (prefixWord ++ tailWord_5876345) baseStart_5876345 baseEnd_5876345 := by
    simpa [prefixWord, tailWord_5876345, baseEnd_5876345] using wordTrace_append hprefix tailTrace_5876345
  have hstable : (prefixWord ++ tailWord_5876345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876345).length < 2 ^ (prefixWord ++ tailWord_5876345).sum := by decide
  have hdescent : baseEnd_5876345 < baseStart_5876345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876356 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_5876356 : Nat := 118140960795 + 5876356 * 2 ^ 59
def prefixEnd_5876356 : Nat := 4983230072969 + 3 ^ 40 * 5876356 * 2
def baseEnd_5876356 : Nat := 3017395124932115963825137

theorem tailTrace_5876356 : CollatzResearch.WordTrace tailWord_5876356 prefixEnd_5876356 3017395124932115963825137 := by
  unfold tailWord_5876356
  simp only [CollatzResearch.WordTrace]
  refine ⟨107164155549486644274548461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142885540732648859032731281 107164155549486644274548461)
  ·
    refine ⟨40186558331057491602955673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107164155549486644274548461 40186558331057491602955673)
    ·
      refine ⟨30139918748293118702216755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40186558331057491602955673 30139918748293118702216755)
      ·
        refine ⟨45209878122439678053325133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30139918748293118702216755 45209878122439678053325133)
        ·
          refine ⟨16953704295914879269996925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45209878122439678053325133 16953704295914879269996925)
          ·
            refine ⟨6357639110968079726248847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16953704295914879269996925 6357639110968079726248847)
            ·
              refine ⟨9536458666452119589373271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357639110968079726248847 9536458666452119589373271)
              ·
                refine ⟨14304687999678179384059907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9536458666452119589373271 14304687999678179384059907)
                ·
                  refine ⟨21457031999517269076089861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14304687999678179384059907 21457031999517269076089861)
                  ·
                    refine ⟨4023193499909487951766849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21457031999517269076089861 4023193499909487951766849)
                    ·
                      refine ⟨3017395124932115963825137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023193499909487951766849 3017395124932115963825137)
                      ·
                        rfl

theorem cell23_5876356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_5876356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876356 prefixEnd_5876356 := by exact prefixLift 5876356
  have htrace : WordTrace (prefixWord ++ tailWord_5876356) baseStart_5876356 baseEnd_5876356 := by
    simpa [prefixWord, tailWord_5876356, baseEnd_5876356] using wordTrace_append hprefix tailTrace_5876356
  have hstable : (prefixWord ++ tailWord_5876356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876356).length < 2 ^ (prefixWord ++ tailWord_5876356).sum := by decide
  have hdescent : baseEnd_5876356 < baseStart_5876356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876375 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 1, 7]
def baseStart_5876375 : Nat := 118140960795 + 5876375 * 2 ^ 59
def prefixEnd_5876375 : Nat := 4983230072969 + 3 ^ 40 * 5876375 * 2
def baseEnd_5876375 : Nat := 1005801627021517129829183

theorem tailTrace_5876375 : CollatzResearch.WordTrace tailWord_5876375 prefixEnd_5876375 1005801627021517129829183 := by
  unfold tailWord_5876375
  simp only [CollatzResearch.WordTrace]
  refine ⟨214329004085904454794038579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142886002723936303196025719 214329004085904454794038579)
  ·
    refine ⟨321493506128856682191057869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214329004085904454794038579 321493506128856682191057869)
    ·
      refine ⟨120560064798321255821646701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321493506128856682191057869 120560064798321255821646701)
      ·
        refine ⟨45210024299370470933117513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120560064798321255821646701 45210024299370470933117513)
        ·
          refine ⟨33907518224527853199838135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45210024299370470933117513 33907518224527853199838135)
          ·
            refine ⟨50861277336791779799757203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33907518224527853199838135 50861277336791779799757203)
            ·
              refine ⟨76291916005187669699635805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50861277336791779799757203 76291916005187669699635805)
              ·
                refine ⟨28609468501945376137363427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76291916005187669699635805 28609468501945376137363427)
                ·
                  refine ⟨42914202752918064206045141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28609468501945376137363427 42914202752918064206045141)
                  ·
                    refine ⟨1005801627021517129829183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42914202752918064206045141 1005801627021517129829183)
                    ·
                      rfl

theorem cell23_5876375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_5876375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876375 prefixEnd_5876375 := by exact prefixLift 5876375
  have htrace : WordTrace (prefixWord ++ tailWord_5876375) baseStart_5876375 baseEnd_5876375 := by
    simpa [prefixWord, tailWord_5876375, baseEnd_5876375] using wordTrace_append hprefix tailTrace_5876375
  have hstable : (prefixWord ++ tailWord_5876375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876375).length < 2 ^ (prefixWord ++ tailWord_5876375).sum := by decide
  have hdescent : baseEnd_5876375 < baseStart_5876375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876412 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5876412 : Nat := 118140960795 + 5876412 * 2 ^ 59
def prefixEnd_5876412 : Nat := 4983230072969 + 3 ^ 40 * 5876412 * 2
def baseEnd_5876412 : Nat := 3017423879848767744724879

theorem tailTrace_5876412 : CollatzResearch.WordTrace tailWord_5876412 prefixEnd_5876412 3017423879848767744724879 := by
  unfold tailWord_5876412
  simp only [CollatzResearch.WordTrace]
  refine ⟨107165176793385205056567745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142886902391180273408756993 107165176793385205056567745)
  ·
    refine ⟨80373882595038903792425809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107165176793385205056567745 80373882595038903792425809)
    ·
      refine ⟨60280411946279177844319357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80373882595038903792425809 60280411946279177844319357)
      ·
        refine ⟨22605154479854691691619759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60280411946279177844319357 22605154479854691691619759)
        ·
          refine ⟨33907731719782037537429639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22605154479854691691619759 33907731719782037537429639)
          ·
            refine ⟨50861597579673056306144459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33907731719782037537429639 50861597579673056306144459)
            ·
              refine ⟨76292396369509584459216689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50861597579673056306144459 76292396369509584459216689)
              ·
                refine ⟨57219297277132188344412517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76292396369509584459216689 57219297277132188344412517)
                ·
                  refine ⟨10728618239462285314577347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57219297277132188344412517 10728618239462285314577347)
                  ·
                    refine ⟨16092927359193427971866021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10728618239462285314577347 16092927359193427971866021)
                    ·
                      refine ⟨3017423879848767744724879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16092927359193427971866021 3017423879848767744724879)
                      ·
                        rfl

theorem cell23_5876412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5876412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876412 prefixEnd_5876412 := by exact prefixLift 5876412
  have htrace : WordTrace (prefixWord ++ tailWord_5876412) baseStart_5876412 baseEnd_5876412 := by
    simpa [prefixWord, tailWord_5876412, baseEnd_5876412] using wordTrace_append hprefix tailTrace_5876412
  have hstable : (prefixWord ++ tailWord_5876412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876412).length < 2 ^ (prefixWord ++ tailWord_5876412).sum := by decide
  have hdescent : baseEnd_5876412 < baseStart_5876412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876449 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_5876449 : Nat := 118140960795 + 5876449 * 2 ^ 59
def prefixEnd_5876449 : Nat := 4983230072969 + 3 ^ 40 * 5876449 * 2
def baseEnd_5876449 : Nat := 3017442878632984099962209

theorem tailTrace_5876449 : CollatzResearch.WordTrace tailWord_5876449 prefixEnd_5876449 3017442878632984099962209 := by
  unfold tailWord_5876449
  simp only [CollatzResearch.WordTrace]
  refine ⟨214331703087636365432232401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142887802058424243621488267 214331703087636365432232401)
  ·
    refine ⟨160748777315727274074174301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214331703087636365432232401 160748777315727274074174301)
    ·
      refine ⟨60280791493397727777815363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160748777315727274074174301 60280791493397727777815363)
      ·
        refine ⟨90421187240096591666723045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60280791493397727777815363 90421187240096591666723045)
        ·
          refine ⟨16953972607518110937510571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90421187240096591666723045 16953972607518110937510571)
          ·
            refine ⟨25430958911277166406265857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953972607518110937510571 25430958911277166406265857)
            ·
              refine ⟨19073219183457874804699393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25430958911277166406265857 19073219183457874804699393)
              ·
                refine ⟨14304914387593406103524545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19073219183457874804699393 14304914387593406103524545)
                ·
                  refine ⟨10728685790695054577643409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14304914387593406103524545 10728685790695054577643409)
                  ·
                    refine ⟨8046514343021290933232557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10728685790695054577643409 8046514343021290933232557)
                    ·
                      refine ⟨3017442878632984099962209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8046514343021290933232557 3017442878632984099962209)
                      ·
                        rfl

theorem cell23_5876449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_5876449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876449 prefixEnd_5876449 := by exact prefixLift 5876449
  have htrace : WordTrace (prefixWord ++ tailWord_5876449) baseStart_5876449 baseEnd_5876449 := by
    simpa [prefixWord, tailWord_5876449, baseEnd_5876449] using wordTrace_append hprefix tailTrace_5876449
  have hstable : (prefixWord ++ tailWord_5876449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876449).length < 2 ^ (prefixWord ++ tailWord_5876449).sum := by decide
  have hdescent : baseEnd_5876449 < baseStart_5876449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876452 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 6]
def baseStart_5876452 : Nat := 118140960795 + 5876452 * 2 ^ 59
def prefixEnd_5876452 : Nat := 4983230072969 + 3 ^ 40 * 5876452 * 2
def baseEnd_5876452 : Nat := 335271602119438620913855

theorem tailTrace_5876452 : CollatzResearch.WordTrace tailWord_5876452 prefixEnd_5876452 335271602119438620913855 := by
  unfold tailWord_5876452
  simp only [CollatzResearch.WordTrace]
  refine ⟨107165906253312748472295805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142887875004416997963061073 107165906253312748472295805)
  ·
    refine ⟨40187214844992280677110927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107165906253312748472295805 40187214844992280677110927)
    ·
      refine ⟨60280822267488421015666391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40187214844992280677110927 60280822267488421015666391)
      ·
        refine ⟨90421233401232631523499587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60280822267488421015666391 90421233401232631523499587)
        ·
          refine ⟨135631850101848947285249381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90421233401232631523499587 135631850101848947285249381)
          ·
            refine ⟨25430971894096677615984259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135631850101848947285249381 25430971894096677615984259)
            ·
              refine ⟨38146457841145016423976389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25430971894096677615984259 38146457841145016423976389)
              ·
                refine ⟨7152460845214690579495573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38146457841145016423976389 7152460845214690579495573)
                ·
                  refine ⟨335271602119438620913855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7152460845214690579495573 335271602119438620913855)
                  ·
                    rfl

theorem cell23_5876452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_5876452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876452 prefixEnd_5876452 := by exact prefixLift 5876452
  have htrace : WordTrace (prefixWord ++ tailWord_5876452) baseStart_5876452 baseEnd_5876452 := by
    simpa [prefixWord, tailWord_5876452, baseEnd_5876452] using wordTrace_append hprefix tailTrace_5876452
  have hstable : (prefixWord ++ tailWord_5876452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876452).length < 2 ^ (prefixWord ++ tailWord_5876452).sum := by decide
  have hdescent : baseEnd_5876452 < baseStart_5876452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876475 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_5876475 : Nat := 118140960795 + 5876475 * 2 ^ 59
def prefixEnd_5876475 : Nat := 4983230072969 + 3 ^ 40 * 5876475 * 2
def baseEnd_5876475 : Nat := 3017456229130000998237089

theorem tailTrace_5876475 : CollatzResearch.WordTrace tailWord_5876475 prefixEnd_5876475 3017456229130000998237089 := by
  unfold tailWord_5876475
  simp only [CollatzResearch.WordTrace]
  refine ⟨214332651385542171872678879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142888434257028114581785919 214332651385542171872678879)
  ·
    refine ⟨321498977078313257809018319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214332651385542171872678879 321498977078313257809018319)
    ·
      refine ⟨482248465617469886713527479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321498977078313257809018319 482248465617469886713527479)
      ·
        refine ⟨723372698426204830070291219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482248465617469886713527479 723372698426204830070291219)
        ·
          refine ⟨1085059047639307245105436829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723372698426204830070291219 1085059047639307245105436829)
          ·
            refine ⟨406897142864740216914538811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1085059047639307245105436829 406897142864740216914538811)
            ·
              refine ⟨610345714297110325371808217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406897142864740216914538811 610345714297110325371808217)
              ·
                refine ⟨457759285722832744028856163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610345714297110325371808217 457759285722832744028856163)
                ·
                  refine ⟨686638928584249116043284245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457759285722832744028856163 686638928584249116043284245)
                  ·
                    refine ⟨32186199777386677314528949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 686638928584249116043284245 32186199777386677314528949)
                    ·
                      refine ⟨3017456229130000998237089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32186199777386677314528949 3017456229130000998237089)
                      ·
                        rfl

theorem cell23_5876475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_5876475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876475 prefixEnd_5876475 := by exact prefixLift 5876475
  have htrace : WordTrace (prefixWord ++ tailWord_5876475) baseStart_5876475 baseEnd_5876475 := by
    simpa [prefixWord, tailWord_5876475, baseEnd_5876475] using wordTrace_append hprefix tailTrace_5876475
  have hstable : (prefixWord ++ tailWord_5876475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876475).length < 2 ^ (prefixWord ++ tailWord_5876475).sum := by decide
  have hdescent : baseEnd_5876475 < baseStart_5876475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876536 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 3, 2, 2]
def baseStart_5876536 : Nat := 118140960795 + 5876536 * 2 ^ 59
def prefixEnd_5876536 : Nat := 4983230072969 + 3 ^ 40 * 5876536 * 2
def baseEnd_5876536 : Nat := 3017487551449925259574309

theorem tailTrace_5876536 : CollatzResearch.WordTrace tailWord_5876536 prefixEnd_5876536 3017487551449925259574309 := by
  unfold tailWord_5876536
  simp only [CollatzResearch.WordTrace]
  refine ⟨107167438119160589645324731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142889917492214119527099641 107167438119160589645324731)
  ·
    refine ⟨160751157178740884467987097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107167438119160589645324731 160751157178740884467987097)
    ·
      refine ⟨120563367884055663350990323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160751157178740884467987097 120563367884055663350990323)
      ·
        refine ⟨180845051826083495026485485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120563367884055663350990323 180845051826083495026485485)
        ·
          refine ⟨67816894434781310634932057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180845051826083495026485485 67816894434781310634932057)
          ·
            refine ⟨50862670826085982976199043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67816894434781310634932057 50862670826085982976199043)
            ·
              refine ⟨76294006239128974464298565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50862670826085982976199043 76294006239128974464298565)
              ·
                refine ⟨14305126169836682712055981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76294006239128974464298565 14305126169836682712055981)
                ·
                  refine ⟨5364422313688756017020993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14305126169836682712055981 5364422313688756017020993)
                  ·
                    refine ⟨4023316735266567012765745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5364422313688756017020993 4023316735266567012765745)
                    ·
                      refine ⟨3017487551449925259574309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023316735266567012765745 3017487551449925259574309)
                      ·
                        rfl

theorem cell23_5876536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_5876536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876536 prefixEnd_5876536 := by exact prefixLift 5876536
  have htrace : WordTrace (prefixWord ++ tailWord_5876536) baseStart_5876536 baseEnd_5876536 := by
    simpa [prefixWord, tailWord_5876536, baseEnd_5876536] using wordTrace_append hprefix tailTrace_5876536
  have hstable : (prefixWord ++ tailWord_5876536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876536).length < 2 ^ (prefixWord ++ tailWord_5876536).sum := by decide
  have hdescent : baseEnd_5876536 < baseStart_5876536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876556 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_5876556 : Nat := 118140960795 + 5876556 * 2 ^ 59
def prefixEnd_5876556 : Nat := 4983230072969 + 3 ^ 40 * 5876556 * 2
def baseEnd_5876556 : Nat := 3017497821063015181324217

theorem tailTrace_5876556 : CollatzResearch.WordTrace tailWord_5876556 prefixEnd_5876556 3017497821063015181324217 := by
  unfold tailWord_5876556
  simp only [CollatzResearch.WordTrace]
  refine ⟨107167802849124361353188761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142890403798832481804251681 107167802849124361353188761)
  ·
    refine ⟨80375852136843271014891571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107167802849124361353188761 80375852136843271014891571)
    ·
      refine ⟨120563778205264906522337357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80375852136843271014891571 120563778205264906522337357)
      ·
        refine ⟨45211416826974339945876509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120563778205264906522337357 45211416826974339945876509)
        ·
          refine ⟨16954281310115377479703691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45211416826974339945876509 16954281310115377479703691)
          ·
            refine ⟨25431421965173066219555537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16954281310115377479703691 25431421965173066219555537)
            ·
              refine ⟨19073566473879799664666653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25431421965173066219555537 19073566473879799664666653)
              ·
                refine ⟨7152587427704924874249995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19073566473879799664666653 7152587427704924874249995)
                ·
                  refine ⟨10728881141557387311374993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7152587427704924874249995 10728881141557387311374993)
                  ·
                    refine ⟨8046660856168040483531245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10728881141557387311374993 8046660856168040483531245)
                    ·
                      refine ⟨3017497821063015181324217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8046660856168040483531245 3017497821063015181324217)
                      ·
                        rfl

theorem cell23_5876556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_5876556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876556 prefixEnd_5876556 := by exact prefixLift 5876556
  have htrace : WordTrace (prefixWord ++ tailWord_5876556) baseStart_5876556 baseEnd_5876556 := by
    simpa [prefixWord, tailWord_5876556, baseEnd_5876556] using wordTrace_append hprefix tailTrace_5876556
  have hstable : (prefixWord ++ tailWord_5876556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876556).length < 2 ^ (prefixWord ++ tailWord_5876556).sum := by decide
  have hdescent : baseEnd_5876556 < baseStart_5876556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876590 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5876590 : Nat := 118140960795 + 5876590 * 2 ^ 59
def prefixEnd_5876590 : Nat := 4983230072969 + 3 ^ 40 * 5876590 * 2
def baseEnd_5876590 : Nat := 3017515279405268048299061

theorem tailTrace_5876590 : CollatzResearch.WordTrace tailWord_5876590 prefixEnd_5876590 3017515279405268048299061 := by
  unfold tailWord_5876590
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792105722515693314139403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142891230520083697675410149 26792105722515693314139403)
  ·
    refine ⟨40188158583773539971209105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26792105722515693314139403 40188158583773539971209105)
    ·
      refine ⟨30141118937830154978406829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40188158583773539971209105 30141118937830154978406829)
      ·
        refine ⟨11302919601686308116902561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30141118937830154978406829 11302919601686308116902561)
        ·
          refine ⟨8477189701264731087676921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11302919601686308116902561 8477189701264731087676921)
          ·
            refine ⟨6357892275948548315757691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8477189701264731087676921 6357892275948548315757691)
            ·
              refine ⟨9536838413922822473636537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357892275948548315757691 9536838413922822473636537)
              ·
                refine ⟨7152628810442116855227403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9536838413922822473636537 7152628810442116855227403)
                ·
                  refine ⟨10728943215663175282841105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7152628810442116855227403 10728943215663175282841105)
                  ·
                    refine ⟨8046707411747381462130829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10728943215663175282841105 8046707411747381462130829)
                    ·
                      refine ⟨3017515279405268048299061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8046707411747381462130829 3017515279405268048299061)
                      ·
                        rfl

theorem cell23_5876590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5876590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876590 prefixEnd_5876590 := by exact prefixLift 5876590
  have htrace : WordTrace (prefixWord ++ tailWord_5876590) baseStart_5876590 baseEnd_5876590 := by
    simpa [prefixWord, tailWord_5876590, baseEnd_5876590] using wordTrace_append hprefix tailTrace_5876590
  have hstable : (prefixWord ++ tailWord_5876590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876590).length < 2 ^ (prefixWord ++ tailWord_5876590).sum := by decide
  have hdescent : baseEnd_5876590 < baseStart_5876590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876602 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_5876602 : Nat := 118140960795 + 5876602 * 2 ^ 59
def prefixEnd_5876602 : Nat := 4983230072969 + 3 ^ 40 * 5876602 * 2
def baseEnd_5876602 : Nat := 1005840480391040667116335

theorem tailTrace_5876602 : CollatzResearch.WordTrace tailWord_5876602 prefixEnd_5876602 1005840480391040667116335 := by
  unfold tailWord_5876602
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584320864020518140638015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142891522304054715041701373 53584320864020518140638015)
  ·
    refine ⟨80376481296030777210957023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53584320864020518140638015 80376481296030777210957023)
    ·
      refine ⟨120564721944046165816435535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80376481296030777210957023 120564721944046165816435535)
      ·
        refine ⟨180847082916069248724653303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120564721944046165816435535 180847082916069248724653303)
        ·
          refine ⟨271270624374103873086979955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180847082916069248724653303 271270624374103873086979955)
          ·
            refine ⟨406905936561155809630469933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271270624374103873086979955 406905936561155809630469933)
            ·
              refine ⟨152589726210433428611426225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406905936561155809630469933 152589726210433428611426225)
              ·
                refine ⟨114442294657825071458569669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152589726210433428611426225 114442294657825071458569669)
                ·
                  refine ⟨21457930248342200898481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114442294657825071458569669 21457930248342200898481813)
                  ·
                    refine ⟨1005840480391040667116335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21457930248342200898481813 1005840480391040667116335)
                    ·
                      rfl

theorem cell23_5876602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_5876602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876602 prefixEnd_5876602 := by exact prefixLift 5876602
  have htrace : WordTrace (prefixWord ++ tailWord_5876602) baseStart_5876602 baseEnd_5876602 := by
    simpa [prefixWord, tailWord_5876602, baseEnd_5876602] using wordTrace_append hprefix tailTrace_5876602
  have hstable : (prefixWord ++ tailWord_5876602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876602).length < 2 ^ (prefixWord ++ tailWord_5876602).sum := by decide
  have hdescent : baseEnd_5876602 < baseStart_5876602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876629 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_5876629 : Nat := 118140960795 + 5876629 * 2 ^ 59
def prefixEnd_5876629 : Nat := 4983230072969 + 3 ^ 40 * 5876629 * 2
def baseEnd_5876629 : Nat := 3017535305150793395711381

theorem tailTrace_5876629 : CollatzResearch.WordTrace tailWord_5876629 prefixEnd_5876629 3017535305150793395711381 := by
  unfold tailWord_5876629
  simp only [CollatzResearch.WordTrace]
  refine ⟨214338268226984256173784941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142892178817989504115856627 214338268226984256173784941)
  ·
    refine ⟨80376850585119096065169353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214338268226984256173784941 80376850585119096065169353)
    ·
      refine ⟨60282637938839322048877015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80376850585119096065169353 60282637938839322048877015)
      ·
        refine ⟨90423956908258983073315523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60282637938839322048877015 90423956908258983073315523)
        ·
          refine ⟨135635935362388474609973285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90423956908258983073315523 135635935362388474609973285)
          ·
            refine ⟨25431737880447838989369991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135635935362388474609973285 25431737880447838989369991)
            ·
              refine ⟨38147606820671758484054987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25431737880447838989369991 38147606820671758484054987)
              ·
                refine ⟨57221410231007637726082481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38147606820671758484054987 57221410231007637726082481)
                ·
                  refine ⟨42916057673255728294561861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57221410231007637726082481 42916057673255728294561861)
                  ·
                    refine ⟨8046760813735449055230349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42916057673255728294561861 8046760813735449055230349)
                    ·
                      refine ⟨3017535305150793395711381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8046760813735449055230349 3017535305150793395711381)
                      ·
                        rfl

theorem cell23_5876629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_5876629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876629 prefixEnd_5876629 := by exact prefixLift 5876629
  have htrace : WordTrace (prefixWord ++ tailWord_5876629) baseStart_5876629 baseEnd_5876629 := by
    simpa [prefixWord, tailWord_5876629, baseEnd_5876629] using wordTrace_append hprefix tailTrace_5876629
  have hstable : (prefixWord ++ tailWord_5876629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876629).length < 2 ^ (prefixWord ++ tailWord_5876629).sum := by decide
  have hdescent : baseEnd_5876629 < baseStart_5876629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876636 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_5876636 : Nat := 118140960795 + 5876636 * 2 ^ 59
def prefixEnd_5876636 : Nat := 4983230072969 + 3 ^ 40 * 5876636 * 2
def baseEnd_5876636 : Nat := 1005846299838458289441283

theorem tailTrace_5876636 : CollatzResearch.WordTrace tailWord_5876636 prefixEnd_5876636 1005846299838458289441283 := by
  unfold tailWord_5876636
  simp only [CollatzResearch.WordTrace]
  refine ⟨107169261768979448184644881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142892349025305930912859841 107169261768979448184644881)
  ·
    refine ⟨80376946326734586138483661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107169261768979448184644881 80376946326734586138483661)
    ·
      refine ⟨30141354872525469801931373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80376946326734586138483661 30141354872525469801931373)
      ·
        refine ⟨11303008077197051175724265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30141354872525469801931373 11303008077197051175724265)
        ·
          refine ⟨8477256057897788381793199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303008077197051175724265 8477256057897788381793199)
          ·
            refine ⟨12715884086846682572689799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8477256057897788381793199 12715884086846682572689799)
            ·
              refine ⟨19073826130270023859034699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12715884086846682572689799 19073826130270023859034699)
              ·
                refine ⟨28610739195405035788552049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19073826130270023859034699 28610739195405035788552049)
                ·
                  refine ⟨21458054396553776841414037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28610739195405035788552049 21458054396553776841414037)
                  ·
                    refine ⟨1005846299838458289441283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21458054396553776841414037 1005846299838458289441283)
                    ·
                      rfl

theorem cell23_5876636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_5876636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876636 prefixEnd_5876636 := by exact prefixLift 5876636
  have htrace : WordTrace (prefixWord ++ tailWord_5876636) baseStart_5876636 baseEnd_5876636 := by
    simpa [prefixWord, tailWord_5876636, baseEnd_5876636] using wordTrace_append hprefix tailTrace_5876636
  have hstable : (prefixWord ++ tailWord_5876636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876636).length < 2 ^ (prefixWord ++ tailWord_5876636).sum := by decide
  have hdescent : baseEnd_5876636 < baseStart_5876636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876639 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5876639 : Nat := 118140960795 + 5876639 * 2 ^ 59
def prefixEnd_5876639 : Nat := 4983230072969 + 3 ^ 40 * 5876639 * 2
def baseEnd_5876639 : Nat := 3017540439957338356586335

theorem tailTrace_5876639 : CollatzResearch.WordTrace tailWord_5876639 prefixEnd_5876639 3017540439957338356586335 := by
  unfold tailWord_5876639
  simp only [CollatzResearch.WordTrace]
  refine ⟨214338632956948027881648971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142892421971298685254432647 214338632956948027881648971)
  ·
    refine ⟨321507949435422041822473457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214338632956948027881648971 321507949435422041822473457)
    ·
      refine ⟨241130962076566531366855093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321507949435422041822473457 241130962076566531366855093)
      ·
        refine ⟨22606027694678112315642665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241130962076566531366855093 22606027694678112315642665)
        ·
          refine ⟨16954520771008584236731999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22606027694678112315642665 16954520771008584236731999)
          ·
            refine ⟨25431781156512876355097999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16954520771008584236731999 25431781156512876355097999)
            ·
              refine ⟨38147671734769314532646999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25431781156512876355097999 38147671734769314532646999)
              ·
                refine ⟨57221507602153971798970499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38147671734769314532646999 57221507602153971798970499)
                ·
                  refine ⟨85832261403230957698455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57221507602153971798970499 85832261403230957698455749)
                  ·
                    refine ⟨16093549013105804568460453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85832261403230957698455749 16093549013105804568460453)
                    ·
                      refine ⟨3017540439957338356586335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16093549013105804568460453 3017540439957338356586335)
                      ·
                        rfl

theorem cell23_5876639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5876639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876639 prefixEnd_5876639 := by exact prefixLift 5876639
  have htrace : WordTrace (prefixWord ++ tailWord_5876639) baseStart_5876639 baseEnd_5876639 := by
    simpa [prefixWord, tailWord_5876639, baseEnd_5876639] using wordTrace_append hprefix tailTrace_5876639
  have hstable : (prefixWord ++ tailWord_5876639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876639).length < 2 ^ (prefixWord ++ tailWord_5876639).sum := by decide
  have hdescent : baseEnd_5876639 < baseStart_5876639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876643 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 2, 2, 2]
def baseStart_5876643 : Nat := 118140960795 + 5876643 * 2 ^ 59
def prefixEnd_5876643 : Nat := 4983230072969 + 3 ^ 40 * 5876643 * 2
def baseEnd_5876643 : Nat := 3017542493879956340936317

theorem tailTrace_5876643 : CollatzResearch.WordTrace tailWord_5876643 prefixEnd_5876643 3017542493879956340936317 := by
  unfold tailWord_5876643
  simp only [CollatzResearch.WordTrace]
  refine ⟨214338778848933536564794583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142892519232622357709863055 214338778848933536564794583)
  ·
    refine ⟨321508168273400304847191875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214338778848933536564794583 321508168273400304847191875)
    ·
      refine ⟨482262252410100457270787813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321508168273400304847191875 482262252410100457270787813)
      ·
        refine ⟨90424172326893835738272715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 482262252410100457270787813 90424172326893835738272715)
        ·
          refine ⟨135636258490340753607409073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90424172326893835738272715 135636258490340753607409073)
          ·
            refine ⟨101727193867755565205556805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135636258490340753607409073 101727193867755565205556805)
            ·
              refine ⟨19073848850204168476041901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101727193867755565205556805 19073848850204168476041901)
              ·
                refine ⟨7152693318826563178515713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19073848850204168476041901 7152693318826563178515713)
                ·
                  refine ⟨5364519989119922383886785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7152693318826563178515713 5364519989119922383886785)
                  ·
                    refine ⟨4023389991839941787915089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5364519989119922383886785 4023389991839941787915089)
                    ·
                      refine ⟨3017542493879956340936317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023389991839941787915089 3017542493879956340936317)
                      ·
                        rfl

theorem cell23_5876643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_5876643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876643 prefixEnd_5876643 := by exact prefixLift 5876643
  have htrace : WordTrace (prefixWord ++ tailWord_5876643) baseStart_5876643 baseEnd_5876643 := by
    simpa [prefixWord, tailWord_5876643, baseEnd_5876643] using wordTrace_append hprefix tailTrace_5876643
  have hstable : (prefixWord ++ tailWord_5876643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876643).length < 2 ^ (prefixWord ++ tailWord_5876643).sum := by decide
  have hdescent : baseEnd_5876643 < baseStart_5876643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876652 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_5876652 : Nat := 118140960795 + 5876652 * 2 ^ 59
def prefixEnd_5876652 : Nat := 4983230072969 + 3 ^ 40 * 5876652 * 2
def baseEnd_5876652 : Nat := 3017547115205846805723775

theorem tailTrace_5876652 : CollatzResearch.WordTrace tailWord_5876652 prefixEnd_5876652 3017547115205846805723775 := by
  unfold tailWord_5876652
  simp only [CollatzResearch.WordTrace]
  refine ⟨107169553552950465550936105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142892738070600620734581473 107169553552950465550936105)
  ·
    refine ⟨80377165164712849163202079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107169553552950465550936105 80377165164712849163202079)
    ·
      refine ⟨120565747747069273744803119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80377165164712849163202079 120565747747069273744803119)
      ·
        refine ⟨180848621620603910617204679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120565747747069273744803119 180848621620603910617204679)
        ·
          refine ⟨271272932430905865925807019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180848621620603910617204679 271272932430905865925807019)
          ·
            refine ⟨406909398646358798888710529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271272932430905865925807019 406909398646358798888710529)
            ·
              refine ⟨305182048984769099166532897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406909398646358798888710529 305182048984769099166532897)
              ·
                refine ⟨228886536738576824374899673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305182048984769099166532897 228886536738576824374899673)
                ·
                  refine ⟨171664902553932618281174755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228886536738576824374899673 171664902553932618281174755)
                  ·
                    refine ⟨257497353830898927421762133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171664902553932618281174755 257497353830898927421762133)
                    ·
                      refine ⟨3017547115205846805723775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 257497353830898927421762133 3017547115205846805723775)
                      ·
                        rfl

theorem cell23_5876652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_5876652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876652 prefixEnd_5876652 := by exact prefixLift 5876652
  have htrace : WordTrace (prefixWord ++ tailWord_5876652) baseStart_5876652 baseEnd_5876652 := by
    simpa [prefixWord, tailWord_5876652, baseEnd_5876652] using wordTrace_append hprefix tailTrace_5876652
  have hstable : (prefixWord ++ tailWord_5876652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876652).length < 2 ^ (prefixWord ++ tailWord_5876652).sum := by decide
  have hdescent : baseEnd_5876652 < baseStart_5876652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876660 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_5876660 : Nat := 118140960795 + 5876660 * 2 ^ 59
def prefixEnd_5876660 : Nat := 4983230072969 + 3 ^ 40 * 5876660 * 2
def baseEnd_5876660 : Nat := 3017551223051082774423739

theorem tailTrace_5876660 : CollatzResearch.WordTrace tailWord_5876660 prefixEnd_5876660 3017551223051082774423739 := by
  unfold tailWord_5876660
  simp only [CollatzResearch.WordTrace]
  refine ⟨107169699444935974234081717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142892932593247965645442289 107169699444935974234081717)
  ·
    refine ⟨10047159322962747584445161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107169699444935974234081717 10047159322962747584445161)
    ·
      refine ⟨7535369492222060688333871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10047159322962747584445161 7535369492222060688333871)
      ·
        refine ⟨11303054238333091032500807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7535369492222060688333871 11303054238333091032500807)
        ·
          refine ⟨16954581357499636548751211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303054238333091032500807 16954581357499636548751211)
          ·
            refine ⟨25431872036249454823126817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16954581357499636548751211 25431872036249454823126817)
            ·
              refine ⟨19073904027187091117345113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25431872036249454823126817 19073904027187091117345113)
              ·
                refine ⟨14305428020390318338008835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19073904027187091117345113 14305428020390318338008835)
                ·
                  refine ⟨21458142030585477507013253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14305428020390318338008835 21458142030585477507013253)
                  ·
                    refine ⟨4023401630734777032564985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21458142030585477507013253 4023401630734777032564985)
                    ·
                      refine ⟨3017551223051082774423739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023401630734777032564985 3017551223051082774423739)
                      ·
                        rfl

theorem cell23_5876660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_5876660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876660 prefixEnd_5876660 := by exact prefixLift 5876660
  have htrace : WordTrace (prefixWord ++ tailWord_5876660) baseStart_5876660 baseEnd_5876660 := by
    simpa [prefixWord, tailWord_5876660, baseEnd_5876660] using wordTrace_append hprefix tailTrace_5876660
  have hstable : (prefixWord ++ tailWord_5876660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876660).length < 2 ^ (prefixWord ++ tailWord_5876660).sum := by decide
  have hdescent : baseEnd_5876660 < baseStart_5876660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876666 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_5876666 : Nat := 118140960795 + 5876666 * 2 ^ 59
def prefixEnd_5876666 : Nat := 4983230072969 + 3 ^ 40 * 5876666 * 2
def baseEnd_5876666 : Nat := 335283811548334416772079

theorem tailTrace_5876666 : CollatzResearch.WordTrace tailWord_5876666 prefixEnd_5876666 335283811548334416772079 := by
  unfold tailWord_5876666
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584904431962552873220463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142893078485233474328587901 53584904431962552873220463)
  ·
    refine ⟨80377356647943829309830695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53584904431962552873220463 80377356647943829309830695)
    ·
      refine ⟨120566034971915743964746043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80377356647943829309830695 120566034971915743964746043)
      ·
        refine ⟨180849052457873615947119065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120566034971915743964746043 180849052457873615947119065)
        ·
          refine ⟨135636789343405211960339299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180849052457873615947119065 135636789343405211960339299)
          ·
            refine ⟨203455184015107817940508949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135636789343405211960339299 203455184015107817940508949)
            ·
              refine ⟨9536961750708178965961357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 203455184015107817940508949 9536961750708178965961357)
              ·
                refine ⟨3576360656515567112235509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9536961750708178965961357 3576360656515567112235509)
                ·
                  refine ⟨335283811548334416772079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3576360656515567112235509 335283811548334416772079)
                  ·
                    rfl

theorem cell23_5876666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_5876666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876666 prefixEnd_5876666 := by exact prefixLift 5876666
  have htrace : WordTrace (prefixWord ++ tailWord_5876666) baseStart_5876666 baseEnd_5876666 := by
    simpa [prefixWord, tailWord_5876666, baseEnd_5876666] using wordTrace_append hprefix tailTrace_5876666
  have hstable : (prefixWord ++ tailWord_5876666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876666).length < 2 ^ (prefixWord ++ tailWord_5876666).sum := by decide
  have hdescent : baseEnd_5876666 < baseStart_5876666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876679 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 2, 5]
def baseStart_5876679 : Nat := 118140960795 + 5876679 * 2 ^ 59
def prefixEnd_5876679 : Nat := 4983230072969 + 3 ^ 40 * 5876679 * 2
def baseEnd_5876679 : Nat := 1005853659727839400028717

theorem tailTrace_5876679 : CollatzResearch.WordTrace tailWord_5876679 prefixEnd_5876679 1005853659727839400028717 := by
  unfold tailWord_5876679
  simp only [CollatzResearch.WordTrace]
  refine ⟨214340091876803114713105091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142893394584535409808736727 214340091876803114713105091)
  ·
    refine ⟨321510137815204672069657637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214340091876803114713105091 321510137815204672069657637)
    ·
      refine ⟨60283150840350876013060807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321510137815204672069657637 60283150840350876013060807)
      ·
        refine ⟨90424726260526314019591211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60283150840350876013060807 90424726260526314019591211)
        ·
          refine ⟨135637089390789471029386817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90424726260526314019591211 135637089390789471029386817)
          ·
            refine ⟨101727817043092103272040113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135637089390789471029386817 101727817043092103272040113)
            ·
              refine ⟨76295862782319077454030085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101727817043092103272040113 76295862782319077454030085)
              ·
                refine ⟨14305474271684827022630641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76295862782319077454030085 14305474271684827022630641)
                ·
                  refine ⟨10729105703763620266972981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14305474271684827022630641 10729105703763620266972981)
                  ·
                    refine ⟨1005853659727839400028717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10729105703763620266972981 1005853659727839400028717)
                    ·
                      rfl

theorem cell23_5876679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_5876679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876679 prefixEnd_5876679 := by exact prefixLift 5876679
  have htrace : WordTrace (prefixWord ++ tailWord_5876679) baseStart_5876679 baseEnd_5876679 := by
    simpa [prefixWord, tailWord_5876679, baseEnd_5876679] using wordTrace_append hprefix tailTrace_5876679
  have hstable : (prefixWord ++ tailWord_5876679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876679).length < 2 ^ (prefixWord ++ tailWord_5876679).sum := by decide
  have hdescent : baseEnd_5876679 < baseStart_5876679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876694 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_5876694 : Nat := 118140960795 + 5876694 * 2 ^ 59
def prefixEnd_5876694 : Nat := 4983230072969 + 3 ^ 40 * 5876694 * 2
def baseEnd_5876694 : Nat := 3017568681393335641398583

theorem tailTrace_5876694 : CollatzResearch.WordTrace tailWord_5876694 prefixEnd_5876694 3017568681393335641398583 := by
  unfold tailWord_5876694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13396289935734298267181321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142893759314499181516600757 13396289935734298267181321)
  ·
    refine ⟨10047217451800723700385991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13396289935734298267181321 10047217451800723700385991)
    ·
      refine ⟨15070826177701085550578987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10047217451800723700385991 15070826177701085550578987)
      ·
        refine ⟨22606239266551628325868481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15070826177701085550578987 22606239266551628325868481)
        ·
          refine ⟨16954679449913721244401361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22606239266551628325868481 16954679449913721244401361)
          ·
            refine ⟨12716009587435290933301021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16954679449913721244401361 12716009587435290933301021)
            ·
              refine ⟨4768503595288234099987883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12716009587435290933301021 4768503595288234099987883)
              ·
                refine ⟨7152755392932351149981825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768503595288234099987883 7152755392932351149981825)
                ·
                  refine ⟨5364566544699263362486369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7152755392932351149981825 5364566544699263362486369)
                  ·
                    refine ⟨4023424908524447521864777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5364566544699263362486369 4023424908524447521864777)
                    ·
                      refine ⟨3017568681393335641398583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023424908524447521864777 3017568681393335641398583)
                      ·
                        rfl

theorem cell23_5876694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_5876694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876694 prefixEnd_5876694 := by exact prefixLift 5876694
  have htrace : WordTrace (prefixWord ++ tailWord_5876694) baseStart_5876694 baseEnd_5876694 := by
    simpa [prefixWord, tailWord_5876694, baseEnd_5876694] using wordTrace_append hprefix tailTrace_5876694
  have hstable : (prefixWord ++ tailWord_5876694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876694).length < 2 ^ (prefixWord ++ tailWord_5876694).sum := by decide
  have hdescent : baseEnd_5876694 < baseStart_5876694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876799 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 5, 6]
def baseStart_5876799 : Nat := 118140960795 + 5876799 * 2 ^ 59
def prefixEnd_5876799 : Nat := 4983230072969 + 3 ^ 40 * 5876799 * 2
def baseEnd_5876799 : Nat := 1005874198954019243528533

theorem tailTrace_5876799 : CollatzResearch.WordTrace tailWord_5876799 prefixEnd_5876799 1005874198954019243528533 := by
  unfold tailWord_5876799
  simp only [CollatzResearch.WordTrace]
  refine ⟨214344468636368375207473451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142896312424245583471648967 214344468636368375207473451)
  ·
    refine ⟨321516702954552562811210177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214344468636368375207473451 321516702954552562811210177)
    ·
      refine ⟨241137527215914422108407633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321516702954552562811210177 241137527215914422108407633)
      ·
        refine ⟨180853145411935816581305725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241137527215914422108407633 180853145411935816581305725)
        ·
          refine ⟨67819929529475931217989647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180853145411935816581305725 67819929529475931217989647)
          ·
            refine ⟨101729894294213896826984471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67819929529475931217989647 101729894294213896826984471)
            ·
              refine ⟨152594841441320845240476707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101729894294213896826984471 152594841441320845240476707)
              ·
                refine ⟨228892262161981267860715061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152594841441320845240476707 228892262161981267860715061)
                ·
                  refine ⟨21458649577685743861942037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228892262161981267860715061 21458649577685743861942037)
                  ·
                    refine ⟨1005874198954019243528533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21458649577685743861942037 1005874198954019243528533)
                    ·
                      rfl

theorem cell23_5876799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_5876799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876799 prefixEnd_5876799 := by exact prefixLift 5876799
  have htrace : WordTrace (prefixWord ++ tailWord_5876799) baseStart_5876799 baseEnd_5876799 := by
    simpa [prefixWord, tailWord_5876799, baseEnd_5876799] using wordTrace_append hprefix tailTrace_5876799
  have hstable : (prefixWord ++ tailWord_5876799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876799).length < 2 ^ (prefixWord ++ tailWord_5876799).sum := by decide
  have hdescent : baseEnd_5876799 < baseStart_5876799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876800 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 1, 1, 3]
def baseStart_5876800 : Nat := 118140960795 + 5876800 * 2 ^ 59
def prefixEnd_5876800 : Nat := 4983230072969 + 3 ^ 40 * 5876800 * 2
def baseEnd_5876800 : Nat := 3017623110342712226673095

theorem tailTrace_5876800 : CollatzResearch.WordTrace tailWord_5876800 prefixEnd_5876800 3017623110342712226673095 := by
  unfold tailWord_5876800
  simp only [CollatzResearch.WordTrace]
  refine ⟨107172252554682376189129927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142896336739576501585506569 107172252554682376189129927)
  ·
    refine ⟨160758378832023564283694891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107172252554682376189129927 160758378832023564283694891)
    ·
      refine ⟨241137568248035346425542337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160758378832023564283694891 241137568248035346425542337)
      ·
        refine ⟨180853176186026509819156753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241137568248035346425542337 180853176186026509819156753)
        ·
          refine ⟨135639882139519882364367565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180853176186026509819156753 135639882139519882364367565)
          ·
            refine ⟨50864955802319955886637837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135639882139519882364367565 50864955802319955886637837)
            ·
              refine ⟨19074358425869983457489189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50864955802319955886637837 19074358425869983457489189)
              ·
                refine ⟨3576442204850621898279223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19074358425869983457489189 3576442204850621898279223)
                ·
                  refine ⟨5364663307275932847418835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576442204850621898279223 5364663307275932847418835)
                  ·
                    refine ⟨8046994960913899271128253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5364663307275932847418835 8046994960913899271128253)
                    ·
                      refine ⟨3017623110342712226673095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8046994960913899271128253 3017623110342712226673095)
                      ·
                        rfl

theorem cell23_5876800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_5876800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876800 prefixEnd_5876800 := by exact prefixLift 5876800
  have htrace : WordTrace (prefixWord ++ tailWord_5876800) baseStart_5876800 baseEnd_5876800 := by
    simpa [prefixWord, tailWord_5876800, baseEnd_5876800] using wordTrace_append hprefix tailTrace_5876800
  have hstable : (prefixWord ++ tailWord_5876800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876800).length < 2 ^ (prefixWord ++ tailWord_5876800).sum := by decide
  have hdescent : baseEnd_5876800 < baseStart_5876800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876834 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5876834 : Nat := 118140960795 + 5876834 * 2 ^ 59
def prefixEnd_5876834 : Nat := 4983230072969 + 3 ^ 40 * 5876834 * 2
def baseEnd_5876834 : Nat := 3017640568684965093647939

theorem tailTrace_5876834 : CollatzResearch.WordTrace tailWord_5876834 prefixEnd_5876834 3017640568684965093647939 := by
  unfold tailWord_5876834
  simp only [CollatzResearch.WordTrace]
  refine ⟨53586436297810394046249389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142897163460827717456665037 53586436297810394046249389)
  ·
    refine ⟨20094913611678897767343521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53586436297810394046249389 20094913611678897767343521)
    ·
      refine ⟨15071185208759173325507641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20094913611678897767343521 15071185208759173325507641)
      ·
        refine ⟨11303388906569379994130731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15071185208759173325507641 11303388906569379994130731)
        ·
          refine ⟨16955083359854069991196097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303388906569379994130731 16955083359854069991196097)
          ·
            refine ⟨12716312519890552493397073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16955083359854069991196097 12716312519890552493397073)
            ·
              refine ⟨9537234389917914370047805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12716312519890552493397073 9537234389917914370047805)
              ·
                refine ⟨3576462896219217888767927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9537234389917914370047805 3576462896219217888767927)
                ·
                  refine ⟨5364694344328826833151891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576462896219217888767927 5364694344328826833151891)
                  ·
                    refine ⟨8047041516493240249727837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5364694344328826833151891 8047041516493240249727837)
                    ·
                      refine ⟨3017640568684965093647939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047041516493240249727837 3017640568684965093647939)
                      ·
                        rfl

theorem cell23_5876834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5876834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876834 prefixEnd_5876834 := by exact prefixLift 5876834
  have htrace : WordTrace (prefixWord ++ tailWord_5876834) baseStart_5876834 baseEnd_5876834 := by
    simpa [prefixWord, tailWord_5876834, baseEnd_5876834] using wordTrace_append hprefix tailTrace_5876834
  have hstable : (prefixWord ++ tailWord_5876834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876834).length < 2 ^ (prefixWord ++ tailWord_5876834).sum := by decide
  have hdescent : baseEnd_5876834 < baseStart_5876834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876846 : List Nat := [4, 1, 2, 2, 1, 3, 10]
def baseStart_5876846 : Nat := 118140960795 + 5876846 * 2 ^ 59
def prefixEnd_5876846 : Nat := 4983230072969 + 3 ^ 40 * 5876846 * 2
def baseEnd_5876846 : Nat := 37254897906824926502443

theorem tailTrace_5876846 : CollatzResearch.WordTrace tailWord_5876846 prefixEnd_5876846 37254897906824926502443 := by
  unfold tailWord_5876846
  simp only [CollatzResearch.WordTrace]
  refine ⟨26793272858399762779304299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142897455244798734822956261 26793272858399762779304299)
  ·
    refine ⟨40189909287599644168956449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26793272858399762779304299 40189909287599644168956449)
    ·
      refine ⟨30142431965699733126717337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40189909287599644168956449 30142431965699733126717337)
      ·
        refine ⟨22606823974274799845038003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30142431965699733126717337 22606823974274799845038003)
        ·
          refine ⟨33910235961412199767557005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22606823974274799845038003 33910235961412199767557005)
          ·
            refine ⟨12716338485529574912833877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33910235961412199767557005 12716338485529574912833877)
            ·
              refine ⟨37254897906824926502443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12716338485529574912833877 37254897906824926502443)
              ·
                rfl

theorem cell23_5876846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 10].length) (baseStart_5876846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876846 prefixEnd_5876846 := by exact prefixLift 5876846
  have htrace : WordTrace (prefixWord ++ tailWord_5876846) baseStart_5876846 baseEnd_5876846 := by
    simpa [prefixWord, tailWord_5876846, baseEnd_5876846] using wordTrace_append hprefix tailTrace_5876846
  have hstable : (prefixWord ++ tailWord_5876846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876846).length < 2 ^ (prefixWord ++ tailWord_5876846).sum := by decide
  have hdescent : baseEnd_5876846 < baseStart_5876846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876856 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_5876856 : Nat := 118140960795 + 5876856 * 2 ^ 59
def prefixEnd_5876856 : Nat := 4983230072969 + 3 ^ 40 * 5876856 * 2
def baseEnd_5876856 : Nat := 3017651865259364007572837

theorem tailTrace_5876856 : CollatzResearch.WordTrace tailWord_5876856 prefixEnd_5876856 3017651865259364007572837 := by
  unfold tailWord_5876856
  simp only [CollatzResearch.WordTrace]
  refine ⟨107173273798580936971149211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142897698398107915961532281 107173273798580936971149211)
  ·
    refine ⟨160759910697871405456723817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107173273798580936971149211 160759910697871405456723817)
    ·
      refine ⟨120569933023403554092542863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160759910697871405456723817 120569933023403554092542863)
      ·
        refine ⟨180854899535105331138814295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120569933023403554092542863 180854899535105331138814295)
        ·
          refine ⟨271282349302657996708221443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180854899535105331138814295 271282349302657996708221443)
          ·
            refine ⟨406923523953986995062332165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271282349302657996708221443 406923523953986995062332165)
            ·
              refine ⟨76298160741372561574187281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406923523953986995062332165 76298160741372561574187281)
              ·
                refine ⟨57223620556029421180640461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76298160741372561574187281 57223620556029421180640461)
                ·
                  refine ⟨21458857708511032942740173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57223620556029421180640461 21458857708511032942740173)
                  ·
                    refine ⟨8047071640691637353527565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21458857708511032942740173 8047071640691637353527565)
                    ·
                      refine ⟨3017651865259364007572837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047071640691637353527565 3017651865259364007572837)
                      ·
                        rfl

theorem cell23_5876856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_5876856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876856 prefixEnd_5876856 := by exact prefixLift 5876856
  have htrace : WordTrace (prefixWord ++ tailWord_5876856) baseStart_5876856 baseEnd_5876856 := by
    simpa [prefixWord, tailWord_5876856, baseEnd_5876856] using wordTrace_append hprefix tailTrace_5876856
  have hstable : (prefixWord ++ tailWord_5876856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876856).length < 2 ^ (prefixWord ++ tailWord_5876856).sum := by decide
  have hdescent : baseEnd_5876856 < baseStart_5876856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876857 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 3, 2, 2]
def baseStart_5876857 : Nat := 118140960795 + 5876857 * 2 ^ 59
def prefixEnd_5876857 : Nat := 4983230072969 + 3 ^ 40 * 5876857 * 2
def baseEnd_5876857 : Nat := 3017652378740018503660333

theorem tailTrace_5876857 : CollatzResearch.WordTrace tailWord_5876857 prefixEnd_5876857 3017652378740018503660333 := by
  unfold tailWord_5876857
  simp only [CollatzResearch.WordTrace]
  refine ⟨214346584070158251113084825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142897722713438834075389883 214346584070158251113084825)
  ·
    refine ⟨160759938052618688334813619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214346584070158251113084825 160759938052618688334813619)
    ·
      refine ⟨241139907078928032502220429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160759938052618688334813619 241139907078928032502220429)
      ·
        refine ⟨90427465154598012188332661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241139907078928032502220429 90427465154598012188332661)
        ·
          refine ⟨8477574858243563642656187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90427465154598012188332661 8477574858243563642656187)
          ·
            refine ⟨12716362287365345463984281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8477574858243563642656187 12716362287365345463984281)
            ·
              refine ⟨9537271715524009097988211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12716362287365345463984281 9537271715524009097988211)
              ·
                refine ⟨14305907573286013646982317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9537271715524009097988211 14305907573286013646982317)
                ·
                  refine ⟨5364715339982255117618369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14305907573286013646982317 5364715339982255117618369)
                  ·
                    refine ⟨4023536504986691338213777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5364715339982255117618369 4023536504986691338213777)
                    ·
                      refine ⟨3017652378740018503660333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023536504986691338213777 3017652378740018503660333)
                      ·
                        rfl

theorem cell23_5876857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_5876857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876857 prefixEnd_5876857 := by exact prefixLift 5876857
  have htrace : WordTrace (prefixWord ++ tailWord_5876857) baseStart_5876857 baseEnd_5876857 := by
    simpa [prefixWord, tailWord_5876857, baseEnd_5876857] using wordTrace_append hprefix tailTrace_5876857
  have hstable : (prefixWord ++ tailWord_5876857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876857).length < 2 ^ (prefixWord ++ tailWord_5876857).sum := by decide
  have hdescent : baseEnd_5876857 < baseStart_5876857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876859 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 9]
def baseStart_5876859 : Nat := 118140960795 + 5876859 * 2 ^ 59
def prefixEnd_5876859 : Nat := 4983230072969 + 3 ^ 40 * 5876859 * 2
def baseEnd_5876859 : Nat := 1005884468567109165278441

theorem tailTrace_5876859 : CollatzResearch.WordTrace tailWord_5876859 prefixEnd_5876859 1005884468567109165278441 := by
  unfold tailWord_5876859
  simp only [CollatzResearch.WordTrace]
  refine ⟨214346657016151005454657631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142897771344100670303105087 214346657016151005454657631)
  ·
    refine ⟨321519985524226508181986447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214346657016151005454657631 321519985524226508181986447)
    ·
      refine ⟨482279978286339762272979671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321519985524226508181986447 482279978286339762272979671)
      ·
        refine ⟨723419967429509643409469507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482279978286339762272979671 723419967429509643409469507)
        ·
          refine ⟨1085129951144264465114204261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723419967429509643409469507 1085129951144264465114204261)
          ·
            refine ⟨203461865839549587208913299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1085129951144264465114204261 203461865839549587208913299)
            ·
              refine ⟨305192798759324380813369949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203461865839549587208913299 305192798759324380813369949)
              ·
                refine ⟨114447299534746642805013731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305192798759324380813369949 114447299534746642805013731)
                ·
                  refine ⟨171670949302119964207520597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114447299534746642805013731 171670949302119964207520597)
                  ·
                    refine ⟨1005884468567109165278441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171670949302119964207520597 1005884468567109165278441)
                    ·
                      rfl

theorem cell23_5876859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_5876859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876859 prefixEnd_5876859 := by exact prefixLift 5876859
  have htrace : WordTrace (prefixWord ++ tailWord_5876859) baseStart_5876859 baseEnd_5876859 := by
    simpa [prefixWord, tailWord_5876859, baseEnd_5876859] using wordTrace_append hprefix tailTrace_5876859
  have hstable : (prefixWord ++ tailWord_5876859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876859).length < 2 ^ (prefixWord ++ tailWord_5876859).sum := by decide
  have hdescent : baseEnd_5876859 < baseStart_5876859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876873 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 3]
def baseStart_5876873 : Nat := 118140960795 + 5876873 * 2 ^ 59
def prefixEnd_5876873 : Nat := 4983230072969 + 3 ^ 40 * 5876873 * 2
def baseEnd_5876873 : Nat := 3017660594430490441060259

theorem tailTrace_5876873 : CollatzResearch.WordTrace tailWord_5876873 prefixEnd_5876873 3017660594430490441060259 := by
  unfold tailWord_5876873
  simp only [CollatzResearch.WordTrace]
  refine ⟨214347167638100285845667273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142898111758733523897111515 214347167638100285845667273)
  ·
    refine ⟨160760375728575214384250455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214347167638100285845667273 160760375728575214384250455)
    ·
      refine ⟨241140563592862821576375683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160760375728575214384250455 241140563592862821576375683)
      ·
        refine ⟨361710845389294232364563525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241140563592862821576375683 361710845389294232364563525)
        ·
          refine ⟨67820783510492668568355661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 361710845389294232364563525 67820783510492668568355661)
          ·
            refine ⟨25432793816434750713133373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67820783510492668568355661 25432793816434750713133373)
            ·
              refine ⟨9537297681163031517425015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25432793816434750713133373 9537297681163031517425015)
              ·
                refine ⟨14305946521744547276137523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9537297681163031517425015 14305946521744547276137523)
                ·
                  refine ⟨21458919782616820914206285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14305946521744547276137523 21458919782616820914206285)
                  ·
                    refine ⟨8047094918481307842827357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21458919782616820914206285 8047094918481307842827357)
                    ·
                      refine ⟨3017660594430490441060259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047094918481307842827357 3017660594430490441060259)
                      ·
                        rfl

theorem cell23_5876873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 3].length) (baseStart_5876873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876873 prefixEnd_5876873 := by exact prefixLift 5876873
  have htrace : WordTrace (prefixWord ++ tailWord_5876873) baseStart_5876873 baseEnd_5876873 := by
    simpa [prefixWord, tailWord_5876873, baseEnd_5876873] using wordTrace_append hprefix tailTrace_5876873
  have hstable : (prefixWord ++ tailWord_5876873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876873).length < 2 ^ (prefixWord ++ tailWord_5876873).sum := by decide
  have hdescent : baseEnd_5876873 < baseStart_5876873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876883 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 3, 3, 2]
def baseStart_5876883 : Nat := 118140960795 + 5876883 * 2 ^ 59
def prefixEnd_5876883 : Nat := 4983230072969 + 3 ^ 40 * 5876883 * 2
def baseEnd_5876883 : Nat := 3017665729237035401935213

theorem tailTrace_5876883 : CollatzResearch.WordTrace tailWord_5876883 prefixEnd_5876883 3017665729237035401935213 := by
  unfold tailWord_5876883
  simp only [CollatzResearch.WordTrace]
  refine ⟨214347532368064057553531303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142898354912042705035687535 214347532368064057553531303)
  ·
    refine ⟨321521298552096086330296955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214347532368064057553531303 321521298552096086330296955)
    ·
      refine ⟨482281947828144129495445433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321521298552096086330296955 482281947828144129495445433)
      ·
        refine ⟨361711460871108097121584075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482281947828144129495445433 361711460871108097121584075)
        ·
          refine ⟨542567191306662145682376113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361711460871108097121584075 542567191306662145682376113)
          ·
            refine ⟨406925393479996609261782085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542567191306662145682376113 406925393479996609261782085)
            ·
              refine ⟨76298511277499364236584141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406925393479996609261782085 76298511277499364236584141)
              ·
                refine ⟨28611941729062261588719053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76298511277499364236584141 28611941729062261588719053)
                ·
                  refine ⟨10729478148398348095769645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28611941729062261588719053 10729478148398348095769645)
                  ·
                    refine ⟨4023554305649380535913617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10729478148398348095769645 4023554305649380535913617)
                    ·
                      refine ⟨3017665729237035401935213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023554305649380535913617 3017665729237035401935213)
                      ·
                        rfl

theorem cell23_5876883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3, 2].length) (baseStart_5876883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876883 prefixEnd_5876883 := by exact prefixLift 5876883
  have htrace : WordTrace (prefixWord ++ tailWord_5876883) baseStart_5876883 baseEnd_5876883 := by
    simpa [prefixWord, tailWord_5876883, baseEnd_5876883] using wordTrace_append hprefix tailTrace_5876883
  have hstable : (prefixWord ++ tailWord_5876883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876883).length < 2 ^ (prefixWord ++ tailWord_5876883).sum := by decide
  have hdescent : baseEnd_5876883 < baseStart_5876883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876890 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5876890 : Nat := 118140960795 + 5876890 * 2 ^ 59
def prefixEnd_5876890 : Nat := 4983230072969 + 3 ^ 40 * 5876890 * 2
def baseEnd_5876890 : Nat := 3017669323601616874547681

theorem tailTrace_5876890 : CollatzResearch.WordTrace tailWord_5876890 prefixEnd_5876890 3017669323601616874547681 := by
  unfold tailWord_5876890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53586946919759674437259031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142898525119359131832690749 53586946919759674437259031)
  ·
    refine ⟨80380420379639511655888547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53586946919759674437259031 80380420379639511655888547)
    ·
      refine ⟨120570630569459267483832821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80380420379639511655888547 120570630569459267483832821)
      ·
        refine ⟨11303496615886806326609327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120570630569459267483832821 11303496615886806326609327)
        ·
          refine ⟨16955244923830209489913991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303496615886806326609327 16955244923830209489913991)
          ·
            refine ⟨25432867385745314234870987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16955244923830209489913991 25432867385745314234870987)
            ·
              refine ⟨38149301078617971352306481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25432867385745314234870987 38149301078617971352306481)
              ·
                refine ⟨28611975808963478514229861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38149301078617971352306481 28611975808963478514229861)
                ·
                  refine ⟨5364745464180652221418099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28611975808963478514229861 5364745464180652221418099)
                  ·
                    refine ⟨8047118196270978332127149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5364745464180652221418099 8047118196270978332127149)
                    ·
                      refine ⟨3017669323601616874547681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047118196270978332127149 3017669323601616874547681)
                      ·
                        rfl

theorem cell23_5876890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5876890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876890 prefixEnd_5876890 := by exact prefixLift 5876890
  have htrace : WordTrace (prefixWord ++ tailWord_5876890) baseStart_5876890 baseEnd_5876890 := by
    simpa [prefixWord, tailWord_5876890, baseEnd_5876890] using wordTrace_append hprefix tailTrace_5876890
  have hstable : (prefixWord ++ tailWord_5876890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876890).length < 2 ^ (prefixWord ++ tailWord_5876890).sum := by decide
  have hdescent : baseEnd_5876890 < baseStart_5876890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876918 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5876918 : Nat := 118140960795 + 5876918 * 2 ^ 59
def prefixEnd_5876918 : Nat := 4983230072969 + 3 ^ 40 * 5876918 * 2
def baseEnd_5876918 : Nat := 1005894567019980921665851

theorem tailTrace_5876918 : CollatzResearch.WordTrace tailWord_5876918 prefixEnd_5876918 1005894567019980921665851 := by
  unfold tailWord_5876918
  simp only [CollatzResearch.WordTrace]
  refine ⟨13396800557683578658190963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142899205948624839020703605 13396800557683578658190963)
  ·
    refine ⟨20095200836525367987286445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13396800557683578658190963 20095200836525367987286445)
    ·
      refine ⟨7535700313697012995232417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20095200836525367987286445 7535700313697012995232417)
      ·
        refine ⟨5651775235272759746424313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7535700313697012995232417 5651775235272759746424313)
        ·
          refine ⟨4238831426454569809818235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5651775235272759746424313 4238831426454569809818235)
          ·
            refine ⟨6358247139681854714727353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238831426454569809818235 6358247139681854714727353)
            ·
              refine ⟨4768685354761391036045515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6358247139681854714727353 4768685354761391036045515)
              ·
                refine ⟨7153028032142086554068273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768685354761391036045515 7153028032142086554068273)
                ·
                  refine ⟨5364771024106564915551205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7153028032142086554068273 5364771024106564915551205)
                  ·
                    refine ⟨1005894567019980921665851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364771024106564915551205 1005894567019980921665851)
                    ·
                      rfl

theorem cell23_5876918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5876918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876918 prefixEnd_5876918 := by exact prefixLift 5876918
  have htrace : WordTrace (prefixWord ++ tailWord_5876918) baseStart_5876918 baseEnd_5876918 := by
    simpa [prefixWord, tailWord_5876918, baseEnd_5876918] using wordTrace_append hprefix tailTrace_5876918
  have hstable : (prefixWord ++ tailWord_5876918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876918).length < 2 ^ (prefixWord ++ tailWord_5876918).sum := by decide
  have hdescent : baseEnd_5876918 < baseStart_5876918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876924 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5876924 : Nat := 118140960795 + 5876924 * 2 ^ 59
def prefixEnd_5876924 : Nat := 4983230072969 + 3 ^ 40 * 5876924 * 2
def baseEnd_5876924 : Nat := 3017686781943869741522525

theorem tailTrace_5876924 : CollatzResearch.WordTrace tailWord_5876924 prefixEnd_5876924 3017686781943869741522525 := by
  unfold tailWord_5876924
  simp only [CollatzResearch.WordTrace]
  refine ⟨107174513880457760777886913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142899351840610347703849217 107174513880457760777886913)
  ·
    refine ⟨80380885410343320583415185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107174513880457760777886913 80380885410343320583415185)
    ·
      refine ⟨60285664057757490437561389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80380885410343320583415185 60285664057757490437561389)
      ·
        refine ⟨22607124021659058914085521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60285664057757490437561389 22607124021659058914085521)
        ·
          refine ⟨16955343016244294185564141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22607124021659058914085521 16955343016244294185564141)
          ·
            refine ⟨6358253631091610319586553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16955343016244294185564141 6358253631091610319586553)
            ·
              refine ⟨4768690223318707739689915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6358253631091610319586553 4768690223318707739689915)
              ·
                refine ⟨7153035334978061609534873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768690223318707739689915 7153035334978061609534873)
                ·
                  refine ⟨5364776501233546207151155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7153035334978061609534873 5364776501233546207151155)
                  ·
                    refine ⟨8047164751850319310726733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5364776501233546207151155 8047164751850319310726733)
                    ·
                      refine ⟨3017686781943869741522525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047164751850319310726733 3017686781943869741522525)
                      ·
                        rfl

theorem cell23_5876924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5876924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876924 prefixEnd_5876924 := by exact prefixLift 5876924
  have htrace : WordTrace (prefixWord ++ tailWord_5876924) baseStart_5876924 baseEnd_5876924 := by
    simpa [prefixWord, tailWord_5876924, baseEnd_5876924] using wordTrace_append hprefix tailTrace_5876924
  have hstable : (prefixWord ++ tailWord_5876924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876924).length < 2 ^ (prefixWord ++ tailWord_5876924).sum := by decide
  have hdescent : baseEnd_5876924 < baseStart_5876924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876936 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 7]
def baseStart_5876936 : Nat := 118140960795 + 5876936 * 2 ^ 59
def prefixEnd_5876936 : Nat := 4983230072969 + 3 ^ 40 * 5876936 * 2
def baseEnd_5876936 : Nat := 335299215967969299396941

theorem tailTrace_5876936 : CollatzResearch.WordTrace tailWord_5876936 prefixEnd_5876936 335299215967969299396941 := by
  unfold tailWord_5876936
  simp only [CollatzResearch.WordTrace]
  refine ⟨107174732718436023802605331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142899643624581365070140441 107174732718436023802605331)
  ·
    refine ⟨160762099077654035703907997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107174732718436023802605331 160762099077654035703907997)
    ·
      refine ⟨60285787154120263388965499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160762099077654035703907997 60285787154120263388965499)
      ·
        refine ⟨90428680731180395083448249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60285787154120263388965499 90428680731180395083448249)
        ·
          refine ⟨67821510548385296312586187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90428680731180395083448249 67821510548385296312586187)
          ·
            refine ⟨101732265822577944468879281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67821510548385296312586187 101732265822577944468879281)
            ·
              refine ⟨76299199366933458351659461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101732265822577944468879281 76299199366933458351659461)
              ·
                refine ⟨14306099881300023440936149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76299199366933458351659461 14306099881300023440936149)
                ·
                  refine ⟨335299215967969299396941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14306099881300023440936149 335299215967969299396941)
                  ·
                    rfl

theorem cell23_5876936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 7].length) (baseStart_5876936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876936 prefixEnd_5876936 := by exact prefixLift 5876936
  have htrace : WordTrace (prefixWord ++ tailWord_5876936) baseStart_5876936 baseEnd_5876936 := by
    simpa [prefixWord, tailWord_5876936, baseEnd_5876936] using wordTrace_append hprefix tailTrace_5876936
  have hstable : (prefixWord ++ tailWord_5876936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876936).length < 2 ^ (prefixWord ++ tailWord_5876936).sum := by decide
  have hdescent : baseEnd_5876936 < baseStart_5876936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876953 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 5]
def baseStart_5876953 : Nat := 118140960795 + 5876953 * 2 ^ 59
def prefixEnd_5876953 : Nat := 4983230072969 + 3 ^ 40 * 5876953 * 2
def baseEnd_5876953 : Nat := 335300185875872236451099

theorem tailTrace_5876953 : CollatzResearch.WordTrace tailWord_5876953 prefixEnd_5876953 335300185875872236451099 := by
  unfold tailWord_5876953
  simp only [CollatzResearch.WordTrace]
  refine ⟨214350085477810459508579513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142900056985206973005719675 214350085477810459508579513)
  ·
    refine ⟨160762564108357844631434635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214350085477810459508579513 160762564108357844631434635)
    ·
      refine ⟨241143846162536766947151953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160762564108357844631434635 241143846162536766947151953)
      ·
        refine ⟨180857884621902575210363965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241143846162536766947151953 180857884621902575210363965)
        ·
          refine ⟨67821706733213465703886487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180857884621902575210363965 67821706733213465703886487)
          ·
            refine ⟨101732560099820198555829731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67821706733213465703886487 101732560099820198555829731)
            ·
              refine ⟨152598840149730297833744597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101732560099820198555829731 152598840149730297833744597)
              ·
                refine ⟨3576535316009303855478389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152598840149730297833744597 3576535316009303855478389)
                ·
                  refine ⟨335300185875872236451099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3576535316009303855478389 335300185875872236451099)
                  ·
                    rfl

theorem cell23_5876953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 5].length) (baseStart_5876953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876953 prefixEnd_5876953 := by exact prefixLift 5876953
  have htrace : WordTrace (prefixWord ++ tailWord_5876953) baseStart_5876953 baseEnd_5876953 := by
    simpa [prefixWord, tailWord_5876953, baseEnd_5876953] using wordTrace_append hprefix tailTrace_5876953
  have hstable : (prefixWord ++ tailWord_5876953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876953).length < 2 ^ (prefixWord ++ tailWord_5876953).sum := by decide
  have hdescent : baseEnd_5876953 < baseStart_5876953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5876970 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_5876970 : Nat := 118140960795 + 5876970 * 2 ^ 59
def prefixEnd_5876970 : Nat := 4983230072969 + 3 ^ 40 * 5876970 * 2
def baseEnd_5876970 : Nat := 335301155783775173505257

theorem tailTrace_5876970 : CollatzResearch.WordTrace tailWord_5876970 prefixEnd_5876970 335301155783775173505257 := by
  unfold tailWord_5876970
  simp only [CollatzResearch.WordTrace]
  refine ⟨53587676379687217852987091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142900470345832580941298909 53587676379687217852987091)
  ·
    refine ⟨80381514569530826779480637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53587676379687217852987091 80381514569530826779480637)
    ·
      refine ⟨30143067963574060042305239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80381514569530826779480637 30143067963574060042305239)
      ·
        refine ⟨45214601945361090063457859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30143067963574060042305239 45214601945361090063457859)
        ·
          refine ⟨67821902918041635095186789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45214601945361090063457859 67821902918041635095186789)
          ·
            refine ⟨12716606797132806580347523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67821902918041635095186789 12716606797132806580347523)
            ·
              refine ⟨19074910195699209870521285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12716606797132806580347523 19074910195699209870521285)
              ·
                refine ⟨3576545661693601850722741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19074910195699209870521285 3576545661693601850722741)
                ·
                  refine ⟨335301155783775173505257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3576545661693601850722741 335301155783775173505257)
                  ·
                    rfl

theorem cell23_5876970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_5876970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5876970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5876970 prefixEnd_5876970 := by exact prefixLift 5876970
  have htrace : WordTrace (prefixWord ++ tailWord_5876970) baseStart_5876970 baseEnd_5876970 := by
    simpa [prefixWord, tailWord_5876970, baseEnd_5876970] using wordTrace_append hprefix tailTrace_5876970
  have hstable : (prefixWord ++ tailWord_5876970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5876970).length < 2 ^ (prefixWord ++ tailWord_5876970).sum := by decide
  have hdescent : baseEnd_5876970 < baseStart_5876970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5876970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877003 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4]
def baseStart_5877003 : Nat := 118140960795 + 5877003 * 2 ^ 59
def prefixEnd_5877003 : Nat := 4983230072969 + 3 ^ 40 * 5877003 * 2
def baseEnd_5877003 : Nat := 3017727346915574932434661

theorem tailTrace_5877003 : CollatzResearch.WordTrace tailWord_5877003 prefixEnd_5877003 3017727346915574932434661 := by
  unfold tailWord_5877003
  simp only [CollatzResearch.WordTrace]
  refine ⟨214351909127629318047899663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142901272751752878698599775 214351909127629318047899663)
  ·
    refine ⟨321527863691443977071849495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214351909127629318047899663 321527863691443977071849495)
    ·
      refine ⟨482291795537165965607774243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321527863691443977071849495 482291795537165965607774243)
      ·
        refine ⟨723437693305748948411661365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482291795537165965607774243 723437693305748948411661365)
        ·
          refine ⟨67822283747413963913593253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 723437693305748948411661365 67822283747413963913593253)
          ·
            refine ⟨12716678202640118233798735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67822283747413963913593253 12716678202640118233798735)
            ·
              refine ⟨19075017303960177350698103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12716678202640118233798735 19075017303960177350698103)
              ·
                refine ⟨28612525955940266026047155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19075017303960177350698103 28612525955940266026047155)
                ·
                  refine ⟨42918788933910399039070733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28612525955940266026047155 42918788933910399039070733)
                  ·
                    refine ⟨16094545850216399639651525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42918788933910399039070733 16094545850216399639651525)
                    ·
                      refine ⟨3017727346915574932434661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16094545850216399639651525 3017727346915574932434661)
                      ·
                        rfl

theorem cell23_5877003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].length) (baseStart_5877003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877003 prefixEnd_5877003 := by exact prefixLift 5877003
  have htrace : WordTrace (prefixWord ++ tailWord_5877003) baseStart_5877003 baseEnd_5877003 := by
    simpa [prefixWord, tailWord_5877003, baseEnd_5877003] using wordTrace_append hprefix tailTrace_5877003
  have hstable : (prefixWord ++ tailWord_5877003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877003).length < 2 ^ (prefixWord ++ tailWord_5877003).sum := by decide
  have hdescent : baseEnd_5877003 < baseStart_5877003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877013 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_5877013 : Nat := 118140960795 + 5877013 * 2 ^ 59
def prefixEnd_5877013 : Nat := 4983230072969 + 3 ^ 40 * 5877013 * 2
def baseEnd_5877013 : Nat := 1005910827240706631103205

theorem tailTrace_5877013 : CollatzResearch.WordTrace tailWord_5877013 prefixEnd_5877013 1005910827240706631103205 := by
  unfold tailWord_5877013
  simp only [CollatzResearch.WordTrace]
  refine ⟨214352273857593089755763693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142901515905062059837175795 214352273857593089755763693)
  ·
    refine ⟨80382102696597408658411385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214352273857593089755763693 80382102696597408658411385)
    ·
      refine ⟨60286577022448056493808539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80382102696597408658411385 60286577022448056493808539)
      ·
        refine ⟨90429865533672084740712809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60286577022448056493808539 90429865533672084740712809)
        ·
          refine ⟨67822399150254063555534607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90429865533672084740712809 67822399150254063555534607)
          ·
            refine ⟨101733598725381095333301911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67822399150254063555534607 101733598725381095333301911)
            ·
              refine ⟨152600398088071642999952867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101733598725381095333301911 152600398088071642999952867)
              ·
                refine ⟨228900597132107464499929301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152600398088071642999952867 228900597132107464499929301)
                ·
                  refine ⟨5364857745283768699217093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 228900597132107464499929301 5364857745283768699217093)
                  ·
                    refine ⟨1005910827240706631103205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364857745283768699217093 1005910827240706631103205)
                    ·
                      rfl

theorem cell23_5877013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_5877013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877013 prefixEnd_5877013 := by exact prefixLift 5877013
  have htrace : WordTrace (prefixWord ++ tailWord_5877013) baseStart_5877013 baseEnd_5877013 := by
    simpa [prefixWord, tailWord_5877013, baseEnd_5877013] using wordTrace_append hprefix tailTrace_5877013
  have hstable : (prefixWord ++ tailWord_5877013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877013).length < 2 ^ (prefixWord ++ tailWord_5877013).sum := by decide
  have hdescent : baseEnd_5877013 < baseStart_5877013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877020 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5877020 : Nat := 118140960795 + 5877020 * 2 ^ 59
def prefixEnd_5877020 : Nat := 4983230072969 + 3 ^ 40 * 5877020 * 2
def baseEnd_5877020 : Nat := 3017736076086701365922083

theorem tailTrace_5877020 : CollatzResearch.WordTrace tailWord_5877020 prefixEnd_5877020 3017736076086701365922083 := by
  unfold tailWord_5877020
  simp only [CollatzResearch.WordTrace]
  refine ⟨107176264584283864975634257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142901686112378486634179009 107176264584283864975634257)
  ·
    refine ⟨80382198438212898731725693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107176264584283864975634257 80382198438212898731725693)
    ·
      refine ⟨30143324414329837024397135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80382198438212898731725693 30143324414329837024397135)
      ·
        refine ⟨45214986621494755536595703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30143324414329837024397135 45214986621494755536595703)
        ·
          refine ⟨67822479932242133304893555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45214986621494755536595703 67822479932242133304893555)
          ·
            refine ⟨101733719898363199957340333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67822479932242133304893555 101733719898363199957340333)
            ·
              refine ⟨38150144961886199984002625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101733719898363199957340333 38150144961886199984002625)
              ·
                refine ⟨28612608721414649988001969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38150144961886199984002625 28612608721414649988001969)
                ·
                  refine ⟨21459456541060987491001477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28612608721414649988001969 21459456541060987491001477)
                  ·
                    refine ⟨4023648101448935154562777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21459456541060987491001477 4023648101448935154562777)
                    ·
                      refine ⟨3017736076086701365922083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023648101448935154562777 3017736076086701365922083)
                      ·
                        rfl

theorem cell23_5877020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5877020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877020 prefixEnd_5877020 := by exact prefixLift 5877020
  have htrace : WordTrace (prefixWord ++ tailWord_5877020) baseStart_5877020 baseEnd_5877020 := by
    simpa [prefixWord, tailWord_5877020, baseEnd_5877020] using wordTrace_append hprefix tailTrace_5877020
  have hstable : (prefixWord ++ tailWord_5877020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877020).length < 2 ^ (prefixWord ++ tailWord_5877020).sum := by decide
  have hdescent : baseEnd_5877020 < baseStart_5877020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877060 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 8]
def baseStart_5877060 : Nat := 118140960795 + 5877060 * 2 ^ 59
def prefixEnd_5877060 : Nat := 4983230072969 + 3 ^ 40 * 5877060 * 2
def baseEnd_5877060 : Nat := 335306290590320134380211

theorem tailTrace_5877060 : CollatzResearch.WordTrace tailWord_5877060 prefixEnd_5877060 335306290590320134380211 := by
  unfold tailWord_5877060
  simp only [CollatzResearch.WordTrace]
  refine ⟨107176994044211408391362317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142902658725615211188483089 107176994044211408391362317)
  ·
    refine ⟨40191372766579278146760869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107176994044211408391362317 40191372766579278146760869)
    ·
      refine ⟨7535882393733614652517663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40191372766579278146760869 7535882393733614652517663)
      ·
        refine ⟨11303823590600421978776495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7535882393733614652517663 11303823590600421978776495)
        ·
          refine ⟨16955735385900632968164743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303823590600421978776495 16955735385900632968164743)
          ·
            refine ⟨25433603078850949452247115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16955735385900632968164743 25433603078850949452247115)
            ·
              refine ⟨38150404618276424178370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25433603078850949452247115 38150404618276424178370673)
              ·
                refine ⟨28612803463707318133778005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38150404618276424178370673 28612803463707318133778005)
                ·
                  refine ⟨335306290590320134380211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28612803463707318133778005 335306290590320134380211)
                  ·
                    rfl

theorem cell23_5877060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_5877060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877060 prefixEnd_5877060 := by exact prefixLift 5877060
  have htrace : WordTrace (prefixWord ++ tailWord_5877060) baseStart_5877060 baseEnd_5877060 := by
    simpa [prefixWord, tailWord_5877060, baseEnd_5877060] using wordTrace_append hprefix tailTrace_5877060
  have hstable : (prefixWord ++ tailWord_5877060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877060).length < 2 ^ (prefixWord ++ tailWord_5877060).sum := by decide
  have hdescent : baseEnd_5877060 < baseStart_5877060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877090 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5877090 : Nat := 118140960795 + 5877090 * 2 ^ 59
def prefixEnd_5877090 : Nat := 4983230072969 + 3 ^ 40 * 5877090 * 2
def baseEnd_5877090 : Nat := 1005924006577505364015587

theorem tailTrace_5877090 : CollatzResearch.WordTrace tailWord_5877090 prefixEnd_5877090 1005924006577505364015587 := by
  unfold tailWord_5877090
  simp only [CollatzResearch.WordTrace]
  refine ⟨53588770569578532976579181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142903388185542754604211149 53588770569578532976579181)
  ·
    refine ⟨20095788963591949866217193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53588770569578532976579181 20095788963591949866217193)
    ·
      refine ⟨15071841722693962399662895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20095788963591949866217193 15071841722693962399662895)
      ·
        refine ⟨22607762584040943599494343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15071841722693962399662895 22607762584040943599494343)
        ·
          refine ⟨33911643876061415399241515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22607762584040943599494343 33911643876061415399241515)
          ·
            refine ⟨50867465814092123098862273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33911643876061415399241515 50867465814092123098862273)
            ·
              refine ⟨38150599360569092324146705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50867465814092123098862273 38150599360569092324146705)
              ·
                refine ⟨28612949520426819243110029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38150599360569092324146705 28612949520426819243110029)
                ·
                  refine ⟨10729856070160057216166261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28612949520426819243110029 10729856070160057216166261)
                  ·
                    refine ⟨1005924006577505364015587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10729856070160057216166261 1005924006577505364015587)
                    ·
                      rfl

theorem cell23_5877090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5877090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877090 prefixEnd_5877090 := by exact prefixLift 5877090
  have htrace : WordTrace (prefixWord ++ tailWord_5877090) baseStart_5877090 baseEnd_5877090 := by
    simpa [prefixWord, tailWord_5877090, baseEnd_5877090] using wordTrace_append hprefix tailTrace_5877090
  have hstable : (prefixWord ++ tailWord_5877090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877090).length < 2 ^ (prefixWord ++ tailWord_5877090).sum := by decide
  have hdescent : baseEnd_5877090 < baseStart_5877090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877103 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 1, 6]
def baseStart_5877103 : Nat := 118140960795 + 5877103 * 2 ^ 59
def prefixEnd_5877103 : Nat := 4983230072969 + 3 ^ 40 * 5877103 * 2
def baseEnd_5877103 : Nat := 1005926231660341513728067

theorem tailTrace_5877103 : CollatzResearch.WordTrace tailWord_5877103 prefixEnd_5877103 1005926231660341513728067 := by
  unfold tailWord_5877103
  simp only [CollatzResearch.WordTrace]
  refine ⟨214355556427267035126539963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142903704284844690084359975 214355556427267035126539963)
  ·
    refine ⟨321533334640900552689809945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214355556427267035126539963 321533334640900552689809945)
    ·
      refine ⟨241150000980675414517357459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321533334640900552689809945 241150000980675414517357459)
      ·
        refine ⟨361725001471013121776036189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241150000980675414517357459 361725001471013121776036189)
        ·
          refine ⟨135646875551629920666013571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361725001471013121776036189 135646875551629920666013571)
          ·
            refine ⟨203470313327444880999020357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135646875551629920666013571 203470313327444880999020357)
            ·
              refine ⟨38150683748895915187316317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203470313327444880999020357 38150683748895915187316317)
              ·
                refine ⟨14306506405835968195243619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38150683748895915187316317 14306506405835968195243619)
                ·
                  refine ⟨21459759608753952292865429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14306506405835968195243619 21459759608753952292865429)
                  ·
                    refine ⟨1005926231660341513728067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21459759608753952292865429 1005926231660341513728067)
                    ·
                      rfl

theorem cell23_5877103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_5877103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877103 prefixEnd_5877103 := by exact prefixLift 5877103
  have htrace : WordTrace (prefixWord ++ tailWord_5877103) baseStart_5877103 baseEnd_5877103 := by
    simpa [prefixWord, tailWord_5877103, baseEnd_5877103] using wordTrace_append hprefix tailTrace_5877103
  have hstable : (prefixWord ++ tailWord_5877103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877103).length < 2 ^ (prefixWord ++ tailWord_5877103).sum := by decide
  have hdescent : baseEnd_5877103 < baseStart_5877103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877113 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_5877113 : Nat := 118140960795 + 5877113 * 2 ^ 59
def prefixEnd_5877113 : Nat := 4983230072969 + 3 ^ 40 * 5877113 * 2
def baseEnd_5877113 : Nat := 3017783829787569502059155

theorem tailTrace_5877113 : CollatzResearch.WordTrace tailWord_5877113 prefixEnd_5877113 3017783829787569502059155 := by
  unfold tailWord_5877113
  simp only [CollatzResearch.WordTrace]
  refine ⟨214355921157230806834403993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142903947438153871222935995 214355921157230806834403993)
  ·
    refine ⟨160766940867923105125802995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214355921157230806834403993 160766940867923105125802995)
    ·
      refine ⟨241150411301884657688704493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160766940867923105125802995 241150411301884657688704493)
      ·
        refine ⟨90431404238206746633264185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241150411301884657688704493 90431404238206746633264185)
        ·
          refine ⟨67823553178655059974948139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90431404238206746633264185 67823553178655059974948139)
          ·
            refine ⟨101735329767982589962422209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67823553178655059974948139 101735329767982589962422209)
            ·
              refine ⟨76301497325986942471816657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101735329767982589962422209 76301497325986942471816657)
              ·
                refine ⟨57226122994490206853862493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76301497325986942471816657 57226122994490206853862493)
                ·
                  refine ⟨21459796122933827570198435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57226122994490206853862493 21459796122933827570198435)
                  ·
                    refine ⟨32189694184400741355297653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21459796122933827570198435 32189694184400741355297653)
                    ·
                      refine ⟨3017783829787569502059155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32189694184400741355297653 3017783829787569502059155)
                      ·
                        rfl

theorem cell23_5877113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_5877113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877113 prefixEnd_5877113 := by exact prefixLift 5877113
  have htrace : WordTrace (prefixWord ++ tailWord_5877113) baseStart_5877113 baseEnd_5877113 := by
    simpa [prefixWord, tailWord_5877113, baseEnd_5877113] using wordTrace_append hprefix tailTrace_5877113
  have hstable : (prefixWord ++ tailWord_5877113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877113).length < 2 ^ (prefixWord ++ tailWord_5877113).sum := by decide
  have hdescent : baseEnd_5877113 < baseStart_5877113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877138 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5877138 : Nat := 118140960795 + 5877138 * 2 ^ 59
def prefixEnd_5877138 : Nat := 4983230072969 + 3 ^ 40 * 5877138 * 2
def baseEnd_5877138 : Nat := 3017796666803931904246541

theorem tailTrace_5877138 : CollatzResearch.WordTrace tailWord_5877138 prefixEnd_5877138 3017796666803931904246541 := by
  unfold tailWord_5877138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53589208245535059026016017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142904555321426824069376045 53589208245535059026016017)
  ·
    refine ⟨40191906184151294269512013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53589208245535059026016017 40191906184151294269512013)
    ·
      refine ⟨15071964819056735351067005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40191906184151294269512013 15071964819056735351067005)
      ·
        refine ⟨5651986807146275756650127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15071964819056735351067005 5651986807146275756650127)
        ·
          refine ⟨8477980210719413634975191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5651986807146275756650127 8477980210719413634975191)
          ·
            refine ⟨12716970316079120452462787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8477980210719413634975191 12716970316079120452462787)
            ·
              refine ⟨19075455474118680678694181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12716970316079120452462787 19075455474118680678694181)
              ·
                refine ⟨3576647901397252627255159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19075455474118680678694181 3576647901397252627255159)
                ·
                  refine ⟨5364971852095878940882739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576647901397252627255159 5364971852095878940882739)
                  ·
                    refine ⟨8047457778143818411324109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5364971852095878940882739 8047457778143818411324109)
                    ·
                      refine ⟨3017796666803931904246541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047457778143818411324109 3017796666803931904246541)
                      ·
                        rfl

theorem cell23_5877138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5877138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877138 prefixEnd_5877138 := by exact prefixLift 5877138
  have htrace : WordTrace (prefixWord ++ tailWord_5877138) baseStart_5877138 baseEnd_5877138 := by
    simpa [prefixWord, tailWord_5877138, baseEnd_5877138] using wordTrace_append hprefix tailTrace_5877138
  have hstable : (prefixWord ++ tailWord_5877138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877138).length < 2 ^ (prefixWord ++ tailWord_5877138).sum := by decide
  have hdescent : baseEnd_5877138 < baseStart_5877138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877194 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_5877194 : Nat := 118140960795 + 5877194 * 2 ^ 59
def prefixEnd_5877194 : Nat := 4983230072969 + 3 ^ 40 * 5877194 * 2
def baseEnd_5877194 : Nat := 3017825421720583685146283

theorem tailTrace_5877194 : CollatzResearch.WordTrace tailWord_5877194 prefixEnd_5877194 3017825421720583685146283 := by
  unfold tailWord_5877194
  simp only [CollatzResearch.WordTrace]
  refine ⟨53589718867484339417025659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142905916979958238445401757 53589718867484339417025659)
  ·
    refine ⟨80384578301226509125538489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53589718867484339417025659 80384578301226509125538489)
    ·
      refine ⟨60288433725919881844153867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80384578301226509125538489 60288433725919881844153867)
      ·
        refine ⟨90432650588879822766230801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60288433725919881844153867 90432650588879822766230801)
        ·
          refine ⟨67824487941659867074673101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90432650588879822766230801 67824487941659867074673101)
          ·
            refine ⟨25434182978122450153002413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67824487941659867074673101 25434182978122450153002413)
            ·
              refine ⟨9537818616795918807375905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25434182978122450153002413 9537818616795918807375905)
              ·
                refine ⟨7153363962596939105531929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537818616795918807375905 7153363962596939105531929)
                ·
                  refine ⟨5365022971947704329148947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7153363962596939105531929 5365022971947704329148947)
                  ·
                    refine ⟨8047534457921556493723421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365022971947704329148947 8047534457921556493723421)
                    ·
                      refine ⟨3017825421720583685146283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047534457921556493723421 3017825421720583685146283)
                      ·
                        rfl

theorem cell23_5877194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_5877194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877194 prefixEnd_5877194 := by exact prefixLift 5877194
  have htrace : WordTrace (prefixWord ++ tailWord_5877194) baseStart_5877194 baseEnd_5877194 := by
    simpa [prefixWord, tailWord_5877194, baseEnd_5877194] using wordTrace_append hprefix tailTrace_5877194
  have hstable : (prefixWord ++ tailWord_5877194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877194).length < 2 ^ (prefixWord ++ tailWord_5877194).sum := by decide
  have hdescent : baseEnd_5877194 < baseStart_5877194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877210 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_5877210 : Nat := 118140960795 + 5877210 * 2 ^ 59
def prefixEnd_5877210 : Nat := 4983230072969 + 3 ^ 40 * 5877210 * 2
def baseEnd_5877210 : Nat := 1005944545803685207515403

theorem tailTrace_5877210 : CollatzResearch.WordTrace tailWord_5877210 prefixEnd_5877210 1005944545803685207515403 := by
  unfold tailWord_5877210
  simp only [CollatzResearch.WordTrace]
  refine ⟨53589864759469848100171271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142906306025252928267123389 53589864759469848100171271)
  ·
    refine ⟨80384797139204772150256907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53589864759469848100171271 80384797139204772150256907)
    ·
      refine ⟨120577195708807158225385361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80384797139204772150256907 120577195708807158225385361)
      ·
        refine ⟨90432896781605368669039021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120577195708807158225385361 90432896781605368669039021)
        ·
          refine ⟨33912336293102013250889633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90432896781605368669039021 33912336293102013250889633)
          ·
            refine ⟨25434252219826509938167225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33912336293102013250889633 25434252219826509938167225)
            ·
              refine ⟨19075689164869882453625419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25434252219826509938167225 19075689164869882453625419)
              ·
                refine ⟨28613533747304823680438129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19075689164869882453625419 28613533747304823680438129)
                ·
                  refine ⟨21460150310478617760328597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28613533747304823680438129 21460150310478617760328597)
                  ·
                    refine ⟨1005944545803685207515403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21460150310478617760328597 1005944545803685207515403)
                    ·
                      rfl

theorem cell23_5877210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_5877210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877210 prefixEnd_5877210 := by exact prefixLift 5877210
  have htrace : WordTrace (prefixWord ++ tailWord_5877210) baseStart_5877210 baseEnd_5877210 := by
    simpa [prefixWord, tailWord_5877210, baseEnd_5877210] using wordTrace_append hprefix tailTrace_5877210
  have hstable : (prefixWord ++ tailWord_5877210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877210).length < 2 ^ (prefixWord ++ tailWord_5877210).sum := by decide
  have hdescent : baseEnd_5877210 < baseStart_5877210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877220 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_5877220 : Nat := 118140960795 + 5877220 * 2 ^ 59
def prefixEnd_5877220 : Nat := 4983230072969 + 3 ^ 40 * 5877220 * 2
def baseEnd_5877220 : Nat := 3017838772217600583421163

theorem tailTrace_5877220 : CollatzResearch.WordTrace tailWord_5877220 prefixEnd_5877220 3017838772217600583421163 := by
  unfold tailWord_5877220
  simp only [CollatzResearch.WordTrace]
  refine ⟨107179911883921582054274557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142906549178562109405699409 107179911883921582054274557)
  ·
    refine ⟨40192466956470593270352959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107179911883921582054274557 40192466956470593270352959)
    ·
      refine ⟨60288700434705889905529439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40192466956470593270352959 60288700434705889905529439)
      ·
        refine ⟨90433050652058834858294159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60288700434705889905529439 90433050652058834858294159)
        ·
          refine ⟨135649575978088252287441239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90433050652058834858294159 135649575978088252287441239)
          ·
            refine ⟨203474363967132378431161859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135649575978088252287441239 203474363967132378431161859)
            ·
              refine ⟨305211545950698567646742789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203474363967132378431161859 305211545950698567646742789)
              ·
                refine ⟨57227164865755981433764273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305211545950698567646742789 57227164865755981433764273)
                ·
                  refine ⟨42920373649316986075323205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57227164865755981433764273 42920373649316986075323205)
                  ·
                    refine ⟨8047570059246934889123101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42920373649316986075323205 8047570059246934889123101)
                    ·
                      refine ⟨3017838772217600583421163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047570059246934889123101 3017838772217600583421163)
                      ·
                        rfl

theorem cell23_5877220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_5877220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877220 prefixEnd_5877220 := by exact prefixLift 5877220
  have htrace : WordTrace (prefixWord ++ tailWord_5877220) baseStart_5877220 baseEnd_5877220 := by
    simpa [prefixWord, tailWord_5877220, baseEnd_5877220] using wordTrace_append hprefix tailTrace_5877220
  have hstable : (prefixWord ++ tailWord_5877220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877220).length < 2 ^ (prefixWord ++ tailWord_5877220).sum := by decide
  have hdescent : baseEnd_5877220 < baseStart_5877220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877221 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5877221 : Nat := 118140960795 + 5877221 * 2 ^ 59
def prefixEnd_5877221 : Nat := 4983230072969 + 3 ^ 40 * 5877221 * 2
def baseEnd_5877221 : Nat := 3017839285698255079508659

theorem tailTrace_5877221 : CollatzResearch.WordTrace tailWord_5877221 prefixEnd_5877221 3017839285698255079508659 := by
  unfold tailWord_5877221
  simp only [CollatzResearch.WordTrace]
  refine ⟨214359860240839541279335517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142906573493893027519557011 214359860240839541279335517)
  ·
    refine ⟨80384947590314827979750819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214359860240839541279335517 80384947590314827979750819)
    ·
      refine ⟨120577421385472241969626229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80384947590314827979750819 120577421385472241969626229)
      ·
        refine ⟨11304133254888022684652459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120577421385472241969626229 11304133254888022684652459)
        ·
          refine ⟨16956199882332034026978689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11304133254888022684652459 16956199882332034026978689)
          ·
            refine ⟨12717149911749025520234017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16956199882332034026978689 12717149911749025520234017)
            ·
              refine ⟨9537862433811769140175513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12717149911749025520234017 9537862433811769140175513)
              ·
                refine ⟨7153396825358826855131635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537862433811769140175513 7153396825358826855131635)
                ·
                  refine ⟨10730095238038240282697453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7153396825358826855131635 10730095238038240282697453)
                  ·
                    refine ⟨4023785714264340106011545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10730095238038240282697453 4023785714264340106011545)
                    ·
                      refine ⟨3017839285698255079508659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023785714264340106011545 3017839285698255079508659)
                      ·
                        rfl

theorem cell23_5877221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5877221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877221 prefixEnd_5877221 := by exact prefixLift 5877221
  have htrace : WordTrace (prefixWord ++ tailWord_5877221) baseStart_5877221 baseEnd_5877221 := by
    simpa [prefixWord, tailWord_5877221, baseEnd_5877221] using wordTrace_append hprefix tailTrace_5877221
  have hstable : (prefixWord ++ tailWord_5877221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877221).length < 2 ^ (prefixWord ++ tailWord_5877221).sum := by decide
  have hdescent : baseEnd_5877221 < baseStart_5877221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877237 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5877237 : Nat := 118140960795 + 5877237 * 2 ^ 59
def prefixEnd_5877237 : Nat := 4983230072969 + 3 ^ 40 * 5877237 * 2
def baseEnd_5877237 : Nat := 3017847501388727016908585

theorem tailTrace_5877237 : CollatzResearch.WordTrace tailWord_5877237 prefixEnd_5877237 3017847501388727016908585 := by
  unfold tailWord_5877237
  simp only [CollatzResearch.WordTrace]
  refine ⟨214360443808781576011917965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142906962539187717341278643 214360443808781576011917965)
  ·
    refine ⟨80385166428293091004469237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214360443808781576011917965 80385166428293091004469237)
    ·
      refine ⟨7536109352652477281668991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80385166428293091004469237 7536109352652477281668991)
      ·
        refine ⟨11304164028978715922503487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536109352652477281668991 11304164028978715922503487)
        ·
          refine ⟨16956246043468073883755231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11304164028978715922503487 16956246043468073883755231)
          ·
            refine ⟨25434369065202110825632847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16956246043468073883755231 25434369065202110825632847)
            ·
              refine ⟨38151553597803166238449271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25434369065202110825632847 38151553597803166238449271)
              ·
                refine ⟨57227330396704749357673907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38151553597803166238449271 57227330396704749357673907)
                ·
                  refine ⟨85840995595057124036510861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57227330396704749357673907 85840995595057124036510861)
                  ·
                    refine ⟨32190373348146421513691573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85840995595057124036510861 32190373348146421513691573)
                    ·
                      refine ⟨3017847501388727016908585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32190373348146421513691573 3017847501388727016908585)
                      ·
                        rfl

theorem cell23_5877237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5877237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877237 prefixEnd_5877237 := by exact prefixLift 5877237
  have htrace : WordTrace (prefixWord ++ tailWord_5877237) baseStart_5877237 baseEnd_5877237 := by
    simpa [prefixWord, tailWord_5877237, baseEnd_5877237] using wordTrace_append hprefix tailTrace_5877237
  have hstable : (prefixWord ++ tailWord_5877237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877237).length < 2 ^ (prefixWord ++ tailWord_5877237).sum := by decide
  have hdescent : baseEnd_5877237 < baseStart_5877237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877308 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 5]
def baseStart_5877308 : Nat := 118140960795 + 5877308 * 2 ^ 59
def prefixEnd_5877308 : Nat := 4983230072969 + 3 ^ 40 * 5877308 * 2
def baseEnd_5877308 : Nat := 335320439835021804346751

theorem tailTrace_5877308 : CollatzResearch.WordTrace tailWord_5877308 prefixEnd_5877308 335320439835021804346751 := by
  unfold tailWord_5877308
  simp only [CollatzResearch.WordTrace]
  refine ⟨107181516695762177568876289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142908688927682903425168385 107181516695762177568876289)
  ·
    refine ⟨80386137521821633176657217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107181516695762177568876289 80386137521821633176657217)
    ·
      refine ⟨60289603141366224882492913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80386137521821633176657217 60289603141366224882492913)
      ·
        refine ⟨45217202356024668661869685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60289603141366224882492913 45217202356024668661869685)
        ·
          refine ⟨4239112720877312687050283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45217202356024668661869685 4239112720877312687050283)
          ·
            refine ⟨6358669081315969030575425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239112720877312687050283 6358669081315969030575425)
            ·
              refine ⟨4769001810986976772931569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6358669081315969030575425 4769001810986976772931569)
              ·
                refine ⟨3576751358240232579698677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769001810986976772931569 3576751358240232579698677)
                ·
                  refine ⟨335320439835021804346751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3576751358240232579698677 335320439835021804346751)
                  ·
                    rfl

theorem cell23_5877308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_5877308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877308 prefixEnd_5877308 := by exact prefixLift 5877308
  have htrace : WordTrace (prefixWord ++ tailWord_5877308) baseStart_5877308 baseEnd_5877308 := by
    simpa [prefixWord, tailWord_5877308, baseEnd_5877308] using wordTrace_append hprefix tailTrace_5877308
  have hstable : (prefixWord ++ tailWord_5877308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877308).length < 2 ^ (prefixWord ++ tailWord_5877308).sum := by decide
  have hdescent : baseEnd_5877308 < baseStart_5877308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877317 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_5877317 : Nat := 118140960795 + 5877317 * 2 ^ 59
def prefixEnd_5877317 : Nat := 4983230072969 + 3 ^ 40 * 5877317 * 2
def baseEnd_5877317 : Nat := 1005962859947028901302739

theorem tailTrace_5877317 : CollatzResearch.WordTrace tailWord_5877317 prefixEnd_5877317 1005962859947028901302739 := by
  unfold tailWord_5877317
  simp only [CollatzResearch.WordTrace]
  refine ⟨214363361648491749674830205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142908907765661166449886803 214363361648491749674830205)
  ·
    refine ⟨80386260618184406128061327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214363361648491749674830205 80386260618184406128061327)
    ·
      refine ⟨120579390927276609192091991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80386260618184406128061327 120579390927276609192091991)
      ·
        refine ⟨180869086390914913788137987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120579390927276609192091991 180869086390914913788137987)
        ·
          refine ⟨271303629586372370682206981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180869086390914913788137987 271303629586372370682206981)
          ·
            refine ⟨50869430547444819502913809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271303629586372370682206981 50869430547444819502913809)
            ·
              refine ⟨38152072910583614627185357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50869430547444819502913809 38152072910583614627185357)
              ·
                refine ⟨14307027341468855485194509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38152072910583614627185357 14307027341468855485194509)
                ·
                  refine ⟨5365135253050820806947941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14307027341468855485194509 5365135253050820806947941)
                  ·
                    refine ⟨1005962859947028901302739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365135253050820806947941 1005962859947028901302739)
                    ·
                      rfl

theorem cell23_5877317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_5877317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877317 prefixEnd_5877317 := by exact prefixLift 5877317
  have htrace : WordTrace (prefixWord ++ tailWord_5877317) baseStart_5877317 baseEnd_5877317 := by
    simpa [prefixWord, tailWord_5877317, baseEnd_5877317] using wordTrace_append hprefix tailTrace_5877317
  have hstable : (prefixWord ++ tailWord_5877317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877317).length < 2 ^ (prefixWord ++ tailWord_5877317).sum := by decide
  have hdescent : baseEnd_5877317 < baseStart_5877317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877320 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_5877320 : Nat := 118140960795 + 5877320 * 2 ^ 59
def prefixEnd_5877320 : Nat := 4983230072969 + 3 ^ 40 * 5877320 * 2
def baseEnd_5877320 : Nat := 3017890120283050192170703

theorem tailTrace_5877320 : CollatzResearch.WordTrace tailWord_5877320 prefixEnd_5877320 3017890120283050192170703 := by
  unfold tailWord_5877320
  simp only [CollatzResearch.WordTrace]
  refine ⟨107181735533740440593594707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142908980711653920791459609 107181735533740440593594707)
  ·
    refine ⟨160772603300610660890392061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107181735533740440593594707 160772603300610660890392061)
    ·
      refine ⟨60289726237728997833897023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160772603300610660890392061 60289726237728997833897023)
      ·
        refine ⟨90434589356593496750845535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60289726237728997833897023 90434589356593496750845535)
        ·
          refine ⟨135651884034890245126268303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90434589356593496750845535 135651884034890245126268303)
          ·
            refine ⟨203477826052335367689402455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135651884034890245126268303 203477826052335367689402455)
            ·
              refine ⟨305216739078503051534103683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203477826052335367689402455 305216739078503051534103683)
              ·
                refine ⟨457825108617754577301155525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305216739078503051534103683 457825108617754577301155525)
                ·
                  refine ⟨85842207865828983243966661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 457825108617754577301155525 85842207865828983243966661)
                  ·
                    refine ⟨16095413974842934358243749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85842207865828983243966661 16095413974842934358243749)
                    ·
                      refine ⟨3017890120283050192170703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16095413974842934358243749 3017890120283050192170703)
                      ·
                        rfl

theorem cell23_5877320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_5877320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877320 prefixEnd_5877320 := by exact prefixLift 5877320
  have htrace : WordTrace (prefixWord ++ tailWord_5877320) baseStart_5877320 baseEnd_5877320 := by
    simpa [prefixWord, tailWord_5877320, baseEnd_5877320] using wordTrace_append hprefix tailTrace_5877320
  have hstable : (prefixWord ++ tailWord_5877320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877320).length < 2 ^ (prefixWord ++ tailWord_5877320).sum := by decide
  have hdescent : baseEnd_5877320 < baseStart_5877320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877324 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 2, 4, 2]
def baseStart_5877324 : Nat := 118140960795 + 5877324 * 2 ^ 59
def prefixEnd_5877324 : Nat := 4983230072969 + 3 ^ 40 * 5877324 * 2
def baseEnd_5877324 : Nat := 3017892174205668176520685

theorem tailTrace_5877324 : CollatzResearch.WordTrace tailWord_5877324 prefixEnd_5877324 3017892174205668176520685 := by
  unfold tailWord_5877324
  simp only [CollatzResearch.WordTrace]
  refine ⟨107181808479733194935167513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142909077972977593246890017 107181808479733194935167513)
  ·
    refine ⟨80386356359799896201375635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107181808479733194935167513 80386356359799896201375635)
    ·
      refine ⟨120579534539699844302063453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80386356359799896201375635 120579534539699844302063453)
      ·
        refine ⟨45217325452387441613273795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120579534539699844302063453 45217325452387441613273795)
        ·
          refine ⟨67825988178581162419910693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45217325452387441613273795 67825988178581162419910693)
          ·
            refine ⟨12717372783483967953733255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67825988178581162419910693 12717372783483967953733255)
            ·
              refine ⟨19076059175225951930599883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12717372783483967953733255 19076059175225951930599883)
              ·
                refine ⟨28614088762838927895899825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19076059175225951930599883 28614088762838927895899825)
                ·
                  refine ⟨21460566572129195921924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28614088762838927895899825 21460566572129195921924869)
                  ·
                    refine ⟨4023856232274224235360913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21460566572129195921924869 4023856232274224235360913)
                    ·
                      refine ⟨3017892174205668176520685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023856232274224235360913 3017892174205668176520685)
                      ·
                        rfl

theorem cell23_5877324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_5877324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877324 prefixEnd_5877324 := by exact prefixLift 5877324
  have htrace : WordTrace (prefixWord ++ tailWord_5877324) baseStart_5877324 baseEnd_5877324 := by
    simpa [prefixWord, tailWord_5877324, baseEnd_5877324] using wordTrace_append hprefix tailTrace_5877324
  have hstable : (prefixWord ++ tailWord_5877324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877324).length < 2 ^ (prefixWord ++ tailWord_5877324).sum := by decide
  have hdescent : baseEnd_5877324 < baseStart_5877324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877341 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5877341 : Nat := 118140960795 + 5877341 * 2 ^ 59
def prefixEnd_5877341 : Nat := 4983230072969 + 3 ^ 40 * 5877341 * 2
def baseEnd_5877341 : Nat := 3017900903376794610008107

theorem tailTrace_5877341 : CollatzResearch.WordTrace tailWord_5877341 prefixEnd_5877341 3017900903376794610008107 := by
  unfold tailWord_5877341
  simp only [CollatzResearch.WordTrace]
  refine ⟨214364237000404801773703877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142909491333603201182469251 214364237000404801773703877)
  ·
    refine ⟨40193294437575900332569477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214364237000404801773703877 40193294437575900332569477)
    ·
      refine ⟨7536242707045481312356777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40193294437575900332569477 7536242707045481312356777)
      ·
        refine ⟨5652182030284110984267583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7536242707045481312356777 5652182030284110984267583)
        ·
          refine ⟨8478273045426166476401375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652182030284110984267583 8478273045426166476401375)
          ·
            refine ⟨12717409568139249714602063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8478273045426166476401375 12717409568139249714602063)
            ·
              refine ⟨19076114352208874571903095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12717409568139249714602063 19076114352208874571903095)
              ·
                refine ⟨28614171528313311857854643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19076114352208874571903095 28614171528313311857854643)
                ·
                  refine ⟨42921257292469967786781965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28614171528313311857854643 42921257292469967786781965)
                  ·
                    refine ⟨16095471484676237920043237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42921257292469967786781965 16095471484676237920043237)
                    ·
                      refine ⟨3017900903376794610008107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16095471484676237920043237 3017900903376794610008107)
                      ·
                        rfl

theorem cell23_5877341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5877341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877341 prefixEnd_5877341 := by exact prefixLift 5877341
  have htrace : WordTrace (prefixWord ++ tailWord_5877341) baseStart_5877341 baseEnd_5877341 := by
    simpa [prefixWord, tailWord_5877341, baseEnd_5877341] using wordTrace_append hprefix tailTrace_5877341
  have hstable : (prefixWord ++ tailWord_5877341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877341).length < 2 ^ (prefixWord ++ tailWord_5877341).sum := by decide
  have hdescent : baseEnd_5877341 < baseStart_5877341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877370 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_5877370 : Nat := 118140960795 + 5877370 * 2 ^ 59
def prefixEnd_5877370 : Nat := 4983230072969 + 3 ^ 40 * 5877370 * 2
def baseEnd_5877370 : Nat := 3017915794315774996545473

theorem tailTrace_5877370 : CollatzResearch.WordTrace tailWord_5877370 prefixEnd_5877370 3017915794315774996545473 := by
  unfold tailWord_5877370
  simp only [CollatzResearch.WordTrace]
  refine ⟨53591323679324934931627391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142910196478199826484339709 53591323679324934931627391)
  ·
    refine ⟨80386985518987402397441087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53591323679324934931627391 80386985518987402397441087)
    ·
      refine ⟨120580478278481103596161631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80386985518987402397441087 120580478278481103596161631)
      ·
        refine ⟨180870717417721655394242447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120580478278481103596161631 180870717417721655394242447)
        ·
          refine ⟨271306076126582483091363671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180870717417721655394242447 271306076126582483091363671)
          ·
            refine ⟨406959114189873724637045507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271306076126582483091363671 406959114189873724637045507)
            ·
              refine ⟨610438671284810586955568261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406959114189873724637045507 610438671284810586955568261)
              ·
                refine ⟨114457250865901985054169049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 610438671284810586955568261 114457250865901985054169049)
                ·
                  refine ⟨85842938149426488790626787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114457250865901985054169049 85842938149426488790626787)
                  ·
                    refine ⟨128764407224139733185940181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85842938149426488790626787 128764407224139733185940181)
                    ·
                      refine ⟨3017915794315774996545473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128764407224139733185940181 3017915794315774996545473)
                      ·
                        rfl

theorem cell23_5877370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_5877370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877370 prefixEnd_5877370 := by exact prefixLift 5877370
  have htrace : WordTrace (prefixWord ++ tailWord_5877370) baseStart_5877370 baseEnd_5877370 := by
    simpa [prefixWord, tailWord_5877370, baseEnd_5877370] using wordTrace_append hprefix tailTrace_5877370
  have hstable : (prefixWord ++ tailWord_5877370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877370).length < 2 ^ (prefixWord ++ tailWord_5877370).sum := by decide
  have hdescent : baseEnd_5877370 < baseStart_5877370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877397 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_5877397 : Nat := 118140960795 + 5877397 * 2 ^ 59
def prefixEnd_5877397 : Nat := 4983230072969 + 3 ^ 40 * 5877397 * 2
def baseEnd_5877397 : Nat := 3017929658293446390907849

theorem tailTrace_5877397 : CollatzResearch.WordTrace tailWord_5877397 prefixEnd_5877397 3017929658293446390907849 := by
  unfold tailWord_5877397
  simp only [CollatzResearch.WordTrace]
  refine ⟨214366279488201923337742445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142910852992134615558494963 214366279488201923337742445)
  ·
    refine ⟨80387354808075721251653417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214366279488201923337742445 80387354808075721251653417)
    ·
      refine ⟨60290516106056790938740063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80387354808075721251653417 60290516106056790938740063)
      ·
        refine ⟨90435774159085186408110095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60290516106056790938740063 90435774159085186408110095)
        ·
          refine ⟨135653661238627779612165143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90435774159085186408110095 135653661238627779612165143)
          ·
            refine ⟨203480491857941669418247715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135653661238627779612165143 203480491857941669418247715)
            ·
              refine ⟨305220737786912504127371573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203480491857941669418247715 305220737786912504127371573)
              ·
                refine ⟨28614444167523047261941085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305220737786912504127371573 28614444167523047261941085)
                ·
                  refine ⟨10730416562821142723227907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28614444167523047261941085 10730416562821142723227907)
                  ·
                    refine ⟨16095624844231714084841861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10730416562821142723227907 16095624844231714084841861)
                    ·
                      refine ⟨3017929658293446390907849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16095624844231714084841861 3017929658293446390907849)
                      ·
                        rfl

theorem cell23_5877397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_5877397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877397 prefixEnd_5877397 := by exact prefixLift 5877397
  have htrace : WordTrace (prefixWord ++ tailWord_5877397) baseStart_5877397 baseEnd_5877397 := by
    simpa [prefixWord, tailWord_5877397, baseEnd_5877397] using wordTrace_append hprefix tailTrace_5877397
  have hstable : (prefixWord ++ tailWord_5877397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877397).length < 2 ^ (prefixWord ++ tailWord_5877397).sum := by decide
  have hdescent : baseEnd_5877397 < baseStart_5877397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877408 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 1, 1, 3]
def baseStart_5877408 : Nat := 118140960795 + 5877408 * 2 ^ 59
def prefixEnd_5877408 : Nat := 4983230072969 + 3 ^ 40 * 5877408 * 2
def baseEnd_5877408 : Nat := 3017935306580645847870299

theorem tailTrace_5877408 : CollatzResearch.WordTrace tailWord_5877408 prefixEnd_5877408 3017935306580645847870299 := by
  unfold tailWord_5877408
  simp only [CollatzResearch.WordTrace]
  refine ⟨107183340345581036108196439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142911120460774714810928585 107183340345581036108196439)
  ·
    refine ⟨160775010518371554162294659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107183340345581036108196439 160775010518371554162294659)
    ·
      refine ⟨241162515777557331243441989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160775010518371554162294659 241162515777557331243441989)
      ·
        refine ⟨45217971708291999608145373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241162515777557331243441989 45217971708291999608145373)
        ·
          refine ⟨16956739390609499853054515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45217971708291999608145373 16956739390609499853054515)
          ·
            refine ⟨25435109085914249779581773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16956739390609499853054515 25435109085914249779581773)
            ·
              refine ⟨9538165907217843667343165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25435109085914249779581773 9538165907217843667343165)
              ·
                refine ⟨3576812215206691375253687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9538165907217843667343165 3576812215206691375253687)
                ·
                  refine ⟨5365218322810037062880531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576812215206691375253687 5365218322810037062880531)
                  ·
                    refine ⟨8047827484215055594320797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365218322810037062880531 8047827484215055594320797)
                    ·
                      refine ⟨3017935306580645847870299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047827484215055594320797 3017935306580645847870299)
                      ·
                        rfl

theorem cell23_5877408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_5877408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877408 prefixEnd_5877408 := by exact prefixLift 5877408
  have htrace : WordTrace (prefixWord ++ tailWord_5877408) baseStart_5877408 baseEnd_5877408 := by
    simpa [prefixWord, tailWord_5877408, baseEnd_5877408] using wordTrace_append hprefix tailTrace_5877408
  have hstable : (prefixWord ++ tailWord_5877408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877408).length < 2 ^ (prefixWord ++ tailWord_5877408).sum := by decide
  have hdescent : baseEnd_5877408 < baseStart_5877408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877437 : List Nat := [1, 4, 1, 2, 1, 2, 4, 8]
def baseStart_5877437 : Nat := 118140960795 + 5877437 * 2 ^ 59
def prefixEnd_5877437 : Nat := 4983230072969 + 3 ^ 40 * 5877437 * 2
def baseEnd_5877437 : Nat := 111775933241467638311395

theorem tailTrace_5877437 : CollatzResearch.WordTrace tailWord_5877437 prefixEnd_5877437 111775933241467638311395 := by
  unfold tailWord_5877437
  simp only [CollatzResearch.WordTrace]
  refine ⟨214367738408057010169198565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142911825605371340112799043 214367738408057010169198565)
  ·
    refine ⟨40193950951510689406724731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214367738408057010169198565 40193950951510689406724731)
    ·
      refine ⟨60290926427266034110087097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40193950951510689406724731 60290926427266034110087097)
      ·
        refine ⟨45218194820449525582565323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60290926427266034110087097 45218194820449525582565323)
        ·
          refine ⟨67827292230674288373847985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45218194820449525582565323 67827292230674288373847985)
          ·
            refine ⟨50870469173005716280385989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67827292230674288373847985 50870469173005716280385989)
            ·
              refine ⟨9538212969938571802572373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50870469173005716280385989 9538212969938571802572373)
              ·
                refine ⟨111775933241467638311395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9538212969938571802572373 111775933241467638311395)
                ·
                  rfl

theorem cell23_5877437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 8].length) (baseStart_5877437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877437 prefixEnd_5877437 := by exact prefixLift 5877437
  have htrace : WordTrace (prefixWord ++ tailWord_5877437) baseStart_5877437 baseEnd_5877437 := by
    simpa [prefixWord, tailWord_5877437, baseEnd_5877437] using wordTrace_append hprefix tailTrace_5877437
  have hstable : (prefixWord ++ tailWord_5877437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877437).length < 2 ^ (prefixWord ++ tailWord_5877437).sum := by decide
  have hdescent : baseEnd_5877437 < baseStart_5877437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877444 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5877444 : Nat := 118140960795 + 5877444 * 2 ^ 59
def prefixEnd_5877444 : Nat := 4983230072969 + 3 ^ 40 * 5877444 * 2
def baseEnd_5877444 : Nat := 3017953791884207707020133

theorem tailTrace_5877444 : CollatzResearch.WordTrace tailWord_5877444 prefixEnd_5877444 3017953791884207707020133 := by
  unfold tailWord_5877444
  simp only [CollatzResearch.WordTrace]
  refine ⟨107183996859515825182351693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142911995812687766909802257 107183996859515825182351693)
  ·
    refine ⟨40193998822318434443381885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107183996859515825182351693 40193998822318434443381885)
    ·
      refine ⟨15072749558369412916268207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40193998822318434443381885 15072749558369412916268207)
      ·
        refine ⟨22609124337554119374402311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15072749558369412916268207 22609124337554119374402311)
        ·
          refine ⟨33913686506331179061603467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22609124337554119374402311 33913686506331179061603467)
          ·
            refine ⟨50870529759496768592405201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33913686506331179061603467 50870529759496768592405201)
            ·
              refine ⟨38152897319622576444303901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50870529759496768592405201 38152897319622576444303901)
              ·
                refine ⟨14307336494858466166613963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38152897319622576444303901 14307336494858466166613963)
                ·
                  refine ⟨21461004742287699249920945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14307336494858466166613963 21461004742287699249920945)
                  ·
                    refine ⟨16095753556715774437440709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21461004742287699249920945 16095753556715774437440709)
                    ·
                      refine ⟨3017953791884207707020133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16095753556715774437440709 3017953791884207707020133)
                      ·
                        rfl

theorem cell23_5877444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5877444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877444 prefixEnd_5877444 := by exact prefixLift 5877444
  have htrace : WordTrace (prefixWord ++ tailWord_5877444) baseStart_5877444 baseEnd_5877444 := by
    simpa [prefixWord, tailWord_5877444, baseEnd_5877444] using wordTrace_append hprefix tailTrace_5877444
  have hstable : (prefixWord ++ tailWord_5877444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877444).length < 2 ^ (prefixWord ++ tailWord_5877444).sum := by decide
  have hdescent : baseEnd_5877444 < baseStart_5877444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877464 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_5877464 : Nat := 118140960795 + 5877464 * 2 ^ 59
def prefixEnd_5877464 : Nat := 4983230072969 + 3 ^ 40 * 5877464 * 2
def baseEnd_5877464 : Nat := 3017964061497297628770041

theorem tailTrace_5877464 : CollatzResearch.WordTrace tailWord_5877464 prefixEnd_5877464 3017964061497297628770041 := by
  unfold tailWord_5877464
  simp only [CollatzResearch.WordTrace]
  refine ⟨107184361589479596890215723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142912482119306129186954297 107184361589479596890215723)
  ·
    refine ⟨160776542384219395335323585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107184361589479596890215723 160776542384219395335323585)
    ·
      refine ⟨120582406788164546501492689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160776542384219395335323585 120582406788164546501492689)
      ·
        refine ⟨90436805091123409876119517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120582406788164546501492689 90436805091123409876119517)
        ·
          refine ⟨33913801909171278703544819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90436805091123409876119517 33913801909171278703544819)
          ·
            refine ⟨50870702863756918055317229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33913801909171278703544819 50870702863756918055317229)
            ·
              refine ⟨19076513573908844270743961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50870702863756918055317229 19076513573908844270743961)
              ·
                refine ⟨14307385180431633203057971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19076513573908844270743961 14307385180431633203057971)
                ·
                  refine ⟨21461077770647449804586957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14307385180431633203057971 21461077770647449804586957)
                  ·
                    refine ⟨8047904163992793676720109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21461077770647449804586957 8047904163992793676720109)
                    ·
                      refine ⟨3017964061497297628770041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8047904163992793676720109 3017964061497297628770041)
                      ·
                        rfl

theorem cell23_5877464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_5877464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877464 prefixEnd_5877464 := by exact prefixLift 5877464
  have htrace : WordTrace (prefixWord ++ tailWord_5877464) baseStart_5877464 baseEnd_5877464 := by
    simpa [prefixWord, tailWord_5877464, baseEnd_5877464] using wordTrace_append hprefix tailTrace_5877464
  have hstable : (prefixWord ++ tailWord_5877464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877464).length < 2 ^ (prefixWord ++ tailWord_5877464).sum := by decide
  have hdescent : baseEnd_5877464 < baseStart_5877464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877468 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5877468 : Nat := 118140960795 + 5877468 * 2 ^ 59
def prefixEnd_5877468 : Nat := 4983230072969 + 3 ^ 40 * 5877468 * 2
def baseEnd_5877468 : Nat := 3017966115419915613120023

theorem tailTrace_5877468 : CollatzResearch.WordTrace tailWord_5877468 prefixEnd_5877468 3017966115419915613120023 := by
  unfold tailWord_5877468
  simp only [CollatzResearch.WordTrace]
  refine ⟨107184434535472351231788529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142912579380629801642384705 107184434535472351231788529)
  ·
    refine ⟨80388325901604263423841397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107184434535472351231788529 80388325901604263423841397)
    ·
      refine ⟨7536405553275399695985131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80388325901604263423841397 7536405553275399695985131)
      ·
        refine ⟨11304608329913099543977697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536405553275399695985131 11304608329913099543977697)
        ·
          refine ⟨8478456247434824657983273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11304608329913099543977697 8478456247434824657983273)
          ·
            refine ⟨6358842185576118493487455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8478456247434824657983273 6358842185576118493487455)
            ·
              refine ⟨9538263278364177740231183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6358842185576118493487455 9538263278364177740231183)
              ·
                refine ⟨14307394917546266610346775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9538263278364177740231183 14307394917546266610346775)
                ·
                  refine ⟨21461092376319399915520163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14307394917546266610346775 21461092376319399915520163)
                  ·
                    refine ⟨32191638564479099873280245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21461092376319399915520163 32191638564479099873280245)
                    ·
                      refine ⟨3017966115419915613120023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32191638564479099873280245 3017966115419915613120023)
                      ·
                        rfl

theorem cell23_5877468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5877468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877468 prefixEnd_5877468 := by exact prefixLift 5877468
  have htrace : WordTrace (prefixWord ++ tailWord_5877468) baseStart_5877468 baseEnd_5877468 := by
    simpa [prefixWord, tailWord_5877468, baseEnd_5877468] using wordTrace_append hprefix tailTrace_5877468
  have hstable : (prefixWord ++ tailWord_5877468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877468).length < 2 ^ (prefixWord ++ tailWord_5877468).sum := by decide
  have hdescent : baseEnd_5877468 < baseStart_5877468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877487 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_5877487 : Nat := 118140960795 + 5877487 * 2 ^ 59
def prefixEnd_5877487 : Nat := 4983230072969 + 3 ^ 40 * 5877487 * 2
def baseEnd_5877487 : Nat := 3017975871552351038782435

theorem tailTrace_5877487 : CollatzResearch.WordTrace tailWord_5877487 prefixEnd_5877487 3017975871552351038782435 := by
  unfold tailWord_5877487
  simp only [CollatzResearch.WordTrace]
  refine ⟨214369562057875868708518715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142913041371917245805679143 214369562057875868708518715)
  ·
    refine ⟨321554343086813803062778073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214369562057875868708518715 321554343086813803062778073)
    ·
      refine ⟨241165757315110352297083555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321554343086813803062778073 241165757315110352297083555)
      ·
        refine ⟨361748635972665528445625333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241165757315110352297083555 361748635972665528445625333)
        ·
          refine ⟨33913934622437393291777375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 361748635972665528445625333 33913934622437393291777375)
          ·
            refine ⟨50870901933656089937666063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33913934622437393291777375 50870901933656089937666063)
            ·
              refine ⟨76306352900484134906499095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50870901933656089937666063 76306352900484134906499095)
              ·
                refine ⟨114459529350726202359748643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76306352900484134906499095 114459529350726202359748643)
                ·
                  refine ⟨171689294026089303539622965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114459529350726202359748643 171689294026089303539622965)
                  ·
                    refine ⟨16095871314945872206839653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 171689294026089303539622965 16095871314945872206839653)
                    ·
                      refine ⟨3017975871552351038782435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16095871314945872206839653 3017975871552351038782435)
                      ·
                        rfl

theorem cell23_5877487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_5877487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877487 prefixEnd_5877487 := by exact prefixLift 5877487
  have htrace : WordTrace (prefixWord ++ tailWord_5877487) baseStart_5877487 baseEnd_5877487 := by
    simpa [prefixWord, tailWord_5877487, baseEnd_5877487] using wordTrace_append hprefix tailTrace_5877487
  have hstable : (prefixWord ++ tailWord_5877487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877487).length < 2 ^ (prefixWord ++ tailWord_5877487).sum := by decide
  have hdescent : baseEnd_5877487 < baseStart_5877487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877504 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 5, 4, 2]
def baseStart_5877504 : Nat := 118140960795 + 5877504 * 2 ^ 59
def prefixEnd_5877504 : Nat := 4983230072969 + 3 ^ 40 * 5877504 * 2
def baseEnd_5877504 : Nat := 3017984600723477472269857

theorem tailTrace_5877504 : CollatzResearch.WordTrace tailWord_5877504 prefixEnd_5877504 3017984600723477472269857 := by
  unfold tailWord_5877504
  simp only [CollatzResearch.WordTrace]
  refine ⟨107185091049407140305943783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142913454732542853741258377 107185091049407140305943783)
  ·
    refine ⟨160777636574110710458915675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107185091049407140305943783 160777636574110710458915675)
    ·
      refine ⟨241166454861166065688373513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160777636574110710458915675 241166454861166065688373513)
      ·
        refine ⟨180874841145874549266280135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241166454861166065688373513 180874841145874549266280135)
        ·
          refine ⟨271312261718811823899420203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180874841145874549266280135 271312261718811823899420203)
          ·
            refine ⟨406968392578217735849130305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271312261718811823899420203 406968392578217735849130305)
            ·
              refine ⟨305226294433663301886847729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406968392578217735849130305 305226294433663301886847729)
              ·
                refine ⟨228919720825247476415135797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305226294433663301886847729 228919720825247476415135797)
                ·
                  refine ⟨21461223827366950913918981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228919720825247476415135797 21461223827366950913918981)
                  ·
                    refine ⟨4023979467631303296359809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21461223827366950913918981 4023979467631303296359809)
                    ·
                      refine ⟨3017984600723477472269857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023979467631303296359809 3017984600723477472269857)
                      ·
                        rfl

theorem cell23_5877504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_5877504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877504 prefixEnd_5877504 := by exact prefixLift 5877504
  have htrace : WordTrace (prefixWord ++ tailWord_5877504) baseStart_5877504 baseEnd_5877504 := by
    simpa [prefixWord, tailWord_5877504, baseEnd_5877504] using wordTrace_append hprefix tailTrace_5877504
  have hstable : (prefixWord ++ tailWord_5877504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877504).length < 2 ^ (prefixWord ++ tailWord_5877504).sum := by decide
  have hdescent : baseEnd_5877504 < baseStart_5877504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877507 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5]
def baseStart_5877507 : Nat := 118140960795 + 5877507 * 2 ^ 59
def prefixEnd_5877507 : Nat := 4983230072969 + 3 ^ 40 * 5877507 * 2
def baseEnd_5877507 : Nat := 3017986141165440960532343

theorem tailTrace_5877507 : CollatzResearch.WordTrace tailWord_5877507 prefixEnd_5877507 3017986141165440960532343 := by
  unfold tailWord_5877507
  simp only [CollatzResearch.WordTrace]
  refine ⟨214370291517803412124246775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142913527678535608082831183 214370291517803412124246775)
  ·
    refine ⟨321555437276705118186370163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214370291517803412124246775 321555437276705118186370163)
    ·
      refine ⟨482333155915057677279555245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321555437276705118186370163 482333155915057677279555245)
      ·
        refine ⟨180874933468146628979833217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 482333155915057677279555245 180874933468146628979833217)
        ·
          refine ⟨135656200101109971734874913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180874933468146628979833217 135656200101109971734874913)
          ·
            refine ⟨101742150075832478801156185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135656200101109971734874913 101742150075832478801156185)
            ·
              refine ⟨76306612556874359100867139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101742150075832478801156185 76306612556874359100867139)
              ·
                refine ⟨114459918835311538651300709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76306612556874359100867139 114459918835311538651300709)
                ·
                  refine ⟨21461234781620913497118883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114459918835311538651300709 21461234781620913497118883)
                  ·
                    refine ⟨32191852172431370245678325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21461234781620913497118883 32191852172431370245678325)
                    ·
                      refine ⟨3017986141165440960532343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32191852172431370245678325 3017986141165440960532343)
                      ·
                        rfl

theorem cell23_5877507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_5877507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877507 prefixEnd_5877507 := by exact prefixLift 5877507
  have htrace : WordTrace (prefixWord ++ tailWord_5877507) baseStart_5877507 baseEnd_5877507 := by
    simpa [prefixWord, tailWord_5877507, baseEnd_5877507] using wordTrace_append hprefix tailTrace_5877507
  have hstable : (prefixWord ++ tailWord_5877507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877507).length < 2 ^ (prefixWord ++ tailWord_5877507).sum := by decide
  have hdescent : baseEnd_5877507 < baseStart_5877507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877521 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 4, 2, 2]
def baseStart_5877521 : Nat := 118140960795 + 5877521 * 2 ^ 59
def prefixEnd_5877521 : Nat := 4983230072969 + 3 ^ 40 * 5877521 * 2
def baseEnd_5877521 : Nat := 3017993329894603905757279

theorem tailTrace_5877521 : CollatzResearch.WordTrace tailWord_5877521 prefixEnd_5877521 3017993329894603905757279 := by
  unfold tailWord_5877521
  simp only [CollatzResearch.WordTrace]
  refine ⟨214370802139752692515256417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142913868093168461676837611 214370802139752692515256417)
  ·
    refine ⟨160778101604814519386442313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214370802139752692515256417 160778101604814519386442313)
    ·
      refine ⟨120583576203610889539831735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160778101604814519386442313 120583576203610889539831735)
      ·
        refine ⟨180875364305416334309747603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120583576203610889539831735 180875364305416334309747603)
        ·
          refine ⟨271313046458124501464621405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180875364305416334309747603 271313046458124501464621405)
          ·
            refine ⟨101742392421796688049233027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271313046458124501464621405 101742392421796688049233027)
            ·
              refine ⟨152613588632695032073849541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101742392421796688049233027 152613588632695032073849541)
              ·
                refine ⟨28615047868630318513846789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152613588632695032073849541 28615047868630318513846789)
                ·
                  refine ⟨5365321475368184721346273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28615047868630318513846789 5365321475368184721346273)
                  ·
                    refine ⟨4023991106526138541009705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5365321475368184721346273 4023991106526138541009705)
                    ·
                      refine ⟨3017993329894603905757279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023991106526138541009705 3017993329894603905757279)
                      ·
                        rfl

theorem cell23_5877521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_5877521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877521 prefixEnd_5877521 := by exact prefixLift 5877521
  have htrace : WordTrace (prefixWord ++ tailWord_5877521) baseStart_5877521 baseEnd_5877521 := by
    simpa [prefixWord, tailWord_5877521, baseEnd_5877521] using wordTrace_append hprefix tailTrace_5877521
  have hstable : (prefixWord ++ tailWord_5877521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877521).length < 2 ^ (prefixWord ++ tailWord_5877521).sum := by decide
  have hdescent : baseEnd_5877521 < baseStart_5877521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877525 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_5877525 : Nat := 118140960795 + 5877525 * 2 ^ 59
def prefixEnd_5877525 : Nat := 4983230072969 + 3 ^ 40 * 5877525 * 2
def baseEnd_5877525 : Nat := 3017995383817221890107261

theorem tailTrace_5877525 : CollatzResearch.WordTrace tailWord_5877525 prefixEnd_5877525 3017995383817221890107261 := by
  unfold tailWord_5877525
  simp only [CollatzResearch.WordTrace]
  refine ⟨214370948031738201198402029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142913965354492134132268019 214370948031738201198402029)
  ·
    refine ⟨80389105511901825449400761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214370948031738201198402029 80389105511901825449400761)
    ·
      refine ⟨60291829133926369087050571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80389105511901825449400761 60291829133926369087050571)
      ·
        refine ⟨90437743700889553630575857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60291829133926369087050571 90437743700889553630575857)
        ·
          refine ⟨67828307775667165222931893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90437743700889553630575857 67828307775667165222931893)
          ·
            refine ⟨6358903853968796739649865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67828307775667165222931893 6358903853968796739649865)
            ·
              refine ⟨4769177890476597554737399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6358903853968796739649865 4769177890476597554737399)
              ·
                refine ⟨7153766835714896332106099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769177890476597554737399 7153766835714896332106099)
                ·
                  refine ⟨10730650253572344498159149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7153766835714896332106099 10730650253572344498159149)
                  ·
                    refine ⟨4023993845089629186809681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10730650253572344498159149 4023993845089629186809681)
                    ·
                      refine ⟨3017995383817221890107261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4023993845089629186809681 3017995383817221890107261)
                      ·
                        rfl

theorem cell23_5877525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_5877525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877525 prefixEnd_5877525 := by exact prefixLift 5877525
  have htrace : WordTrace (prefixWord ++ tailWord_5877525) baseStart_5877525 baseEnd_5877525 := by
    simpa [prefixWord, tailWord_5877525, baseEnd_5877525] using wordTrace_append hprefix tailTrace_5877525
  have hstable : (prefixWord ++ tailWord_5877525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877525).length < 2 ^ (prefixWord ++ tailWord_5877525).sum := by decide
  have hdescent : baseEnd_5877525 < baseStart_5877525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877538 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_5877538 : Nat := 118140960795 + 5877538 * 2 ^ 59
def prefixEnd_5877538 : Nat := 4983230072969 + 3 ^ 40 * 5877538 * 2
def baseEnd_5877538 : Nat := 3018002059065730339244701

theorem tailTrace_5877538 : CollatzResearch.WordTrace tailWord_5877538 prefixEnd_5877538 3018002059065730339244701 := by
  unfold tailWord_5877538
  simp only [CollatzResearch.WordTrace]
  refine ⟨53592855545172776104656317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142914281453794069612416845 53592855545172776104656317)
  ·
    refine ⟨20097320829439791039246119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53592855545172776104656317 20097320829439791039246119)
    ·
      refine ⟨30145981244159686558869179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20097320829439791039246119 30145981244159686558869179)
      ·
        refine ⟨45218971866239529838303769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30145981244159686558869179 45218971866239529838303769)
        ·
          refine ⟨33914228899679647378727827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45218971866239529838303769 33914228899679647378727827)
          ·
            refine ⟨50871343349519471068091741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33914228899679647378727827 50871343349519471068091741)
            ·
              refine ⟨19076753756069801650534403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50871343349519471068091741 19076753756069801650534403)
              ·
                refine ⟨28615130634104702475801605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19076753756069801650534403 28615130634104702475801605)
                ·
                  refine ⟨5365336993894631714212801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28615130634104702475801605 5365336993894631714212801)
                  ·
                    refine ⟨4024002745420973785659601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5365336993894631714212801 4024002745420973785659601)
                    ·
                      refine ⟨3018002059065730339244701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024002745420973785659601 3018002059065730339244701)
                      ·
                        rfl

theorem cell23_5877538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_5877538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877538 prefixEnd_5877538 := by exact prefixLift 5877538
  have htrace : WordTrace (prefixWord ++ tailWord_5877538) baseStart_5877538 baseEnd_5877538 := by
    simpa [prefixWord, tailWord_5877538, baseEnd_5877538] using wordTrace_append hprefix tailTrace_5877538
  have hstable : (prefixWord ++ tailWord_5877538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877538).length < 2 ^ (prefixWord ++ tailWord_5877538).sum := by decide
  have hdescent : baseEnd_5877538 < baseStart_5877538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877544 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 7]
def baseStart_5877544 : Nat := 118140960795 + 5877544 * 2 ^ 59
def prefixEnd_5877544 : Nat := 4983230072969 + 3 ^ 40 * 5877544 * 2
def baseEnd_5877544 : Nat := 335333904438850812863297

theorem tailTrace_5877544 : CollatzResearch.WordTrace tailWord_5877544 prefixEnd_5877544 335333904438850812863297 := by
  unfold tailWord_5877544
  simp only [CollatzResearch.WordTrace]
  refine ⟨107185820509334683721671843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142914427345779578295562457 107185820509334683721671843)
  ·
    refine ⟨160778730764002025582507765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107185820509334683721671843 160778730764002025582507765)
    ·
      refine ⟨15073006009125189898360103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160778730764002025582507765 15073006009125189898360103)
      ·
        refine ⟨22609509013687784847540155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15073006009125189898360103 22609509013687784847540155)
        ·
          refine ⟨33914263520531677271310233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22609509013687784847540155 33914263520531677271310233)
          ·
            refine ⟨25435697640398757953482675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33914263520531677271310233 25435697640398757953482675)
            ·
              refine ⟨38153546460598136930224013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25435697640398757953482675 38153546460598136930224013)
              ·
                refine ⟨14307579922724301348834005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38153546460598136930224013 14307579922724301348834005)
                ·
                  refine ⟨335333904438850812863297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14307579922724301348834005 335333904438850812863297)
                  ·
                    rfl

theorem cell23_5877544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_5877544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877544 prefixEnd_5877544 := by exact prefixLift 5877544
  have htrace : WordTrace (prefixWord ++ tailWord_5877544) baseStart_5877544 baseEnd_5877544 := by
    simpa [prefixWord, tailWord_5877544, baseEnd_5877544] using wordTrace_append hprefix tailTrace_5877544
  have hstable : (prefixWord ++ tailWord_5877544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877544).length < 2 ^ (prefixWord ++ tailWord_5877544).sum := by decide
  have hdescent : baseEnd_5877544 < baseStart_5877544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877555 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 1, 4, 2]
def baseStart_5877555 : Nat := 118140960795 + 5877555 * 2 ^ 59
def prefixEnd_5877555 : Nat := 4983230072969 + 3 ^ 40 * 5877555 * 2
def baseEnd_5877555 : Nat := 3018010788236856772732123

theorem tailTrace_5877555 : CollatzResearch.WordTrace tailWord_5877555 prefixEnd_5877555 3018010788236856772732123 := by
  unfold tailWord_5877555
  simp only [CollatzResearch.WordTrace]
  refine ⟨214372042221629516321994119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142914694814419677547996079 214372042221629516321994119)
  ·
    refine ⟨321558063332444274482991179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214372042221629516321994119 321558063332444274482991179)
    ·
      refine ⟨482337094998666411724486769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321558063332444274482991179 482337094998666411724486769)
      ·
        refine ⟨361752821248999808793365077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482337094998666411724486769 361752821248999808793365077)
        ·
          refine ⟨4239290874011716509297247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 361752821248999808793365077 4239290874011716509297247)
          ·
            refine ⟨6358936311017574763945871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239290874011716509297247 6358936311017574763945871)
            ·
              refine ⟨9538404466526362145918807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6358936311017574763945871 9538404466526362145918807)
              ·
                refine ⟨14307606699789543218878211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9538404466526362145918807 14307606699789543218878211)
                ·
                  refine ⟨21461410049684314828317317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14307606699789543218878211 21461410049684314828317317)
                  ·
                    refine ⟨4024014384315809030309497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21461410049684314828317317 4024014384315809030309497)
                    ·
                      refine ⟨3018010788236856772732123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024014384315809030309497 3018010788236856772732123)
                      ·
                        rfl

theorem cell23_5877555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 4, 2].length) (baseStart_5877555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877555 prefixEnd_5877555 := by exact prefixLift 5877555
  have htrace : WordTrace (prefixWord ++ tailWord_5877555) baseStart_5877555 baseEnd_5877555 := by
    simpa [prefixWord, tailWord_5877555, baseEnd_5877555] using wordTrace_append hprefix tailTrace_5877555
  have hstable : (prefixWord ++ tailWord_5877555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877555).length < 2 ^ (prefixWord ++ tailWord_5877555).sum := by decide
  have hdescent : baseEnd_5877555 < baseStart_5877555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877591 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 2, 5]
def baseStart_5877591 : Nat := 118140960795 + 5877591 * 2 ^ 59
def prefixEnd_5877591 : Nat := 4983230072969 + 3 ^ 40 * 5877591 * 2
def baseEnd_5877591 : Nat := 1006009757846806210627319

theorem tailTrace_5877591 : CollatzResearch.WordTrace tailWord_5877591 prefixEnd_5877591 1006009757846806210627319 := by
  unfold tailWord_5877591
  simp only [CollatzResearch.WordTrace]
  refine ⟨214373355249499094470304627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142915570166332729646869751 214373355249499094470304627)
  ·
    refine ⟨321560032874248641705456941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214373355249499094470304627 321560032874248641705456941)
    ·
      refine ⟨120585012327843240639546353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321560032874248641705456941 120585012327843240639546353)
      ·
        refine ⟨90438759245882430479659765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120585012327843240639546353 90438759245882430479659765)
        ·
          refine ⟨8478633679301477857468103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90438759245882430479659765 8478633679301477857468103)
          ·
            refine ⟨12717950518952216786202155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8478633679301477857468103 12717950518952216786202155)
            ·
              refine ⟨19076925778428325179303233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12717950518952216786202155 19076925778428325179303233)
              ·
                refine ⟨14307694333821243884477425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19076925778428325179303233 14307694333821243884477425)
                ·
                  refine ⟨10730770750365932913358069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14307694333821243884477425 10730770750365932913358069)
                  ·
                    refine ⟨1006009757846806210627319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10730770750365932913358069 1006009757846806210627319)
                    ·
                      rfl

theorem cell23_5877591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_5877591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877591 prefixEnd_5877591 := by exact prefixLift 5877591
  have htrace : WordTrace (prefixWord ++ tailWord_5877591) baseStart_5877591 baseEnd_5877591 := by
    simpa [prefixWord, tailWord_5877591, baseEnd_5877591] using wordTrace_append hprefix tailTrace_5877591
  have hstable : (prefixWord ++ tailWord_5877591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877591).length < 2 ^ (prefixWord ++ tailWord_5877591).sum := by decide
  have hdescent : baseEnd_5877591 < baseStart_5877591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877621 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5877621 : Nat := 118140960795 + 5877621 * 2 ^ 59
def prefixEnd_5877621 : Nat := 4983230072969 + 3 ^ 40 * 5877621 * 2
def baseEnd_5877621 : Nat := 1006014892653351171502273

theorem tailTrace_5877621 : CollatzResearch.WordTrace tailWord_5877621 prefixEnd_5877621 1006014892653351171502273 := by
  unfold tailWord_5877621
  simp only [CollatzResearch.WordTrace]
  refine ⟨214374449439390409593896717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142916299626260273062597811 214374449439390409593896717)
  ·
    refine ⟨80390418539771403597711269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214374449439390409593896717 80390418539771403597711269)
    ·
      refine ⟨15073203476207138174570863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80390418539771403597711269 15073203476207138174570863)
      ·
        refine ⟨22609805214310707261856295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15073203476207138174570863 22609805214310707261856295)
        ·
          refine ⟨33914707821466060892784443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22609805214310707261856295 33914707821466060892784443)
          ·
            refine ⟨50872061732199091339176665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33914707821466060892784443 50872061732199091339176665)
            ·
              refine ⟨38154046299149318504382499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50872061732199091339176665 38154046299149318504382499)
              ·
                refine ⟨57231069448723977756573749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38154046299149318504382499 57231069448723977756573749)
                ·
                  refine ⟨5365412760817872914678789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57231069448723977756573749 5365412760817872914678789)
                  ·
                    refine ⟨1006014892653351171502273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365412760817872914678789 1006014892653351171502273)
                    ·
                      rfl

theorem cell23_5877621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5877621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877621 prefixEnd_5877621 := by exact prefixLift 5877621
  have htrace : WordTrace (prefixWord ++ tailWord_5877621) baseStart_5877621 baseEnd_5877621 := by
    simpa [prefixWord, tailWord_5877621, baseEnd_5877621] using wordTrace_append hprefix tailTrace_5877621
  have hstable : (prefixWord ++ tailWord_5877621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877621).length < 2 ^ (prefixWord ++ tailWord_5877621).sum := by decide
  have hdescent : baseEnd_5877621 < baseStart_5877621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877655 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 1, 4]
def baseStart_5877655 : Nat := 118140960795 + 5877655 * 2 ^ 59
def prefixEnd_5877655 : Nat := 4983230072969 + 3 ^ 40 * 5877655 * 2
def baseEnd_5877655 : Nat := 1006020712100768793827221

theorem tailTrace_5877655 : CollatzResearch.WordTrace tailWord_5877655 prefixEnd_5877655 1006020712100768793827221 := by
  unfold tailWord_5877655
  simp only [CollatzResearch.WordTrace]
  refine ⟨214375689521267233400634419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142917126347511488933756279 214375689521267233400634419)
  ·
    refine ⟨321563534281900850100951629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214375689521267233400634419 321563534281900850100951629)
    ·
      refine ⟨120586325355712818787856861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321563534281900850100951629 120586325355712818787856861)
      ·
        refine ⟨45219872008392307045446323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120586325355712818787856861 45219872008392307045446323)
        ·
          refine ⟨67829808012588460568169485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45219872008392307045446323 67829808012588460568169485)
          ·
            refine ⟨25436178004720672713063557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67829808012588460568169485 25436178004720672713063557)
            ·
              refine ⟨4769283375885126133699417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25436178004720672713063557 4769283375885126133699417)
              ·
                refine ⟨3576962531913844600274563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769283375885126133699417 3576962531913844600274563)
                ·
                  refine ⟨5365443797870766900411845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576962531913844600274563 5365443797870766900411845)
                  ·
                    refine ⟨1006020712100768793827221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365443797870766900411845 1006020712100768793827221)
                    ·
                      rfl

theorem cell23_5877655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_5877655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877655 prefixEnd_5877655 := by exact prefixLift 5877655
  have htrace : WordTrace (prefixWord ++ tailWord_5877655) baseStart_5877655 baseEnd_5877655 := by
    simpa [prefixWord, tailWord_5877655, baseEnd_5877655] using wordTrace_append hprefix tailTrace_5877655
  have hstable : (prefixWord ++ tailWord_5877655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877655).length < 2 ^ (prefixWord ++ tailWord_5877655).sum := by decide
  have hdescent : baseEnd_5877655 < baseStart_5877655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877662 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5877662 : Nat := 118140960795 + 5877662 * 2 ^ 59
def prefixEnd_5877662 : Nat := 4983230072969 + 3 ^ 40 * 5877662 * 2
def baseEnd_5877662 : Nat := 3018065730666887854094131

theorem tailTrace_5877662 : CollatzResearch.WordTrace tailWord_5877662 prefixEnd_5877662 3018065730666887854094131 := by
  unfold tailWord_5877662
  simp only [CollatzResearch.WordTrace]
  refine ⟨26796993104030234199517405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142917296554827915730759493 26796993104030234199517405)
  ·
    refine ⟨10048872414011337824819027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26796993104030234199517405 10048872414011337824819027)
    ·
      refine ⟨15073308621017006737228541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10048872414011337824819027 15073308621017006737228541)
      ·
        refine ⟨5652490732881377526460703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15073308621017006737228541 5652490732881377526460703)
        ·
          refine ⟨8478736099322066289691055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652490732881377526460703 8478736099322066289691055)
          ·
            refine ⟨12718104148983099434536583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8478736099322066289691055 12718104148983099434536583)
            ·
              refine ⟨19077156223474649151804875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12718104148983099434536583 19077156223474649151804875)
              ·
                refine ⟨28615734335211973727707313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19077156223474649151804875 28615734335211973727707313)
                ·
                  refine ⟨21461800751408980295780485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28615734335211973727707313 21461800751408980295780485)
                  ·
                    refine ⟨4024087640889183805458841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21461800751408980295780485 4024087640889183805458841)
                    ·
                      refine ⟨3018065730666887854094131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024087640889183805458841 3018065730666887854094131)
                      ·
                        rfl

theorem cell23_5877662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5877662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877662 prefixEnd_5877662 := by exact prefixLift 5877662
  have htrace : WordTrace (prefixWord ++ tailWord_5877662) baseStart_5877662 baseEnd_5877662 := by
    simpa [prefixWord, tailWord_5877662, baseEnd_5877662] using wordTrace_append hprefix tailTrace_5877662
  have hstable : (prefixWord ++ tailWord_5877662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877662).length < 2 ^ (prefixWord ++ tailWord_5877662).sum := by decide
  have hdescent : baseEnd_5877662 < baseStart_5877662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877681 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_5877681 : Nat := 118140960795 + 5877681 * 2 ^ 59
def prefixEnd_5877681 : Nat := 4983230072969 + 3 ^ 40 * 5877681 * 2
def baseEnd_5877681 : Nat := 1006025162266441093252181

theorem tailTrace_5877681 : CollatzResearch.WordTrace tailWord_5877681 prefixEnd_5877681 1006025162266441093252181 := by
  unfold tailWord_5877681
  simp only [CollatzResearch.WordTrace]
  refine ⟨214376637819173039841080897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142917758546115359894053931 214376637819173039841080897)
  ·
    refine ⟨160782478364379779880810673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214376637819173039841080897 160782478364379779880810673)
    ·
      refine ⟨120586858773284834910608005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160782478364379779880810673 120586858773284834910608005)
      ·
        refine ⟨22610036019990906545739001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120586858773284834910608005 22610036019990906545739001)
        ·
          refine ⟨16957527014993179909304251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22610036019990906545739001 16957527014993179909304251)
          ·
            refine ⟨25436290522489769863956377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16957527014993179909304251 25436290522489769863956377)
            ·
              refine ⟨19077217891867327397967283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25436290522489769863956377 19077217891867327397967283)
              ·
                refine ⟨28615826837800991096950925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19077217891867327397967283 28615826837800991096950925)
                ·
                  refine ⟨10730935064175371661356597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28615826837800991096950925 10730935064175371661356597)
                  ·
                    refine ⟨1006025162266441093252181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10730935064175371661356597 1006025162266441093252181)
                    ·
                      rfl

theorem cell23_5877681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_5877681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877681 prefixEnd_5877681 := by exact prefixLift 5877681
  have htrace : WordTrace (prefixWord ++ tailWord_5877681) baseStart_5877681 baseEnd_5877681 := by
    simpa [prefixWord, tailWord_5877681, baseEnd_5877681] using wordTrace_append hprefix tailTrace_5877681
  have hstable : (prefixWord ++ tailWord_5877681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877681).length < 2 ^ (prefixWord ++ tailWord_5877681).sum := by decide
  have hdescent : baseEnd_5877681 < baseStart_5877681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877695 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 1, 1, 3]
def baseStart_5877695 : Nat := 118140960795 + 5877695 * 2 ^ 59
def prefixEnd_5877695 : Nat := 4983230072969 + 3 ^ 40 * 5877695 * 2
def baseEnd_5877695 : Nat := 3018082675528486224981479

theorem tailTrace_5877695 : CollatzResearch.WordTrace tailWord_5877695 prefixEnd_5877695 3018082675528486224981479 := by
  unfold tailWord_5877695
  simp only [CollatzResearch.WordTrace]
  refine ⟨214377148441122320232090539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142918098960748213488060359 214377148441122320232090539)
  ·
    refine ⟨321565722661683480348135809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214377148441122320232090539 321565722661683480348135809)
    ·
      refine ⟨241174291996262610261101857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321565722661683480348135809 241174291996262610261101857)
      ·
        refine ⟨180880718997196957695826393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241174291996262610261101857 180880718997196957695826393)
        ·
          refine ⟨135660539247897718271869795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180880718997196957695826393 135660539247897718271869795)
          ·
            refine ⟨203490808871846577407804693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135660539247897718271869795 203490808871846577407804693)
            ·
              refine ⟨9538631665867808315990845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 203490808871846577407804693 9538631665867808315990845)
              ·
                refine ⟨3576986874700428118496567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9538631665867808315990845 3576986874700428118496567)
                ·
                  refine ⟨5365480312050642177744851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576986874700428118496567 5365480312050642177744851)
                  ·
                    refine ⟨8048220468075963266617277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365480312050642177744851 8048220468075963266617277)
                    ·
                      refine ⟨3018082675528486224981479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8048220468075963266617277 3018082675528486224981479)
                      ·
                        rfl

theorem cell23_5877695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_5877695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877695 prefixEnd_5877695 := by exact prefixLift 5877695
  have htrace : WordTrace (prefixWord ++ tailWord_5877695) baseStart_5877695 baseEnd_5877695 := by
    simpa [prefixWord, tailWord_5877695, baseEnd_5877695] using wordTrace_append hprefix tailTrace_5877695
  have hstable : (prefixWord ++ tailWord_5877695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877695).length < 2 ^ (prefixWord ++ tailWord_5877695).sum := by decide
  have hdescent : baseEnd_5877695 < baseStart_5877695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877711 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 4, 4]
def baseStart_5877711 : Nat := 118140960795 + 5877711 * 2 ^ 59
def prefixEnd_5877711 : Nat := 4983230072969 + 3 ^ 40 * 5877711 * 2
def baseEnd_5877711 : Nat := 1006030297072986054127135

theorem tailTrace_5877711 : CollatzResearch.WordTrace tailWord_5877711 prefixEnd_5877711 1006030297072986054127135 := by
  unfold tailWord_5877711
  simp only [CollatzResearch.WordTrace]
  refine ⟨214377732009064354964672987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142918488006042903309781991 214377732009064354964672987)
  ·
    refine ⟨321566598013596532447009481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214377732009064354964672987 321566598013596532447009481)
    ·
      refine ⟨241174948510197399335257111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321566598013596532447009481 241174948510197399335257111)
      ·
        refine ⟨361762422765296099002885667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241174948510197399335257111 361762422765296099002885667)
        ·
          refine ⟨542643634147944148504328501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361762422765296099002885667 542643634147944148504328501)
          ·
            refine ⟨50872840701369763922280797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 542643634147944148504328501 50872840701369763922280797)
            ·
              refine ⟨19077315263013661470855299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50872840701369763922280797 19077315263013661470855299)
              ·
                refine ⟨28615972894520492206282949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19077315263013661470855299 28615972894520492206282949)
                ·
                  refine ⟨5365494917722592288678053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28615972894520492206282949 5365494917722592288678053)
                  ·
                    refine ⟨1006030297072986054127135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365494917722592288678053 1006030297072986054127135)
                    ·
                      rfl

theorem cell23_5877711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 4].length) (baseStart_5877711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877711 prefixEnd_5877711 := by exact prefixLift 5877711
  have htrace : WordTrace (prefixWord ++ tailWord_5877711) baseStart_5877711 baseEnd_5877711 := by
    simpa [prefixWord, tailWord_5877711, baseEnd_5877711] using wordTrace_append hprefix tailTrace_5877711
  have hstable : (prefixWord ++ tailWord_5877711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877711).length < 2 ^ (prefixWord ++ tailWord_5877711).sum := by decide
  have hdescent : baseEnd_5877711 < baseStart_5877711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877731 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5877731 : Nat := 118140960795 + 5877731 * 2 ^ 59
def prefixEnd_5877731 : Nat := 4983230072969 + 3 ^ 40 * 5877731 * 2
def baseEnd_5877731 : Nat := 3018101160832048084131313

theorem tailTrace_5877731 : CollatzResearch.WordTrace tailWord_5877731 prefixEnd_5877731 3018101160832048084131313 := by
  unfold tailWord_5877731
  simp only [CollatzResearch.WordTrace]
  refine ⟨214378461468991898380401047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142918974312661265586934031 214378461468991898380401047)
  ·
    refine ⟨321567692203487847570601571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214378461468991898380401047 321567692203487847570601571)
    ·
      refine ⟨482351538305231771355902357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321567692203487847570601571 482351538305231771355902357)
      ·
        refine ⟨22610228358057739282307923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 482351538305231771355902357 22610228358057739282307923)
        ·
          refine ⟨33915342537086608923461885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22610228358057739282307923 33915342537086608923461885)
          ·
            refine ⟨12718253451407478346298207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33915342537086608923461885 12718253451407478346298207)
            ·
              refine ⟨19077380177111217519447311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12718253451407478346298207 19077380177111217519447311)
              ·
                refine ⟨28616070265666826279170967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19077380177111217519447311 28616070265666826279170967)
                ·
                  refine ⟨42924105398500239418756451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28616070265666826279170967 42924105398500239418756451)
                  ·
                    refine ⟨64386158097750359128134677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42924105398500239418756451 64386158097750359128134677)
                    ·
                      refine ⟨3018101160832048084131313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64386158097750359128134677 3018101160832048084131313)
                      ·
                        rfl

theorem cell23_5877731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5877731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877731 prefixEnd_5877731 := by exact prefixLift 5877731
  have htrace : WordTrace (prefixWord ++ tailWord_5877731) baseStart_5877731 baseEnd_5877731 := by
    simpa [prefixWord, tailWord_5877731, baseEnd_5877731] using wordTrace_append hprefix tailTrace_5877731
  have hstable : (prefixWord ++ tailWord_5877731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877731).length < 2 ^ (prefixWord ++ tailWord_5877731).sum := by decide
  have hdescent : baseEnd_5877731 < baseStart_5877731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877735 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5877735 : Nat := 118140960795 + 5877735 * 2 ^ 59
def prefixEnd_5877735 : Nat := 4983230072969 + 3 ^ 40 * 5877735 * 2
def baseEnd_5877735 : Nat := 3018103214754666068481295

theorem tailTrace_5877735 : CollatzResearch.WordTrace tailWord_5877735 prefixEnd_5877735 3018103214754666068481295 := by
  unfold tailWord_5877735
  simp only [CollatzResearch.WordTrace]
  refine ⟨214378607360977407063546659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142919071573984938042364439 214378607360977407063546659)
  ·
    refine ⟨321567911041466110595319989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214378607360977407063546659 321567911041466110595319989)
    ·
      refine ⟨30146991660137447868311249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 321567911041466110595319989 30146991660137447868311249)
      ·
        refine ⟨22610243745103085901233437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30146991660137447868311249 22610243745103085901233437)
        ·
          refine ⟨8478841404413657212962539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22610243745103085901233437 8478841404413657212962539)
          ·
            refine ⟨12718262106620485819443809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8478841404413657212962539 12718262106620485819443809)
            ·
              refine ⟨9538696579965364364582857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12718262106620485819443809 9538696579965364364582857)
              ·
                refine ⟨7154022434974023273437143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9538696579965364364582857 7154022434974023273437143)
                ·
                  refine ⟨10731033652461034910155715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7154022434974023273437143 10731033652461034910155715)
                  ·
                    refine ⟨16096550478691552365233573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10731033652461034910155715 16096550478691552365233573)
                    ·
                      refine ⟨3018103214754666068481295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16096550478691552365233573 3018103214754666068481295)
                      ·
                        rfl

theorem cell23_5877735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5877735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877735 prefixEnd_5877735 := by exact prefixLift 5877735
  have htrace : WordTrace (prefixWord ++ tailWord_5877735) baseStart_5877735 baseEnd_5877735 := by
    simpa [prefixWord, tailWord_5877735, baseEnd_5877735] using wordTrace_append hprefix tailTrace_5877735
  have hstable : (prefixWord ++ tailWord_5877735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877735).length < 2 ^ (prefixWord ++ tailWord_5877735).sum := by decide
  have hdescent : baseEnd_5877735 < baseStart_5877735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877752 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 1, 2, 2]
def baseStart_5877752 : Nat := 118140960795 + 5877752 * 2 ^ 59
def prefixEnd_5877752 : Nat := 4983230072969 + 3 ^ 40 * 5877752 * 2
def baseEnd_5877752 : Nat := 3018111943925792501968717

theorem tailTrace_5877752 : CollatzResearch.WordTrace tailWord_5877752 prefixEnd_5877752 3018111943925792501968717 := by
  unfold tailWord_5877752
  simp only [CollatzResearch.WordTrace]
  refine ⟨107189613700957909483457755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142919484934610545977943673 107189613700957909483457755)
  ·
    refine ⟨160784420551436864225186633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107189613700957909483457755 160784420551436864225186633)
    ·
      refine ⟨120588315413577648168889975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160784420551436864225186633 120588315413577648168889975)
      ·
        refine ⟨180882473120366472253334963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120588315413577648168889975 180882473120366472253334963)
        ·
          refine ⟨271323709680549708380002445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180882473120366472253334963 271323709680549708380002445)
          ·
            refine ⟨101746391130206140642500917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271323709680549708380002445 101746391130206140642500917)
            ·
              refine ⟨9538724168456825685234461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101746391130206140642500917 9538724168456825685234461)
              ·
                refine ⟨3577021563171309631962923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9538724168456825685234461 3577021563171309631962923)
                ·
                  refine ⟨5365532344756964447944385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577021563171309631962923 5365532344756964447944385)
                  ·
                    refine ⟨4024149258567723335958289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5365532344756964447944385 4024149258567723335958289)
                    ·
                      refine ⟨3018111943925792501968717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024149258567723335958289 3018111943925792501968717)
                      ·
                        rfl

theorem cell23_5877752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_5877752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877752 prefixEnd_5877752 := by exact prefixLift 5877752
  have htrace : WordTrace (prefixWord ++ tailWord_5877752) baseStart_5877752 baseEnd_5877752 := by
    simpa [prefixWord, tailWord_5877752, baseEnd_5877752] using wordTrace_append hprefix tailTrace_5877752
  have hstable : (prefixWord ++ tailWord_5877752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877752).length < 2 ^ (prefixWord ++ tailWord_5877752).sum := by decide
  have hdescent : baseEnd_5877752 < baseStart_5877752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877754 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_5877754 : Nat := 118140960795 + 5877754 * 2 ^ 59
def prefixEnd_5877754 : Nat := 4983230072969 + 3 ^ 40 * 5877754 * 2
def baseEnd_5877754 : Nat := 1006037656962367164714569

theorem tailTrace_5877754 : CollatzResearch.WordTrace tailWord_5877754 prefixEnd_5877754 1006037656962367164714569 := by
  unfold tailWord_5877754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53594825086977143327122079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142919533565272382205658877 53594825086977143327122079)
  ·
    refine ⟨80392237630465714990683119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53594825086977143327122079 80392237630465714990683119)
    ·
      refine ⟨120588356445698572486024679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80392237630465714990683119 120588356445698572486024679)
      ·
        refine ⟨180882534668547858729037019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120588356445698572486024679 180882534668547858729037019)
        ·
          refine ⟨271323802002821788093555529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180882534668547858729037019 271323802002821788093555529)
          ·
            refine ⟨203492851502116341070166647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271323802002821788093555529 203492851502116341070166647)
            ·
              refine ⟨305239277253174511605249971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203492851502116341070166647 305239277253174511605249971)
              ·
                refine ⟨457858915879761767407874957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305239277253174511605249971 457858915879761767407874957)
                ·
                  refine ⟨171697093454910662777953109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457858915879761767407874957 171697093454910662777953109)
                  ·
                    refine ⟨1006037656962367164714569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171697093454910662777953109 1006037656962367164714569)
                    ·
                      rfl

theorem cell23_5877754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_5877754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877754 prefixEnd_5877754 := by exact prefixLift 5877754
  have htrace : WordTrace (prefixWord ++ tailWord_5877754) baseStart_5877754 baseEnd_5877754 := by
    simpa [prefixWord, tailWord_5877754, baseEnd_5877754] using wordTrace_append hprefix tailTrace_5877754
  have hstable : (prefixWord ++ tailWord_5877754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877754).length < 2 ^ (prefixWord ++ tailWord_5877754).sum := by decide
  have hdescent : baseEnd_5877754 < baseStart_5877754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877758 : List Nat := [4, 2, 2, 2, 1, 3, 9]
def baseStart_5877758 : Nat := 118140960795 + 5877758 * 2 ^ 59
def prefixEnd_5877758 : Nat := 4983230072969 + 3 ^ 40 * 5877758 * 2
def baseEnd_5877758 : Nat := 37260679318638512080169

theorem tailTrace_5877758 : CollatzResearch.WordTrace tailWord_5877758 prefixEnd_5877758 37260679318638512080169 := by
  unfold tailWord_5877758
  simp only [CollatzResearch.WordTrace]
  refine ⟨26797430779986760248954241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142919630826596054661089285 26797430779986760248954241)
  ·
    refine ⟨20098073084990070186715681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26797430779986760248954241 20098073084990070186715681)
    ·
      refine ⟨15073554813742552640036761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20098073084990070186715681 15073554813742552640036761)
      ·
        refine ⟨11305166110306914480027571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15073554813742552640036761 11305166110306914480027571)
        ·
          refine ⟨16957749165460371720041357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11305166110306914480027571 16957749165460371720041357)
          ·
            refine ⟨6359155937047639395015509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16957749165460371720041357 6359155937047639395015509)
            ·
              refine ⟨37260679318638512080169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6359155937047639395015509 37260679318638512080169)
              ·
                rfl

theorem cell23_5877758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 9].length) (baseStart_5877758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877758 prefixEnd_5877758 := by exact prefixLift 5877758
  have htrace : WordTrace (prefixWord ++ tailWord_5877758) baseStart_5877758 baseEnd_5877758 := by
    simpa [prefixWord, tailWord_5877758, baseEnd_5877758] using wordTrace_append hprefix tailTrace_5877758
  have hstable : (prefixWord ++ tailWord_5877758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877758).length < 2 ^ (prefixWord ++ tailWord_5877758).sum := by decide
  have hdescent : baseEnd_5877758 < baseStart_5877758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877768 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_5877768 : Nat := 118140960795 + 5877768 * 2 ^ 59
def prefixEnd_5877768 : Nat := 4983230072969 + 3 ^ 40 * 5877768 * 2
def baseEnd_5877768 : Nat := 3018120159616264439368643

theorem tailTrace_5877768 : CollatzResearch.WordTrace tailWord_5877768 prefixEnd_5877768 3018120159616264439368643 := by
  unfold tailWord_5877768
  simp only [CollatzResearch.WordTrace]
  refine ⟨107189905484928926849748979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142919873979905235799665305 107189905484928926849748979)
  ·
    refine ⟨160784858227393390274623469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107189905484928926849748979 160784858227393390274623469)
    ·
      refine ⟨60294321835272521352983801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160784858227393390274623469 60294321835272521352983801)
      ·
        refine ⟨45220741376454391014737851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60294321835272521352983801 45220741376454391014737851)
        ·
          refine ⟨67831112064681586522106777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45220741376454391014737851 67831112064681586522106777)
          ·
            refine ⟨50873334048511189891580083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67831112064681586522106777 50873334048511189891580083)
            ·
              refine ⟨76310001072766784837370125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50873334048511189891580083 76310001072766784837370125)
              ·
                refine ⟨28616250402287544314013797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76310001072766784837370125 28616250402287544314013797)
                ·
                  refine ⟨5365546950428914558877587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28616250402287544314013797 5365546950428914558877587)
                  ·
                    refine ⟨8048320425643371838316381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365546950428914558877587 8048320425643371838316381)
                    ·
                      refine ⟨3018120159616264439368643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8048320425643371838316381 3018120159616264439368643)
                      ·
                        rfl

theorem cell23_5877768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_5877768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877768 prefixEnd_5877768 := by exact prefixLift 5877768
  have htrace : WordTrace (prefixWord ++ tailWord_5877768) baseStart_5877768 baseEnd_5877768 := by
    simpa [prefixWord, tailWord_5877768, baseEnd_5877768] using wordTrace_append hprefix tailTrace_5877768
  have hstable : (prefixWord ++ tailWord_5877768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877768).length < 2 ^ (prefixWord ++ tailWord_5877768).sum := by decide
  have hdescent : baseEnd_5877768 < baseStart_5877768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877808 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 3, 4, 2]
def baseStart_5877808 : Nat := 118140960795 + 5877808 * 2 ^ 59
def prefixEnd_5877808 : Nat := 4983230072969 + 3 ^ 40 * 5877808 * 2
def baseEnd_5877808 : Nat := 3018140698842444282868459

theorem tailTrace_5877808 : CollatzResearch.WordTrace tailWord_5877808 prefixEnd_5877808 3018140698842444282868459 := by
  unfold tailWord_5877808
  simp only [CollatzResearch.WordTrace]
  refine ⟨107190634944856470265477039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142920846593141960353969385 107190634944856470265477039)
  ·
    refine ⟨160785952417284705398215559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107190634944856470265477039 160785952417284705398215559)
    ·
      refine ⟨241178928625927058097323339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160785952417284705398215559 241178928625927058097323339)
      ·
        refine ⟨361768392938890587145985009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241178928625927058097323339 361768392938890587145985009)
        ·
          refine ⟨271326294704167940359488757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361768392938890587145985009 271326294704167940359488757)
          ·
            refine ⟨25436840128515744408702071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271326294704167940359488757 25436840128515744408702071)
            ·
              refine ⟨38155260192773616613053107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25436840128515744408702071 38155260192773616613053107)
              ·
                refine ⟨57232890289160424919579661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38155260192773616613053107 57232890289160424919579661)
                ·
                  refine ⟨21462333858435159344842373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57232890289160424919579661 21462333858435159344842373)
                  ·
                    refine ⟨4024187598456592377157945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21462333858435159344842373 4024187598456592377157945)
                    ·
                      refine ⟨3018140698842444282868459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024187598456592377157945 3018140698842444282868459)
                      ·
                        rfl

theorem cell23_5877808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 4, 2].length) (baseStart_5877808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877808 prefixEnd_5877808 := by exact prefixLift 5877808
  have htrace : WordTrace (prefixWord ++ tailWord_5877808) baseStart_5877808 baseEnd_5877808 := by
    simpa [prefixWord, tailWord_5877808, baseEnd_5877808] using wordTrace_append hprefix tailTrace_5877808
  have hstable : (prefixWord ++ tailWord_5877808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877808).length < 2 ^ (prefixWord ++ tailWord_5877808).sum := by decide
  have hdescent : baseEnd_5877808 < baseStart_5877808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877811 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5]
def baseStart_5877811 : Nat := 118140960795 + 5877811 * 2 ^ 59
def prefixEnd_5877811 : Nat := 4983230072969 + 3 ^ 40 * 5877811 * 2
def baseEnd_5877811 : Nat := 3018142239284407771130945

theorem tailTrace_5877811 : CollatzResearch.WordTrace tailWord_5877811 prefixEnd_5877811 3018142239284407771130945 := by
  unfold tailWord_5877811
  simp only [CollatzResearch.WordTrace]
  refine ⟨214381379308702072043313287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142920919539134714695542191 214381379308702072043313287)
  ·
    refine ⟨321572068963053108064969931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214381379308702072043313287 321572068963053108064969931)
    ·
      refine ⟨482358103444579662097454897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321572068963053108064969931 482358103444579662097454897)
      ·
        refine ⟨361768577583434746573091173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482358103444579662097454897 361768577583434746573091173)
        ·
          refine ⟨67831608296894014982454595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 361768577583434746573091173 67831608296894014982454595)
          ·
            refine ⟨101747412445341022473681893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67831608296894014982454595 101747412445341022473681893)
            ·
              refine ⟨19077639833501441713815355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101747412445341022473681893 19077639833501441713815355)
              ·
                refine ⟨28616459750252162570723033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19077639833501441713815355 28616459750252162570723033)
                ·
                  refine ⟨21462344812689121928042275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28616459750252162570723033 21462344812689121928042275)
                  ·
                    refine ⟨32193517219033682892063413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21462344812689121928042275 32193517219033682892063413)
                    ·
                      refine ⟨3018142239284407771130945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32193517219033682892063413 3018142239284407771130945)
                      ·
                        rfl

theorem cell23_5877811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_5877811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877811 prefixEnd_5877811 := by exact prefixLift 5877811
  have htrace : WordTrace (prefixWord ++ tailWord_5877811) baseStart_5877811 baseEnd_5877811 := by
    simpa [prefixWord, tailWord_5877811, baseEnd_5877811] using wordTrace_append hprefix tailTrace_5877811
  have hstable : (prefixWord ++ tailWord_5877811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877811).length < 2 ^ (prefixWord ++ tailWord_5877811).sum := by decide
  have hdescent : baseEnd_5877811 < baseStart_5877811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877831 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 7]
def baseStart_5877831 : Nat := 118140960795 + 5877831 * 2 ^ 59
def prefixEnd_5877831 : Nat := 4983230072969 + 3 ^ 40 * 5877831 * 2
def baseEnd_5877831 : Nat := 335350278766388632542317

theorem tailTrace_5877831 : CollatzResearch.WordTrace tailWord_5877831 prefixEnd_5877831 335350278766388632542317 := by
  unfold tailWord_5877831
  simp only [CollatzResearch.WordTrace]
  refine ⟨214382108768629615459041347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142921405845753076972694231 214382108768629615459041347)
  ·
    refine ⟨321573163152944423188562021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214382108768629615459041347 321573163152944423188562021)
    ·
      refine ⟨60294968091177079347855379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321573163152944423188562021 60294968091177079347855379)
      ·
        refine ⟨90442452136765619021783069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60294968091177079347855379 90442452136765619021783069)
        ·
          refine ⟨33915919551287107133168651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90442452136765619021783069 33915919551287107133168651)
          ·
            refine ⟨50873879326930660699752977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33915919551287107133168651 50873879326930660699752977)
            ·
              refine ⟨38155409495197995524814733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50873879326930660699752977 38155409495197995524814733)
              ·
                refine ⟨14308278560699248321805525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38155409495197995524814733 14308278560699248321805525)
                ·
                  refine ⟨335350278766388632542317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14308278560699248321805525 335350278766388632542317)
                  ·
                    rfl

theorem cell23_5877831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 7].length) (baseStart_5877831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877831 prefixEnd_5877831 := by exact prefixLift 5877831
  have htrace : WordTrace (prefixWord ++ tailWord_5877831) baseStart_5877831 baseEnd_5877831 := by
    simpa [prefixWord, tailWord_5877831, baseEnd_5877831] using wordTrace_append hprefix tailTrace_5877831
  have hstable : (prefixWord ++ tailWord_5877831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877831).length < 2 ^ (prefixWord ++ tailWord_5877831).sum := by decide
  have hdescent : baseEnd_5877831 < baseStart_5877831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877838 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_5877838 : Nat := 118140960795 + 5877838 * 2 ^ 59
def prefixEnd_5877838 : Nat := 4983230072969 + 3 ^ 40 * 5877838 * 2
def baseEnd_5877838 : Nat := 3018156103262079165493321

theorem tailTrace_5877838 : CollatzResearch.WordTrace tailWord_5877838 prefixEnd_5877838 3018156103262079165493321 := by
  unfold tailWord_5877838
  simp only [CollatzResearch.WordTrace]
  refine ⟨26797795509950531956818271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142921576053069503769697445 26797795509950531956818271)
  ·
    refine ⟨40196693264925797935227407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26797795509950531956818271 40196693264925797935227407)
    ·
      refine ⟨60295039897388696902841111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40196693264925797935227407 60295039897388696902841111)
      ·
        refine ⟨90442559846083045354261667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60295039897388696902841111 90442559846083045354261667)
        ·
          refine ⟨135663839769124568031392501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90442559846083045354261667 135663839769124568031392501)
          ·
            refine ⟨12718484978355428252943047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135663839769124568031392501 12718484978355428252943047)
            ·
              refine ⟨19077727467533142379414571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12718484978355428252943047 19077727467533142379414571)
              ·
                refine ⟨28616591201299713569121857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19077727467533142379414571 28616591201299713569121857)
                ·
                  refine ⟨21462443400974785176841393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28616591201299713569121857 21462443400974785176841393)
                  ·
                    refine ⟨16096832550731088882631045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21462443400974785176841393 16096832550731088882631045)
                    ·
                      refine ⟨3018156103262079165493321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16096832550731088882631045 3018156103262079165493321)
                      ·
                        rfl

theorem cell23_5877838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_5877838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877838 prefixEnd_5877838 := by exact prefixLift 5877838
  have htrace : WordTrace (prefixWord ++ tailWord_5877838) baseStart_5877838 baseEnd_5877838 := by
    simpa [prefixWord, tailWord_5877838, baseEnd_5877838] using wordTrace_append hprefix tailTrace_5877838
  have hstable : (prefixWord ++ tailWord_5877838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877838).length < 2 ^ (prefixWord ++ tailWord_5877838).sum := by decide
  have hdescent : baseEnd_5877838 < baseStart_5877838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877842 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_5877842 : Nat := 118140960795 + 5877842 * 2 ^ 59
def prefixEnd_5877842 : Nat := 4983230072969 + 3 ^ 40 * 5877842 * 2
def baseEnd_5877842 : Nat := 3018158157184697149843303

theorem tailTrace_5877842 : CollatzResearch.WordTrace tailWord_5877842 prefixEnd_5877842 3018158157184697149843303 := by
  unfold tailWord_5877842
  simp only [CollatzResearch.WordTrace]
  refine ⟨53595627492897441084422945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142921673314393176225127853 53595627492897441084422945)
  ·
    refine ⟨40196720619673080813317209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53595627492897441084422945 40196720619673080813317209)
    ·
      refine ⟨30147540464754810609987907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40196720619673080813317209 30147540464754810609987907)
      ·
        refine ⟨45221310697132215914981861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30147540464754810609987907 45221310697132215914981861)
        ·
          refine ⟨8478995755712290484059099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45221310697132215914981861 8478995755712290484059099)
          ·
            refine ⟨12718493633568435726088649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8478995755712290484059099 12718493633568435726088649)
            ·
              refine ⟨9538870225176326794566487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12718493633568435726088649 9538870225176326794566487)
              ·
                refine ⟨14308305337764490191849731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9538870225176326794566487 14308305337764490191849731)
                ·
                  refine ⟨21462458006646735287774597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14308305337764490191849731 21462458006646735287774597)
                  ·
                    refine ⟨4024210876246262866457737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21462458006646735287774597 4024210876246262866457737)
                    ·
                      refine ⟨3018158157184697149843303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024210876246262866457737 3018158157184697149843303)
                      ·
                        rfl

theorem cell23_5877842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_5877842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877842 prefixEnd_5877842 := by exact prefixLift 5877842
  have htrace : WordTrace (prefixWord ++ tailWord_5877842) baseStart_5877842 baseEnd_5877842 := by
    simpa [prefixWord, tailWord_5877842, baseEnd_5877842] using wordTrace_append hprefix tailTrace_5877842
  have hstable : (prefixWord ++ tailWord_5877842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877842).length < 2 ^ (prefixWord ++ tailWord_5877842).sum := by decide
  have hdescent : baseEnd_5877842 < baseStart_5877842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877898 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5877898 : Nat := 118140960795 + 5877898 * 2 ^ 59
def prefixEnd_5877898 : Nat := 4983230072969 + 3 ^ 40 * 5877898 * 2
def baseEnd_5877898 : Nat := 3018186912101348930743045

theorem tailTrace_5877898 : CollatzResearch.WordTrace tailWord_5877898 prefixEnd_5877898 3018186912101348930743045 := by
  unfold tailWord_5877898
  simp only [CollatzResearch.WordTrace]
  refine ⟨53596138114846721475432587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142923034972924590601153565 53596138114846721475432587)
  ·
    refine ⟨80394207172270082213148881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53596138114846721475432587 80394207172270082213148881)
    ·
      refine ⟨60295655379202561659861661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80394207172270082213148881 60295655379202561659861661)
      ·
        refine ⟨22610870767200960622448123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60295655379202561659861661 22610870767200960622448123)
        ·
          refine ⟨33916306150801440933672185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22610870767200960622448123 33916306150801440933672185)
          ·
            refine ⟨25437229613101080700254139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33916306150801440933672185 25437229613101080700254139)
            ·
              refine ⟨38155844419651621050381209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25437229613101080700254139 38155844419651621050381209)
              ·
                refine ⟨28616883314738715787785907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38155844419651621050381209 28616883314738715787785907)
                ·
                  refine ⟨42925324972108073681678861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28616883314738715787785907 42925324972108073681678861)
                  ·
                    refine ⟨16096996864540527630629573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42925324972108073681678861 16096996864540527630629573)
                    ·
                      refine ⟨3018186912101348930743045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16096996864540527630629573 3018186912101348930743045)
                      ·
                        rfl

theorem cell23_5877898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5877898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877898 prefixEnd_5877898 := by exact prefixLift 5877898
  have htrace : WordTrace (prefixWord ++ tailWord_5877898) baseStart_5877898 baseEnd_5877898 := by
    simpa [prefixWord, tailWord_5877898, baseEnd_5877898] using wordTrace_append hprefix tailTrace_5877898
  have hstable : (prefixWord ++ tailWord_5877898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877898).length < 2 ^ (prefixWord ++ tailWord_5877898).sum := by decide
  have hdescent : baseEnd_5877898 < baseStart_5877898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877938 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_5877938 : Nat := 118140960795 + 5877938 * 2 ^ 59
def prefixEnd_5877938 : Nat := 4983230072969 + 3 ^ 40 * 5877938 * 2
def baseEnd_5877938 : Nat := 335356383480836530471429

theorem tailTrace_5877938 : CollatzResearch.WordTrace tailWord_5877938 prefixEnd_5877938 335356383480836530471429 := by
  unfold tailWord_5877938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53596502844810493183296617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142924007586161315155457645 53596502844810493183296617)
  ·
    refine ⟨40197377133607869887472463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53596502844810493183296617 40197377133607869887472463)
    ·
      refine ⟨60296065700411804831208695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40197377133607869887472463 60296065700411804831208695)
      ·
        refine ⟨90444098550617707246813043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60296065700411804831208695 90444098550617707246813043)
        ·
          refine ⟨135666147825926560870219565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90444098550617707246813043 135666147825926560870219565)
          ·
            refine ⟨50874805434722460326332337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135666147825926560870219565 50874805434722460326332337)
            ·
              refine ⟨38156104076041845244749253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50874805434722460326332337 38156104076041845244749253)
              ·
                refine ⟨7154269514257845983390485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38156104076041845244749253 7154269514257845983390485)
                ·
                  refine ⟨335356383480836530471429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7154269514257845983390485 335356383480836530471429)
                  ·
                    rfl

theorem cell23_5877938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_5877938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877938 prefixEnd_5877938 := by exact prefixLift 5877938
  have htrace : WordTrace (prefixWord ++ tailWord_5877938) baseStart_5877938 baseEnd_5877938 := by
    simpa [prefixWord, tailWord_5877938, baseEnd_5877938] using wordTrace_append hprefix tailTrace_5877938
  have hstable : (prefixWord ++ tailWord_5877938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877938).length < 2 ^ (prefixWord ++ tailWord_5877938).sum := by decide
  have hdescent : baseEnd_5877938 < baseStart_5877938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877951 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 9]
def baseStart_5877951 : Nat := 118140960795 + 5877951 * 2 ^ 59
def prefixEnd_5877951 : Nat := 4983230072969 + 3 ^ 40 * 5877951 * 2
def baseEnd_5877951 : Nat := 1006071375525345741126767

theorem tailTrace_5877951 : CollatzResearch.WordTrace tailWord_5877951 prefixEnd_5877951 1006071375525345741126767 := by
  unfold tailWord_5877951
  simp only [CollatzResearch.WordTrace]
  refine ⟨214386485528194875953409707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142924323685463250635606471 214386485528194875953409707)
  ·
    refine ⟨321579728292292313930114561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214386485528194875953409707 321579728292292313930114561)
    ·
      refine ⟨241184796219219235447585921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321579728292292313930114561 241184796219219235447585921)
      ·
        refine ⟨180888597164414426585689441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241184796219219235447585921 180888597164414426585689441)
        ·
          refine ⟨135666447873310819939267081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180888597164414426585689441 135666447873310819939267081)
          ·
            refine ⟨101749835904983114954450311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135666447873310819939267081 101749835904983114954450311)
            ·
              refine ⟨152624753857474672431675467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101749835904983114954450311 152624753857474672431675467)
              ·
                refine ⟨228937130786212008647513201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152624753857474672431675467 228937130786212008647513201)
                ·
                  refine ⟨171702848089659006485634901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228937130786212008647513201 171702848089659006485634901)
                  ·
                    refine ⟨1006071375525345741126767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171702848089659006485634901 1006071375525345741126767)
                    ·
                      rfl

theorem cell23_5877951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_5877951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877951 prefixEnd_5877951 := by exact prefixLift 5877951
  have htrace : WordTrace (prefixWord ++ tailWord_5877951) baseStart_5877951 baseEnd_5877951 := by
    simpa [prefixWord, tailWord_5877951, baseEnd_5877951] using wordTrace_append hprefix tailTrace_5877951
  have hstable : (prefixWord ++ tailWord_5877951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877951).length < 2 ^ (prefixWord ++ tailWord_5877951).sum := by decide
  have hdescent : baseEnd_5877951 < baseStart_5877951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877961 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_5877961 : Nat := 118140960795 + 5877961 * 2 ^ 59
def prefixEnd_5877961 : Nat := 4983230072969 + 3 ^ 40 * 5877961 * 2
def baseEnd_5877961 : Nat := 3018219261382582184255255

theorem tailTrace_5877961 : CollatzResearch.WordTrace tailWord_5877961 prefixEnd_5877961 3018219261382582184255255 := by
  unfold tailWord_5877961
  simp only [CollatzResearch.WordTrace]
  refine ⟨214386850258158647661273737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142924566838772431774182491 214386850258158647661273737)
  ·
    refine ⟨160790137693618985745955303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214386850258158647661273737 160790137693618985745955303)
    ·
      refine ⟨241185206540428478618932955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160790137693618985745955303 241185206540428478618932955)
      ·
        refine ⟨361777809810642717928399433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241185206540428478618932955 361777809810642717928399433)
        ·
          refine ⟨271333357357982038446299575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361777809810642717928399433 271333357357982038446299575)
          ·
            refine ⟨407000036036973057669449363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271333357357982038446299575 407000036036973057669449363)
            ·
              refine ⟨610500054055459586504174045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407000036036973057669449363 610500054055459586504174045)
              ·
                refine ⟨228937520270797344939065267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 610500054055459586504174045 228937520270797344939065267)
                ·
                  refine ⟨343406280406196017408597901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228937520270797344939065267 343406280406196017408597901)
                  ·
                    refine ⟨128777355152323506528224213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343406280406196017408597901 128777355152323506528224213)
                    ·
                      refine ⟨3018219261382582184255255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128777355152323506528224213 3018219261382582184255255)
                      ·
                        rfl

theorem cell23_5877961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_5877961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877961 prefixEnd_5877961 := by exact prefixLift 5877961
  have htrace : WordTrace (prefixWord ++ tailWord_5877961) baseStart_5877961 baseEnd_5877961 := by
    simpa [prefixWord, tailWord_5877961, baseEnd_5877961] using wordTrace_append hprefix tailTrace_5877961
  have hstable : (prefixWord ++ tailWord_5877961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877961).length < 2 ^ (prefixWord ++ tailWord_5877961).sum := by decide
  have hdescent : baseEnd_5877961 < baseStart_5877961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877992 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5877992 : Nat := 118140960795 + 5877992 * 2 ^ 59
def prefixEnd_5877992 : Nat := 4983230072969 + 3 ^ 40 * 5877992 * 2
def baseEnd_5877992 : Nat := 3018235179282871562967613

theorem tailTrace_5877992 : CollatzResearch.WordTrace tailWord_5877992 prefixEnd_5877992 3018235179282871562967613 := by
  unfold tailWord_5877992
  simp only [CollatzResearch.WordTrace]
  refine ⟨107193990460523169977826115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142925320614030893303768153 107193990460523169977826115)
  ·
    refine ⟨160790985690784754966739173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107193990460523169977826115 160790985690784754966739173)
    ·
      refine ⟨30148309817022141556263595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160790985690784754966739173 30148309817022141556263595)
      ·
        refine ⟨45222464725533212334395393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30148309817022141556263595 45222464725533212334395393)
        ·
          refine ⟨33916848544149909250796545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45222464725533212334395393 33916848544149909250796545)
          ·
            refine ⟨25437636408112431938097409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33916848544149909250796545 25437636408112431938097409)
            ·
              refine ⟨19078227306084323953573057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25437636408112431938097409 19078227306084323953573057)
              ·
                refine ⟨14308670479563242965179793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19078227306084323953573057 14308670479563242965179793)
                ·
                  refine ⟨10731502859672432223884845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14308670479563242965179793 10731502859672432223884845)
                  ·
                    refine ⟨4024313572377162083956817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10731502859672432223884845 4024313572377162083956817)
                    ·
                      refine ⟨3018235179282871562967613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024313572377162083956817 3018235179282871562967613)
                      ·
                        rfl

theorem cell23_5877992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5877992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877992 prefixEnd_5877992 := by exact prefixLift 5877992
  have htrace : WordTrace (prefixWord ++ tailWord_5877992) baseStart_5877992 baseEnd_5877992 := by
    simpa [prefixWord, tailWord_5877992, baseEnd_5877992] using wordTrace_append hprefix tailTrace_5877992
  have hstable : (prefixWord ++ tailWord_5877992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877992).length < 2 ^ (prefixWord ++ tailWord_5877992).sum := by decide
  have hdescent : baseEnd_5877992 < baseStart_5877992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877998 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_5877998 : Nat := 118140960795 + 5877998 * 2 ^ 59
def prefixEnd_5877998 : Nat := 4983230072969 + 3 ^ 40 * 5877998 * 2
def baseEnd_5877998 : Nat := 1006079420055599513164195

theorem tailTrace_5877998 : CollatzResearch.WordTrace tailWord_5877998 prefixEnd_5877998 1006079420055599513164195 := by
  unfold tailWord_5877998
  simp only [CollatzResearch.WordTrace]
  refine ⟨26798524969878075372546331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142925466506016401986913765 26798524969878075372546331)
  ·
    refine ⟨40197787454817113058819497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26798524969878075372546331 40197787454817113058819497)
    ·
      refine ⟨30148340591112834794114623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40197787454817113058819497 30148340591112834794114623)
      ·
        refine ⟨45222510886669252191171935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30148340591112834794114623 45222510886669252191171935)
        ·
          refine ⟨67833766330003878286757903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45222510886669252191171935 67833766330003878286757903)
          ·
            refine ⟨101750649495005817430136855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67833766330003878286757903 101750649495005817430136855)
            ·
              refine ⟨152625974242508726145205283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101750649495005817430136855 152625974242508726145205283)
              ·
                refine ⟨228938961363763089217807925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152625974242508726145205283 228938961363763089217807925)
                ·
                  refine ⟨21463027627852789614169493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228938961363763089217807925 21463027627852789614169493)
                  ·
                    refine ⟨1006079420055599513164195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21463027627852789614169493 1006079420055599513164195)
                    ·
                      rfl

theorem cell23_5877998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_5877998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877998 prefixEnd_5877998 := by exact prefixLift 5877998
  have htrace : WordTrace (prefixWord ++ tailWord_5877998) baseStart_5877998 baseEnd_5877998 := by
    simpa [prefixWord, tailWord_5877998, baseEnd_5877998] using wordTrace_append hprefix tailTrace_5877998
  have hstable : (prefixWord ++ tailWord_5877998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877998).length < 2 ^ (prefixWord ++ tailWord_5877998).sum := by decide
  have hdescent : baseEnd_5877998 < baseStart_5877998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5877999 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 1, 1, 3]
def baseStart_5877999 : Nat := 118140960795 + 5877999 * 2 ^ 59
def prefixEnd_5877999 : Nat := 4983230072969 + 3 ^ 40 * 5877999 * 2
def baseEnd_5877999 : Nat := 3018238773647453035580081

theorem tailTrace_5877999 : CollatzResearch.WordTrace tailWord_5877999 prefixEnd_5877999 3018238773647453035580081 := by
  unfold tailWord_5877999
  simp only [CollatzResearch.WordTrace]
  refine ⟨214388236232020980151157051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142925490821347320100771367 214388236232020980151157051)
  ·
    refine ⟨321582354348031470226735577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214388236232020980151157051 321582354348031470226735577)
    ·
      refine ⟨241186765761023602670051683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321582354348031470226735577 241186765761023602670051683)
      ·
        refine ⟨361780148641535404005077525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241186765761023602670051683 361780148641535404005077525)
        ·
          refine ⟨16958444467571972062738009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 361780148641535404005077525 16958444467571972062738009)
          ·
            refine ⟨12718833350678979047053507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16958444467571972062738009 12718833350678979047053507)
            ·
              refine ⟨19078250026018468570580261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12718833350678979047053507 19078250026018468570580261)
              ·
                refine ⟨3577171879878462856983799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19078250026018468570580261 3577171879878462856983799)
                ·
                  refine ⟨5365757819817694285475699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577171879878462856983799 5365757819817694285475699)
                  ·
                    refine ⟨8048636729726541428213549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365757819817694285475699 8048636729726541428213549)
                    ·
                      refine ⟨3018238773647453035580081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8048636729726541428213549 3018238773647453035580081)
                      ·
                        rfl

theorem cell23_5877999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 1, 3].length) (baseStart_5877999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5877999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5877999 prefixEnd_5877999 := by exact prefixLift 5877999
  have htrace : WordTrace (prefixWord ++ tailWord_5877999) baseStart_5877999 baseEnd_5877999 := by
    simpa [prefixWord, tailWord_5877999, baseEnd_5877999] using wordTrace_append hprefix tailTrace_5877999
  have hstable : (prefixWord ++ tailWord_5877999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5877999).length < 2 ^ (prefixWord ++ tailWord_5877999).sum := by decide
  have hdescent : baseEnd_5877999 < baseStart_5877999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5877999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878008 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_5878008 : Nat := 118140960795 + 5878008 * 2 ^ 59
def prefixEnd_5878008 : Nat := 4983230072969 + 3 ^ 40 * 5878008 * 2
def baseEnd_5878008 : Nat := 3018243394973343500367539

theorem tailTrace_5878008 : CollatzResearch.WordTrace tailWord_5878008 prefixEnd_5878008 3018243394973343500367539 := by
  unfold tailWord_5878008
  simp only [CollatzResearch.WordTrace]
  refine ⟨107194282244494187344117339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142925709659325583125489785 107194282244494187344117339)
  ·
    refine ⟨160791423366741281016176009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107194282244494187344117339 160791423366741281016176009)
    ·
      refine ⟨120593567525055960762132007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160791423366741281016176009 120593567525055960762132007)
      ·
        refine ⟨180890351287583941143198011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120593567525055960762132007 180890351287583941143198011)
        ·
          refine ⟨271335526931375911714797017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180890351287583941143198011 271335526931375911714797017)
          ·
            refine ⟨203501645198531933786097763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271335526931375911714797017 203501645198531933786097763)
            ·
              refine ⟨305252467797797900679146645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203501645198531933786097763 305252467797797900679146645)
              ·
                refine ⟨14308709428021776594334999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305252467797797900679146645 14308709428021776594334999)
                ·
                  refine ⟨21463064142032664891502499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14308709428021776594334999 21463064142032664891502499)
                  ·
                    refine ⟨32194596213048997337253749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21463064142032664891502499 32194596213048997337253749)
                    ·
                      refine ⟨3018243394973343500367539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32194596213048997337253749 3018243394973343500367539)
                      ·
                        rfl

theorem cell23_5878008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_5878008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878008 prefixEnd_5878008 := by exact prefixLift 5878008
  have htrace : WordTrace (prefixWord ++ tailWord_5878008) baseStart_5878008 baseEnd_5878008 := by
    simpa [prefixWord, tailWord_5878008, baseEnd_5878008] using wordTrace_append hprefix tailTrace_5878008
  have hstable : (prefixWord ++ tailWord_5878008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878008).length < 2 ^ (prefixWord ++ tailWord_5878008).sum := by decide
  have hdescent : baseEnd_5878008 < baseStart_5878008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878015 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 2, 4]
def baseStart_5878015 : Nat := 118140960795 + 5878015 * 2 ^ 59
def prefixEnd_5878015 : Nat := 4983230072969 + 3 ^ 40 * 5878015 * 2
def baseEnd_5878015 : Nat := 1006082329779308324326669

theorem tailTrace_5878015 : CollatzResearch.WordTrace tailWord_5878015 prefixEnd_5878015 1006082329779308324326669 := by
  unfold tailWord_5878015
  simp only [CollatzResearch.WordTrace]
  refine ⟨214388819799963014883739499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142925879866642009922492999 214388819799963014883739499)
  ·
    refine ⟨321583229699944522325609249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214388819799963014883739499 321583229699944522325609249)
    ·
      refine ⟨241187422274958391744206937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321583229699944522325609249 241187422274958391744206937)
      ·
        refine ⟨180890566706218793808155203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241187422274958391744206937 180890566706218793808155203)
        ·
          refine ⟨271335850059328190712232805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180890566706218793808155203 271335850059328190712232805)
          ·
            refine ⟨50875471886124035758543651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271335850059328190712232805 50875471886124035758543651)
            ·
              refine ⟨76313207829186053637815477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50875471886124035758543651 76313207829186053637815477)
              ·
                refine ⟨7154363233986192528545201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76313207829186053637815477 7154363233986192528545201)
                ·
                  refine ⟨5365772425489644396408901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7154363233986192528545201 5365772425489644396408901)
                  ·
                    refine ⟨1006082329779308324326669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365772425489644396408901 1006082329779308324326669)
                    ·
                      rfl

theorem cell23_5878015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 4].length) (baseStart_5878015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878015 prefixEnd_5878015 := by exact prefixLift 5878015
  have htrace : WordTrace (prefixWord ++ tailWord_5878015) baseStart_5878015 baseEnd_5878015 := by
    simpa [prefixWord, tailWord_5878015, baseEnd_5878015] using wordTrace_append hprefix tailTrace_5878015
  have hstable : (prefixWord ++ tailWord_5878015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878015).length < 2 ^ (prefixWord ++ tailWord_5878015).sum := by decide
  have hdescent : baseEnd_5878015 < baseStart_5878015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878025 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 3]
def baseStart_5878025 : Nat := 118140960795 + 5878025 * 2 ^ 59
def prefixEnd_5878025 : Nat := 4983230072969 + 3 ^ 40 * 5878025 * 2
def baseEnd_5878025 : Nat := 3018252124144469933854961

theorem tailTrace_5878025 : CollatzResearch.WordTrace tailWord_5878025 prefixEnd_5878025 3018252124144469933854961 := by
  unfold tailWord_5878025
  simp only [CollatzResearch.WordTrace]
  refine ⟨214389184529926786591603529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142926123019951191061069019 214389184529926786591603529)
  ·
    refine ⟨160791888397445089943702647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214389184529926786591603529 160791888397445089943702647)
    ·
      refine ⟨241187832596167634915553971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160791888397445089943702647 241187832596167634915553971)
      ·
        refine ⟨361781748894251452373330957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241187832596167634915553971 361781748894251452373330957)
        ·
          refine ⟨135668155835344294639999109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361781748894251452373330957 135668155835344294639999109)
          ·
            refine ⟨25437779219127055244999833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135668155835344294639999109 25437779219127055244999833)
            ·
              refine ⟨19078334414345291433749875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25437779219127055244999833 19078334414345291433749875)
              ·
                refine ⟨28617501621517937150624813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19078334414345291433749875 28617501621517937150624813)
                ·
                  refine ⟨10731563108069226431484305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28617501621517937150624813 10731563108069226431484305)
                  ·
                    refine ⟨8048672331051919823613229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10731563108069226431484305 8048672331051919823613229)
                    ·
                      refine ⟨3018252124144469933854961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8048672331051919823613229 3018252124144469933854961)
                      ·
                        rfl

theorem cell23_5878025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 3].length) (baseStart_5878025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878025 prefixEnd_5878025 := by exact prefixLift 5878025
  have htrace : WordTrace (prefixWord ++ tailWord_5878025) baseStart_5878025 baseEnd_5878025 := by
    simpa [prefixWord, tailWord_5878025, baseEnd_5878025] using wordTrace_append hprefix tailTrace_5878025
  have hstable : (prefixWord ++ tailWord_5878025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878025).length < 2 ^ (prefixWord ++ tailWord_5878025).sum := by decide
  have hdescent : baseEnd_5878025 < baseStart_5878025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878039 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5878039 : Nat := 118140960795 + 5878039 * 2 ^ 59
def prefixEnd_5878039 : Nat := 4983230072969 + 3 ^ 40 * 5878039 * 2
def baseEnd_5878039 : Nat := 3018259312873632879079897

theorem tailTrace_5878039 : CollatzResearch.WordTrace tailWord_5878039 prefixEnd_5878039 3018259312873632879079897 := by
  unfold tailWord_5878039
  simp only [CollatzResearch.WordTrace]
  refine ⟨214389695151876066982613171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142926463434584044655075447 214389695151876066982613171)
  ·
    refine ⟨321584542727814100473919757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214389695151876066982613171 321584542727814100473919757)
    ·
      refine ⟨120594203522930287677719909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321584542727814100473919757 120594203522930287677719909)
      ·
        refine ⟨22611413160549428939572483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120594203522930287677719909 22611413160549428939572483)
        ·
          refine ⟨33917119740824143409358725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22611413160549428939572483 33917119740824143409358725)
          ·
            refine ⟨6359459951404526889254761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33917119740824143409358725 6359459951404526889254761)
            ·
              refine ⟨4769594963553395166941071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6359459951404526889254761 4769594963553395166941071)
              ·
                refine ⟨7154392445330092750411607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769594963553395166941071 7154392445330092750411607)
                ·
                  refine ⟨10731588667995139125617411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7154392445330092750411607 10731588667995139125617411)
                  ·
                    refine ⟨16097383001992708688426117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10731588667995139125617411 16097383001992708688426117)
                    ·
                      refine ⟨3018259312873632879079897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16097383001992708688426117 3018259312873632879079897)
                      ·
                        rfl

theorem cell23_5878039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5878039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878039 prefixEnd_5878039 := by exact prefixLift 5878039
  have htrace : WordTrace (prefixWord ++ tailWord_5878039) baseStart_5878039 baseEnd_5878039 := by
    simpa [prefixWord, tailWord_5878039, baseEnd_5878039] using wordTrace_append hprefix tailTrace_5878039
  have hstable : (prefixWord ++ tailWord_5878039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878039).length < 2 ^ (prefixWord ++ tailWord_5878039).sum := by decide
  have hdescent : baseEnd_5878039 < baseStart_5878039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878045 : List Nat := [1, 4, 2, 3, 2, 1, 10]
def baseStart_5878045 : Nat := 118140960795 + 5878045 * 2 ^ 59
def prefixEnd_5878045 : Nat := 4983230072969 + 3 ^ 40 * 5878045 * 2
def baseEnd_5878045 : Nat := 37262498688364936488949

theorem tailTrace_5878045 : CollatzResearch.WordTrace tailWord_5878045 prefixEnd_5878045 37262498688364936488949 := by
  unfold tailWord_5878045
  simp only [CollatzResearch.WordTrace]
  refine ⟨214389913989854330007331589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142926609326569553338221059 214389913989854330007331589)
  ·
    refine ⟨40198108873097686876374673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214389913989854330007331589 40198108873097686876374673)
    ·
      refine ⟨30148581654823265157281005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40198108873097686876374673 30148581654823265157281005)
      ·
        refine ⟨11305718120558724433980377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30148581654823265157281005 11305718120558724433980377)
        ·
          refine ⟨8479288590419043325485283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11305718120558724433980377 8479288590419043325485283)
          ·
            refine ⟨12718932885628564988227925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8479288590419043325485283 12718932885628564988227925)
            ·
              refine ⟨37262498688364936488949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12718932885628564988227925 37262498688364936488949)
              ·
                rfl

theorem cell23_5878045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 10].length) (baseStart_5878045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878045 prefixEnd_5878045 := by exact prefixLift 5878045
  have htrace : WordTrace (prefixWord ++ tailWord_5878045) baseStart_5878045 baseEnd_5878045 := by
    simpa [prefixWord, tailWord_5878045, baseEnd_5878045] using wordTrace_append hprefix tailTrace_5878045
  have hstable : (prefixWord ++ tailWord_5878045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878045).length < 2 ^ (prefixWord ++ tailWord_5878045).sum := by decide
  have hdescent : baseEnd_5878045 < baseStart_5878045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878056 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5878056 : Nat := 118140960795 + 5878056 * 2 ^ 59
def prefixEnd_5878056 : Nat := 4983230072969 + 3 ^ 40 * 5878056 * 2
def baseEnd_5878056 : Nat := 3018268042044759312567319

theorem tailTrace_5878056 : CollatzResearch.WordTrace tailWord_5878056 prefixEnd_5878056 3018268042044759312567319 := by
  unfold tailWord_5878056
  simp only [CollatzResearch.WordTrace]
  refine ⟨107195157596407239442991011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142926876795209652590654681 107195157596407239442991011)
  ·
    refine ⟨160792736394610859164486517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107195157596407239442991011 160792736394610859164486517)
    ·
      refine ⟨15074319036994768046670611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160792736394610859164486517 15074319036994768046670611)
      ·
        refine ⟨22611478555492152070005917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15074319036994768046670611 22611478555492152070005917)
        ·
          refine ⟨8479304458309557026252219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22611478555492152070005917 8479304458309557026252219)
          ·
            refine ⟨12718956687464335539378329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8479304458309557026252219 12718956687464335539378329)
            ·
              refine ⟨9539217515598251654533747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12718956687464335539378329 9539217515598251654533747)
              ·
                refine ⟨14308826273397377481800621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9539217515598251654533747 14308826273397377481800621)
                ·
                  refine ⟨5365809852524016555675233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14308826273397377481800621 5365809852524016555675233)
                  ·
                    refine ⟨4024357389393012416756425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5365809852524016555675233 4024357389393012416756425)
                    ·
                      refine ⟨3018268042044759312567319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024357389393012416756425 3018268042044759312567319)
                      ·
                        rfl

theorem cell23_5878056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5878056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878056 prefixEnd_5878056 := by exact prefixLift 5878056
  have htrace : WordTrace (prefixWord ++ tailWord_5878056) baseStart_5878056 baseEnd_5878056 := by
    simpa [prefixWord, tailWord_5878056, baseEnd_5878056] using wordTrace_append hprefix tailTrace_5878056
  have hstable : (prefixWord ++ tailWord_5878056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878056).length < 2 ^ (prefixWord ++ tailWord_5878056).sum := by decide
  have hdescent : baseEnd_5878056 < baseStart_5878056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878072 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_5878072 : Nat := 118140960795 + 5878072 * 2 ^ 59
def prefixEnd_5878072 : Nat := 4983230072969 + 3 ^ 40 * 5878072 * 2
def baseEnd_5878072 : Nat := 3018276257735231249967245

theorem tailTrace_5878072 : CollatzResearch.WordTrace tailWord_5878072 prefixEnd_5878072 3018276257735231249967245 := by
  unfold tailWord_5878072
  simp only [CollatzResearch.WordTrace]
  refine ⟨107195449380378256809282235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142927265840504342412376313 107195449380378256809282235)
  ·
    refine ⟨160793174070567385213923353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107195449380378256809282235 160793174070567385213923353)
    ·
      refine ⟨120594880552925538910442515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160793174070567385213923353 120594880552925538910442515)
      ·
        refine ⟨180892320829388308365663773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120594880552925538910442515 180892320829388308365663773)
        ·
          refine ⟨67834620311020615637123915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180892320829388308365663773 67834620311020615637123915)
          ·
            refine ⟨101751930466530923455685873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67834620311020615637123915 101751930466530923455685873)
            ·
              refine ⟨76313947849898192591764405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101751930466530923455685873 76313947849898192591764405)
              ·
                refine ⟨7154432610927955555477913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76313947849898192591764405 7154432610927955555477913)
                ·
                  refine ⟨5365824458195966666608435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7154432610927955555477913 5365824458195966666608435)
                  ·
                    refine ⟨8048736687293949999912653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365824458195966666608435 8048736687293949999912653)
                    ·
                      refine ⟨3018276257735231249967245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8048736687293949999912653 3018276257735231249967245)
                      ·
                        rfl

theorem cell23_5878072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_5878072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878072 prefixEnd_5878072 := by exact prefixLift 5878072
  have htrace : WordTrace (prefixWord ++ tailWord_5878072) baseStart_5878072 baseEnd_5878072 := by
    simpa [prefixWord, tailWord_5878072, baseEnd_5878072] using wordTrace_append hprefix tailTrace_5878072
  have hstable : (prefixWord ++ tailWord_5878072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878072).length < 2 ^ (prefixWord ++ tailWord_5878072).sum := by decide
  have hdescent : baseEnd_5878072 < baseStart_5878072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878088 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_5878088 : Nat := 118140960795 + 5878088 * 2 ^ 59
def prefixEnd_5878088 : Nat := 4983230072969 + 3 ^ 40 * 5878088 * 2
def baseEnd_5878088 : Nat := 1006094824475234395789057

theorem tailTrace_5878088 : CollatzResearch.WordTrace tailWord_5878088 prefixEnd_5878088 1006094824475234395789057 := by
  unfold tailWord_5878088
  simp only [CollatzResearch.WordTrace]
  refine ⟨107195741164349274175573459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142927654885799032234097945 107195741164349274175573459)
  ·
    refine ⟨160793611746523911263360189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107195741164349274175573459 160793611746523911263360189)
    ·
      refine ⟨60297604404946466723760071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160793611746523911263360189 60297604404946466723760071)
      ·
        refine ⟨90446406607419700085640107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60297604404946466723760071 90446406607419700085640107)
        ·
          refine ⟨135669609911129550128460161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90446406607419700085640107 135669609911129550128460161)
          ·
            refine ⟨101752207433347162596345121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135669609911129550128460161 101752207433347162596345121)
            ·
              refine ⟨76314155575010371947258841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101752207433347162596345121 76314155575010371947258841)
              ·
                refine ⟨57235616681257778960444131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76314155575010371947258841 57235616681257778960444131)
                ·
                  refine ⟨85853425021886668440666197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57235616681257778960444131 85853425021886668440666197)
                  ·
                    refine ⟨1006094824475234395789057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85853425021886668440666197 1006094824475234395789057)
                    ·
                      rfl

theorem cell23_5878088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_5878088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878088 prefixEnd_5878088 := by exact prefixLift 5878088
  have htrace : WordTrace (prefixWord ++ tailWord_5878088) baseStart_5878088 baseEnd_5878088 := by
    simpa [prefixWord, tailWord_5878088, baseEnd_5878088] using wordTrace_append hprefix tailTrace_5878088
  have hstable : (prefixWord ++ tailWord_5878088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878088).length < 2 ^ (prefixWord ++ tailWord_5878088).sum := by decide
  have hdescent : baseEnd_5878088 < baseStart_5878088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878115 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 3]
def baseStart_5878115 : Nat := 118140960795 + 5878115 * 2 ^ 59
def prefixEnd_5878115 : Nat := 4983230072969 + 3 ^ 40 * 5878115 * 2
def baseEnd_5878115 : Nat := 3018298337403374581729547

theorem tailTrace_5878115 : CollatzResearch.WordTrace tailWord_5878115 prefixEnd_5878115 3018298337403374581729547 := by
  unfold tailWord_5878115
  simp only [CollatzResearch.WordTrace]
  refine ⟨214392467099600731962379799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142928311399733821308253199 214392467099600731962379799)
  ·
    refine ⟨321588700649401097943569699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214392467099600731962379799 321588700649401097943569699)
    ·
      refine ⟨482383050974101646915354549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321588700649401097943569699 482383050974101646915354549)
      ·
        refine ⟨45223411028822029398314489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 482383050974101646915354549 45223411028822029398314489)
        ·
          refine ⟨33917558271616522048735867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45223411028822029398314489 33917558271616522048735867)
          ·
            refine ⟨50876337407424783073103801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33917558271616522048735867 50876337407424783073103801)
            ·
              refine ⟨38157253055568587304827851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50876337407424783073103801 38157253055568587304827851)
              ·
                refine ⟨57235879583352880957241777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38157253055568587304827851 57235879583352880957241777)
                ·
                  refine ⟨42926909687514660717931333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57235879583352880957241777 42926909687514660717931333)
                  ·
                    refine ⟨8048795566408998884612125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42926909687514660717931333 8048795566408998884612125)
                    ·
                      refine ⟨3018298337403374581729547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8048795566408998884612125 3018298337403374581729547)
                      ·
                        rfl

theorem cell23_5878115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_5878115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878115 prefixEnd_5878115 := by exact prefixLift 5878115
  have htrace : WordTrace (prefixWord ++ tailWord_5878115) baseStart_5878115 baseEnd_5878115 := by
    simpa [prefixWord, tailWord_5878115, baseEnd_5878115] using wordTrace_append hprefix tailTrace_5878115
  have hstable : (prefixWord ++ tailWord_5878115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878115).length < 2 ^ (prefixWord ++ tailWord_5878115).sum := by decide
  have hdescent : baseEnd_5878115 < baseStart_5878115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878125 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5878125 : Nat := 118140960795 + 5878125 * 2 ^ 59
def prefixEnd_5878125 : Nat := 4983230072969 + 3 ^ 40 * 5878125 * 2
def baseEnd_5878125 : Nat := 3018303472209919542604501

theorem tailTrace_5878125 : CollatzResearch.WordTrace tailWord_5878125 prefixEnd_5878125 3018303472209919542604501 := by
  unfold tailWord_5878125
  simp only [CollatzResearch.WordTrace]
  refine ⟨214392831829564503670243829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142928554553043002446829219 214392831829564503670243829)
  ·
    refine ⟨20099327984021672219085359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214392831829564503670243829 20099327984021672219085359)
    ·
      refine ⟨30148991976032508328628039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20099327984021672219085359 30148991976032508328628039)
      ·
        refine ⟨45223487964048762492942059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30148991976032508328628039 45223487964048762492942059)
        ·
          refine ⟨67835231946073143739413089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45223487964048762492942059 67835231946073143739413089)
          ·
            refine ⟨50876423959554857804559817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67835231946073143739413089 50876423959554857804559817)
            ·
              refine ⟨38157317969666143353419863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50876423959554857804559817 38157317969666143353419863)
              ·
                refine ⟨57235976954499215030129795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38157317969666143353419863 57235976954499215030129795)
                ·
                  refine ⟨85853965431748822545194693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57235976954499215030129795 85853965431748822545194693)
                  ·
                    refine ⟨16097618518452904227224005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85853965431748822545194693 16097618518452904227224005)
                    ·
                      refine ⟨3018303472209919542604501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16097618518452904227224005 3018303472209919542604501)
                      ·
                        rfl

theorem cell23_5878125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5878125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878125 prefixEnd_5878125 := by exact prefixLift 5878125
  have htrace : WordTrace (prefixWord ++ tailWord_5878125) baseStart_5878125 baseEnd_5878125 := by
    simpa [prefixWord, tailWord_5878125, baseEnd_5878125] using wordTrace_append hprefix tailTrace_5878125
  have hstable : (prefixWord ++ tailWord_5878125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878125).length < 2 ^ (prefixWord ++ tailWord_5878125).sum := by decide
  have hdescent : baseEnd_5878125 < baseStart_5878125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878152 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 5]
def baseStart_5878152 : Nat := 118140960795 + 5878152 * 2 ^ 59
def prefixEnd_5878152 : Nat := 4983230072969 + 3 ^ 40 * 5878152 * 2
def baseEnd_5878152 : Nat := 335368592909732326329653

theorem tailTrace_5878152 : CollatzResearch.WordTrace tailWord_5878152 prefixEnd_5878152 335368592909732326329653 := by
  unfold tailWord_5878152
  simp only [CollatzResearch.WordTrace]
  refine ⟨107196908300233343640738355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142929211066977791520984473 107196908300233343640738355)
  ·
    refine ⟨160795362450350015461107533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107196908300233343640738355 160795362450350015461107533)
    ·
      refine ⟨60298260918881255797915325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160795362450350015461107533 60298260918881255797915325)
      ·
        refine ⟨22611847844580470924218247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60298260918881255797915325 22611847844580470924218247)
        ·
          refine ⟨33917771766870706386327371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22611847844580470924218247 33917771766870706386327371)
          ·
            refine ⟨50876657650306059579491057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33917771766870706386327371 50876657650306059579491057)
            ·
              refine ⟨38157493237729544684618293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50876657650306059579491057 38157493237729544684618293)
              ·
                refine ⟨3577264991037144814182965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38157493237729544684618293 3577264991037144814182965)
                ·
                  refine ⟨335368592909732326329653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577264991037144814182965 335368592909732326329653)
                  ·
                    rfl

theorem cell23_5878152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 5].length) (baseStart_5878152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878152 prefixEnd_5878152 := by exact prefixLift 5878152
  have htrace : WordTrace (prefixWord ++ tailWord_5878152) baseStart_5878152 baseEnd_5878152 := by
    simpa [prefixWord, tailWord_5878152, baseEnd_5878152] using wordTrace_append hprefix tailTrace_5878152
  have hstable : (prefixWord ++ tailWord_5878152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878152).length < 2 ^ (prefixWord ++ tailWord_5878152).sum := by decide
  have hdescent : baseEnd_5878152 < baseStart_5878152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878175 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5878175 : Nat := 118140960795 + 5878175 * 2 ^ 59
def prefixEnd_5878175 : Nat := 4983230072969 + 3 ^ 40 * 5878175 * 2
def baseEnd_5878175 : Nat := 3018329146242644346979271

theorem tailTrace_5878175 : CollatzResearch.WordTrace tailWord_5878175 prefixEnd_5878175 3018329146242644346979271 := by
  unfold tailWord_5878175
  simp only [CollatzResearch.WordTrace]
  refine ⟨214394655479383362209563979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142929770319588908139709319 214394655479383362209563979)
  ·
    refine ⟨321591983219075043314345969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214394655479383362209563979 321591983219075043314345969)
    ·
      refine ⟨241193987414306282485759477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321591983219075043314345969 241193987414306282485759477)
      ·
        refine ⟨22611936320091213983039951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241193987414306282485759477 22611936320091213983039951)
        ·
          refine ⟨33917904480136820974559927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22611936320091213983039951 33917904480136820974559927)
          ·
            refine ⟨50876856720205231461839891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33917904480136820974559927 50876856720205231461839891)
            ·
              refine ⟨76315285080307847192759837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50876856720205231461839891 76315285080307847192759837)
              ·
                refine ⟨28618231905115442697284939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76315285080307847192759837 28618231905115442697284939)
                ·
                  refine ⟨42927347857673164045927409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28618231905115442697284939 42927347857673164045927409)
                  ·
                    refine ⟨32195510893254873034445557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42927347857673164045927409 32195510893254873034445557)
                    ·
                      refine ⟨3018329146242644346979271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32195510893254873034445557 3018329146242644346979271)
                      ·
                        rfl

theorem cell23_5878175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5878175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878175 prefixEnd_5878175 := by exact prefixLift 5878175
  have htrace : WordTrace (prefixWord ++ tailWord_5878175) baseStart_5878175 baseEnd_5878175 := by
    simpa [prefixWord, tailWord_5878175, baseEnd_5878175] using wordTrace_append hprefix tailTrace_5878175
  have hstable : (prefixWord ++ tailWord_5878175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878175).length < 2 ^ (prefixWord ++ tailWord_5878175).sum := by decide
  have hdescent : baseEnd_5878175 < baseStart_5878175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878185 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_5878185 : Nat := 118140960795 + 5878185 * 2 ^ 59
def prefixEnd_5878185 : Nat := 4983230072969 + 3 ^ 40 * 5878185 * 2
def baseEnd_5878185 : Nat := 3018334281049189307854225

theorem tailTrace_5878185 : CollatzResearch.WordTrace tailWord_5878185 prefixEnd_5878185 3018334281049189307854225 := by
  unfold tailWord_5878185
  simp only [CollatzResearch.WordTrace]
  refine ⟨214395020209347133917428009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142930013472898089278285339 214395020209347133917428009)
  ·
    refine ⟨160796265157010350438071007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214395020209347133917428009 160796265157010350438071007)
    ·
      refine ⟨241194397735515525657106511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160796265157010350438071007 241194397735515525657106511)
      ·
        refine ⟨361791596603273288485659767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241194397735515525657106511 361791596603273288485659767)
        ·
          refine ⟨542687394904909932728489651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361791596603273288485659767 542687394904909932728489651)
          ·
            refine ⟨814031092357364899092734477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542687394904909932728489651 814031092357364899092734477)
            ·
              refine ⟨305261659634011837159775429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 814031092357364899092734477 305261659634011837159775429)
              ·
                refine ⟨57236561181377219467457893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305261659634011837159775429 57236561181377219467457893)
                ·
                  refine ⟨10731855221508228650148355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57236561181377219467457893 10731855221508228650148355)
                  ·
                    refine ⟨16097782832262342975222533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10731855221508228650148355 16097782832262342975222533)
                    ·
                      refine ⟨3018334281049189307854225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16097782832262342975222533 3018334281049189307854225)
                      ·
                        rfl

theorem cell23_5878185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_5878185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878185 prefixEnd_5878185 := by exact prefixLift 5878185
  have htrace : WordTrace (prefixWord ++ tailWord_5878185) baseStart_5878185 baseEnd_5878185 := by
    simpa [prefixWord, tailWord_5878185, baseEnd_5878185] using wordTrace_append hprefix tailTrace_5878185
  have hstable : (prefixWord ++ tailWord_5878185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878185).length < 2 ^ (prefixWord ++ tailWord_5878185).sum := by decide
  have hdescent : baseEnd_5878185 < baseStart_5878185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878186 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_5878186 : Nat := 118140960795 + 5878186 * 2 ^ 59
def prefixEnd_5878186 : Nat := 4983230072969 + 3 ^ 40 * 5878186 * 2
def baseEnd_5878186 : Nat := 335370532725538200437969

theorem tailTrace_5878186 : CollatzResearch.WordTrace tailWord_5878186 prefixEnd_5878186 335370532725538200437969 := by
  unfold tailWord_5878186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53598764170585877772053603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142930037788229007392142941 53598764170585877772053603)
  ·
    refine ⟨80398146255878816658080405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53598764170585877772053603 80398146255878816658080405)
    ·
      refine ⟨3768663105744319530847519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80398146255878816658080405 3768663105744319530847519)
      ·
        refine ⟨5652994658616479296271279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768663105744319530847519 5652994658616479296271279)
        ·
          refine ⟨8479491987924718944406919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652994658616479296271279 8479491987924718944406919)
          ·
            refine ⟨12719237981887078416610379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8479491987924718944406919 12719237981887078416610379)
            ·
              refine ⟨19078856972830617624915569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12719237981887078416610379 19078856972830617624915569)
              ·
                refine ⟨14309142729622963218686677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19078856972830617624915569 14309142729622963218686677)
                ·
                  refine ⟨335370532725538200437969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14309142729622963218686677 335370532725538200437969)
                  ·
                    rfl

theorem cell23_5878186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_5878186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878186 prefixEnd_5878186 := by exact prefixLift 5878186
  have htrace : WordTrace (prefixWord ++ tailWord_5878186) baseStart_5878186 baseEnd_5878186 := by
    simpa [prefixWord, tailWord_5878186, baseEnd_5878186] using wordTrace_append hprefix tailTrace_5878186
  have hstable : (prefixWord ++ tailWord_5878186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878186).length < 2 ^ (prefixWord ++ tailWord_5878186).sum := by decide
  have hdescent : baseEnd_5878186 < baseStart_5878186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878215 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_5878215 : Nat := 118140960795 + 5878215 * 2 ^ 59
def prefixEnd_5878215 : Nat := 4983230072969 + 3 ^ 40 * 5878215 * 2
def baseEnd_5878215 : Nat := 3018349685468824190479087

theorem tailTrace_5878215 : CollatzResearch.WordTrace tailWord_5878215 prefixEnd_5878215 3018349685468824190479087 := by
  unfold tailWord_5878215
  simp only [CollatzResearch.WordTrace]
  refine ⟨214396114399238449041020099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142930742932825632694013399 214396114399238449041020099)
  ·
    refine ⟨321594171598857673561530149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214396114399238449041020099 321594171598857673561530149)
    ·
      refine ⟨60298907174785813792786903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321594171598857673561530149 60298907174785813792786903)
      ·
        refine ⟨90448360762178720689180355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60298907174785813792786903 90448360762178720689180355)
        ·
          refine ⟨135672541143268081033770533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90448360762178720689180355 135672541143268081033770533)
          ·
            refine ⟨25438601464362765193831975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135672541143268081033770533 25438601464362765193831975)
            ·
              refine ⟨38157902196544147790747963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25438601464362765193831975 38157902196544147790747963)
              ·
                refine ⟨57236853294816221686121945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38157902196544147790747963 57236853294816221686121945)
                ·
                  refine ⟨42927639971112166264591459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57236853294816221686121945 42927639971112166264591459)
                  ·
                    refine ⟨64391459956668249396887189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42927639971112166264591459 64391459956668249396887189)
                    ·
                      refine ⟨3018349685468824190479087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64391459956668249396887189 3018349685468824190479087)
                      ·
                        rfl

theorem cell23_5878215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_5878215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878215 prefixEnd_5878215 := by exact prefixLift 5878215
  have htrace : WordTrace (prefixWord ++ tailWord_5878215) baseStart_5878215 baseEnd_5878215 := by
    simpa [prefixWord, tailWord_5878215, baseEnd_5878215] using wordTrace_append hprefix tailTrace_5878215
  have hstable : (prefixWord ++ tailWord_5878215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878215).length < 2 ^ (prefixWord ++ tailWord_5878215).sum := by decide
  have hdescent : baseEnd_5878215 < baseStart_5878215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878222 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_5878222 : Nat := 118140960795 + 5878222 * 2 ^ 59
def prefixEnd_5878222 : Nat := 4983230072969 + 3 ^ 40 * 5878222 * 2
def baseEnd_5878222 : Nat := 3018353279833405663091555

theorem tailTrace_5878222 : CollatzResearch.WordTrace tailWord_5878222 prefixEnd_5878222 3018353279833405663091555 := by
  unfold tailWord_5878222
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799546213776636154565615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142930913140142059491016613 26799546213776636154565615)
  ·
    refine ⟨40199319320664954231848423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26799546213776636154565615 40199319320664954231848423)
    ·
      refine ⟨60298978980997431347772635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40199319320664954231848423 60298978980997431347772635)
      ·
        refine ⟨90448468471496147021658953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60298978980997431347772635 90448468471496147021658953)
        ·
          refine ⟨67836351353622110266244215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90448468471496147021658953 67836351353622110266244215)
          ·
            refine ⟨101754527030433165399366323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67836351353622110266244215 101754527030433165399366323)
            ·
              refine ⟨152631790545649748099049485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101754527030433165399366323 152631790545649748099049485)
              ·
                refine ⟨57236921454618655537143557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152631790545649748099049485 57236921454618655537143557)
                ·
                  refine ⟨10731922772740997913214417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57236921454618655537143557 10731922772740997913214417)
                  ·
                    refine ⟨8048942079555748434910813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10731922772740997913214417 8048942079555748434910813)
                    ·
                      refine ⟨3018353279833405663091555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8048942079555748434910813 3018353279833405663091555)
                      ·
                        rfl

theorem cell23_5878222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_5878222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878222 prefixEnd_5878222 := by exact prefixLift 5878222
  have htrace : WordTrace (prefixWord ++ tailWord_5878222) baseStart_5878222 baseEnd_5878222 := by
    simpa [prefixWord, tailWord_5878222, baseEnd_5878222] using wordTrace_append hprefix tailTrace_5878222
  have hstable : (prefixWord ++ tailWord_5878222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878222).length < 2 ^ (prefixWord ++ tailWord_5878222).sum := by decide
  have hdescent : baseEnd_5878222 < baseStart_5878222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878229 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_5878229 : Nat := 118140960795 + 5878229 * 2 ^ 59
def prefixEnd_5878229 : Nat := 4983230072969 + 3 ^ 40 * 5878229 * 2
def baseEnd_5878229 : Nat := 1006118958065995711901341

theorem tailTrace_5878229 : CollatzResearch.WordTrace tailWord_5878229 prefixEnd_5878229 1006118958065995711901341 := by
  unfold tailWord_5878229
  simp only [CollatzResearch.WordTrace]
  refine ⟨214396625021187729432029741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142931083347458486288019827 214396625021187729432029741)
  ·
    refine ⟨80398734382945398537011153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214396625021187729432029741 80398734382945398537011153)
    ·
      refine ⟨60299050787209048902758365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80398734382945398537011153 60299050787209048902758365)
      ·
        refine ⟨22612144045203393338534387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60299050787209048902758365 22612144045203393338534387)
        ·
          refine ⟨33918216067805090007801581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22612144045203393338534387 33918216067805090007801581)
          ·
            refine ⟨12719331025426908752925593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33918216067805090007801581 12719331025426908752925593)
            ·
              refine ⟨9539498269070181564694195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12719331025426908752925593 9539498269070181564694195)
              ·
                refine ⟨14309247403605272347041293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9539498269070181564694195 14309247403605272347041293)
                ·
                  refine ⟨5365967776351977130140485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14309247403605272347041293 5365967776351977130140485)
                  ·
                    refine ⟨1006118958065995711901341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365967776351977130140485 1006118958065995711901341)
                    ·
                      rfl

theorem cell23_5878229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_5878229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878229 prefixEnd_5878229 := by exact prefixLift 5878229
  have htrace : WordTrace (prefixWord ++ tailWord_5878229) baseStart_5878229 baseEnd_5878229 := by
    simpa [prefixWord, tailWord_5878229, baseEnd_5878229] using wordTrace_append hprefix tailTrace_5878229
  have hstable : (prefixWord ++ tailWord_5878229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878229).length < 2 ^ (prefixWord ++ tailWord_5878229).sum := by decide
  have hdescent : baseEnd_5878229 < baseStart_5878229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878286 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_5878286 : Nat := 118140960795 + 5878286 * 2 ^ 59
def prefixEnd_5878286 : Nat := 4983230072969 + 3 ^ 40 * 5878286 * 2
def baseEnd_5878286 : Nat := 3018386142595293412691261

theorem tailTrace_5878286 : CollatzResearch.WordTrace tailWord_5878286 prefixEnd_5878286 3018386142595293412691261 := by
  unfold tailWord_5878286
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799837997747653520856839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142932469321320818777903141 26799837997747653520856839)
  ·
    refine ⟨40199756996621480281285259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26799837997747653520856839 40199756996621480281285259)
    ·
      refine ⟨60299635494932220421927889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40199756996621480281285259 60299635494932220421927889)
      ·
        refine ⟨45224726621199165316445917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60299635494932220421927889 45224726621199165316445917)
        ·
          refine ⟨16959272482949686993667219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45224726621199165316445917 16959272482949686993667219)
          ·
            refine ⟨25438908724424530490500829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16959272482949686993667219 25438908724424530490500829)
            ·
              refine ⟨9539590771659198933937811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25438908724424530490500829 9539590771659198933937811)
              ·
                refine ⟨14309386157488798400906717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9539590771659198933937811 14309386157488798400906717)
                ·
                  refine ⟨5366019809058299400340019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14309386157488798400906717 5366019809058299400340019)
                  ·
                    refine ⟨8049029713587449100510029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366019809058299400340019 8049029713587449100510029)
                    ·
                      refine ⟨3018386142595293412691261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049029713587449100510029 3018386142595293412691261)
                      ·
                        rfl

theorem cell23_5878286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_5878286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878286 prefixEnd_5878286 := by exact prefixLift 5878286
  have htrace : WordTrace (prefixWord ++ tailWord_5878286) baseStart_5878286 baseEnd_5878286 := by
    simpa [prefixWord, tailWord_5878286, baseEnd_5878286] using wordTrace_append hprefix tailTrace_5878286
  have hstable : (prefixWord ++ tailWord_5878286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878286).length < 2 ^ (prefixWord ++ tailWord_5878286).sum := by decide
  have hdescent : baseEnd_5878286 < baseStart_5878286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878309 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_5878309 : Nat := 118140960795 + 5878309 * 2 ^ 59
def prefixEnd_5878309 : Nat := 4983230072969 + 3 ^ 40 * 5878309 * 2
def baseEnd_5878309 : Nat := 3018397952650346822703655

theorem tailTrace_5878309 : CollatzResearch.WordTrace tailWord_5878309 prefixEnd_5878309 3018397952650346822703655 := by
  unfold tailWord_5878309
  simp only [CollatzResearch.WordTrace]
  refine ⟨214399542860897903094941981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142933028573931935396627987 214399542860897903094941981)
  ·
    refine ⟨80399828572836713660603243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214399542860897903094941981 80399828572836713660603243)
    ·
      refine ⟨120599742859255070490904865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80399828572836713660603243 120599742859255070490904865)
      ·
        refine ⟨90449807144441302868178649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120599742859255070490904865 90449807144441302868178649)
        ·
          refine ⟨67837355358330977151133987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90449807144441302868178649 67837355358330977151133987)
          ·
            refine ⟨101756033037496465726700981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67837355358330977151133987 101756033037496465726700981)
            ·
              refine ⟨9539628097265293661878217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101756033037496465726700981 9539628097265293661878217)
              ·
                refine ⟨7154721072948970246408663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9539628097265293661878217 7154721072948970246408663)
                ·
                  refine ⟨10732081609423455369612995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7154721072948970246408663 10732081609423455369612995)
                  ·
                    refine ⟨16098122414135183054419493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10732081609423455369612995 16098122414135183054419493)
                    ·
                      refine ⟨3018397952650346822703655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16098122414135183054419493 3018397952650346822703655)
                      ·
                        rfl

theorem cell23_5878309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_5878309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878309 prefixEnd_5878309 := by exact prefixLift 5878309
  have htrace : WordTrace (prefixWord ++ tailWord_5878309) baseStart_5878309 baseEnd_5878309 := by
    simpa [prefixWord, tailWord_5878309, baseEnd_5878309] using wordTrace_append hprefix tailTrace_5878309
  have hstable : (prefixWord ++ tailWord_5878309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878309).length < 2 ^ (prefixWord ++ tailWord_5878309).sum := by decide
  have hdescent : baseEnd_5878309 < baseStart_5878309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878322 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_5878322 : Nat := 118140960795 + 5878322 * 2 ^ 59
def prefixEnd_5878322 : Nat := 4983230072969 + 3 ^ 40 * 5878322 * 2
def baseEnd_5878322 : Nat := 3018404627898855271841095

theorem tailTrace_5878322 : CollatzResearch.WordTrace tailWord_5878322 prefixEnd_5878322 3018404627898855271841095 := by
  unfold tailWord_5878322
  simp only [CollatzResearch.WordTrace]
  refine ⟨53600004252462701578791305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142933344673233870876776813 53600004252462701578791305)
  ·
    refine ⟨40200003189347026184093479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53600004252462701578791305 40200003189347026184093479)
    ·
      refine ⟨60300004784020539276140219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40200003189347026184093479 60300004784020539276140219)
      ·
        refine ⟨90450007176030808914210329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60300004784020539276140219 90450007176030808914210329)
        ·
          refine ⟨67837505382023106685657747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90450007176030808914210329 67837505382023106685657747)
          ·
            refine ⟨101756258073034660028486621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67837505382023106685657747 101756258073034660028486621)
            ·
              refine ⟨38158596777387997510682483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101756258073034660028486621 38158596777387997510682483)
              ·
                refine ⟨57237895166081996266023725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38158596777387997510682483 57237895166081996266023725)
                ·
                  refine ⟨21464210687280748599758897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57237895166081996266023725 21464210687280748599758897)
                  ·
                    refine ⟨16098158015460561449819173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21464210687280748599758897 16098158015460561449819173)
                    ·
                      refine ⟨3018404627898855271841095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16098158015460561449819173 3018404627898855271841095)
                      ·
                        rfl

theorem cell23_5878322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_5878322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878322 prefixEnd_5878322 := by exact prefixLift 5878322
  have htrace : WordTrace (prefixWord ++ tailWord_5878322) baseStart_5878322 baseEnd_5878322 := by
    simpa [prefixWord, tailWord_5878322, baseEnd_5878322] using wordTrace_append hprefix tailTrace_5878322
  have hstable : (prefixWord ++ tailWord_5878322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878322).length < 2 ^ (prefixWord ++ tailWord_5878322).sum := by decide
  have hdescent : baseEnd_5878322 < baseStart_5878322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878349 : List Nat := [1, 6, 1, 1, 2, 1, 3, 8]
def baseStart_5878349 : Nat := 118140960795 + 5878349 * 2 ^ 59
def prefixEnd_5878349 : Nat := 4983230072969 + 3 ^ 40 * 5878349 * 2
def baseEnd_5878349 : Nat := 111793277476908395044573

theorem tailTrace_5878349 : CollatzResearch.WordTrace tailWord_5878349 prefixEnd_5878349 111793277476908395044573 := by
  unfold tailWord_5878349
  simp only [CollatzResearch.WordTrace]
  refine ⟨214401001780752989926398101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142934001187168659950932067 214401001780752989926398101)
  ·
    refine ⟨10050046958472796402799911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 214401001780752989926398101 10050046958472796402799911)
    ·
      refine ⟨15075070437709194604199867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10050046958472796402799911 15075070437709194604199867)
      ·
        refine ⟨22612605656563791906299801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15075070437709194604199867 22612605656563791906299801)
        ·
          refine ⟨16959454242422843929724851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22612605656563791906299801 16959454242422843929724851)
          ·
            refine ⟨25439181363634265894587277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16959454242422843929724851 25439181363634265894587277)
            ·
              refine ⟨9539693011362849710470229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25439181363634265894587277 9539693011362849710470229)
              ·
                refine ⟨111793277476908395044573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9539693011362849710470229 111793277476908395044573)
                ·
                  rfl

theorem cell23_5878349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 8].length) (baseStart_5878349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878349 prefixEnd_5878349 := by exact prefixLift 5878349
  have htrace : WordTrace (prefixWord ++ tailWord_5878349) baseStart_5878349 baseEnd_5878349 := by
    simpa [prefixWord, tailWord_5878349, baseEnd_5878349] using wordTrace_append hprefix tailTrace_5878349
  have hstable : (prefixWord ++ tailWord_5878349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878349).length < 2 ^ (prefixWord ++ tailWord_5878349).sum := by decide
  have hdescent : baseEnd_5878349 < baseStart_5878349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878359 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_5878359 : Nat := 118140960795 + 5878359 * 2 ^ 59
def prefixEnd_5878359 : Nat := 4983230072969 + 3 ^ 40 * 5878359 * 2
def baseEnd_5878359 : Nat := 3018423626683071627078425

theorem tailTrace_5878359 : CollatzResearch.WordTrace tailWord_5878359 prefixEnd_5878359 3018423626683071627078425 := by
  unfold tailWord_5878359
  simp only [CollatzResearch.WordTrace]
  refine ⟨214401366510716761634262131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142934244340477841089508087 214401366510716761634262131)
  ·
    refine ⟨321602049766075142451393197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214401366510716761634262131 321602049766075142451393197)
    ·
      refine ⟨120600768662278178419272449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321602049766075142451393197 120600768662278178419272449)
      ·
        refine ⟨90450576496708633814454337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120600768662278178419272449 90450576496708633814454337)
        ·
          refine ⟨67837932372531475360840753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90450576496708633814454337 67837932372531475360840753)
          ·
            refine ⟨50878449279398606520630565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67837932372531475360840753 50878449279398606520630565)
            ·
              refine ⟨9539709239887238722618231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50878449279398606520630565 9539709239887238722618231)
              ·
                refine ⟨14309563859830858083927347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9539709239887238722618231 14309563859830858083927347)
                ·
                  refine ⟨21464345789746287125891021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14309563859830858083927347 21464345789746287125891021)
                  ·
                    refine ⟨8049129671154857672209133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21464345789746287125891021 8049129671154857672209133)
                    ·
                      refine ⟨3018423626683071627078425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049129671154857672209133 3018423626683071627078425)
                      ·
                        rfl

theorem cell23_5878359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_5878359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878359 prefixEnd_5878359 := by exact prefixLift 5878359
  have htrace : WordTrace (prefixWord ++ tailWord_5878359) baseStart_5878359 baseEnd_5878359 := by
    simpa [prefixWord, tailWord_5878359, baseEnd_5878359] using wordTrace_append hprefix tailTrace_5878359
  have hstable : (prefixWord ++ tailWord_5878359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878359).length < 2 ^ (prefixWord ++ tailWord_5878359).sum := by decide
  have hdescent : baseEnd_5878359 < baseStart_5878359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878372 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_5878372 : Nat := 118140960795 + 5878372 * 2 ^ 59
def prefixEnd_5878372 : Nat := 4983230072969 + 3 ^ 40 * 5878372 * 2
def baseEnd_5878372 : Nat := 3018430301931580076215865

theorem tailTrace_5878372 : CollatzResearch.WordTrace tailWord_5878372 prefixEnd_5878372 3018430301931580076215865 := by
  unfold tailWord_5878372
  simp only [CollatzResearch.WordTrace]
  refine ⟨107200920329834832427242685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142934560439779776569656913 107200920329834832427242685)
  ·
    refine ⟨40200345123688062160216007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107200920329834832427242685 40200345123688062160216007)
    ·
      refine ⟨60300517685532093240324011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40200345123688062160216007 60300517685532093240324011)
      ·
        refine ⟨90450776528298139860486017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60300517685532093240324011 90450776528298139860486017)
        ·
          refine ⟨67838082396223604895364513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90450776528298139860486017 67838082396223604895364513)
          ·
            refine ⟨50878561797167703671523385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67838082396223604895364513 50878561797167703671523385)
            ·
              refine ⟨38158921347875777753642539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50878561797167703671523385 38158921347875777753642539)
              ·
                refine ⟨57238382021813666630463809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38158921347875777753642539 57238382021813666630463809)
                ·
                  refine ⟨42928786516360249972847857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57238382021813666630463809 42928786516360249972847857)
                  ·
                    refine ⟨32196589887270187479635893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42928786516360249972847857 32196589887270187479635893)
                    ·
                      refine ⟨3018430301931580076215865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32196589887270187479635893 3018430301931580076215865)
                      ·
                        rfl

theorem cell23_5878372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_5878372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878372 prefixEnd_5878372 := by exact prefixLift 5878372
  have htrace : WordTrace (prefixWord ++ tailWord_5878372) baseStart_5878372 baseEnd_5878372 := by
    simpa [prefixWord, tailWord_5878372, baseEnd_5878372] using wordTrace_append hprefix tailTrace_5878372
  have hstable : (prefixWord ++ tailWord_5878372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878372).length < 2 ^ (prefixWord ++ tailWord_5878372).sum := by decide
  have hdescent : baseEnd_5878372 < baseStart_5878372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878393 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 3]
def baseStart_5878393 : Nat := 118140960795 + 5878393 * 2 ^ 59
def prefixEnd_5878393 : Nat := 4983230072969 + 3 ^ 40 * 5878393 * 2
def baseEnd_5878393 : Nat := 3018441085025324494053269

theorem tailTrace_5878393 : CollatzResearch.WordTrace tailWord_5878393 prefixEnd_5878393 3018441085025324494053269 := by
  unfold tailWord_5878393
  simp only [CollatzResearch.WordTrace]
  refine ⟨214402606592593585440999833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142935071061729056960666555 214402606592593585440999833)
  ·
    refine ⟨160801954944445189080749875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214402606592593585440999833 160801954944445189080749875)
    ·
      refine ⟨241202932416667783621124813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160801954944445189080749875 241202932416667783621124813)
      ·
        refine ⟨90451099656250418857921805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241202932416667783621124813 90451099656250418857921805)
        ·
          refine ⟨33919162371093907071720677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90451099656250418857921805 33919162371093907071720677)
          ·
            refine ⟨6359842944580107575947627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33919162371093907071720677 6359842944580107575947627)
            ·
              refine ⟨9539764416870161363921441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359842944580107575947627 9539764416870161363921441)
              ·
                refine ⟨7154823312652621022941081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9539764416870161363921441 7154823312652621022941081)
                ·
                  refine ⟨5366117484489465767205811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7154823312652621022941081 5366117484489465767205811)
                  ·
                    refine ⟨8049176226734198650808717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366117484489465767205811 8049176226734198650808717)
                    ·
                      refine ⟨3018441085025324494053269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049176226734198650808717 3018441085025324494053269)
                      ·
                        rfl

theorem cell23_5878393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_5878393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878393 prefixEnd_5878393 := by exact prefixLift 5878393
  have htrace : WordTrace (prefixWord ++ tailWord_5878393) baseStart_5878393 baseEnd_5878393 := by
    simpa [prefixWord, tailWord_5878393, baseEnd_5878393] using wordTrace_append hprefix tailTrace_5878393
  have hstable : (prefixWord ++ tailWord_5878393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878393).length < 2 ^ (prefixWord ++ tailWord_5878393).sum := by decide
  have hdescent : baseEnd_5878393 < baseStart_5878393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878410 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_5878410 : Nat := 118140960795 + 5878410 * 2 ^ 59
def prefixEnd_5878410 : Nat := 4983230072969 + 3 ^ 40 * 5878410 * 2
def baseEnd_5878410 : Nat := 3018449814196450927540691

theorem tailTrace_5878410 : CollatzResearch.WordTrace tailWord_5878410 prefixEnd_5878410 3018449814196450927540691 := by
  unfold tailWord_5878410
  simp only [CollatzResearch.WordTrace]
  refine ⟨53600806658382999336092171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142935484422354664896245789 53600806658382999336092171)
  ·
    refine ⟨80401209987574499004138257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53600806658382999336092171 80401209987574499004138257)
    ·
      refine ⟨60300907490680874253103693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80401209987574499004138257 60300907490680874253103693)
      ·
        refine ⟨22612840309005327844913885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60300907490680874253103693 22612840309005327844913885)
        ·
          refine ⟨8479815115876997941842707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22612840309005327844913885 8479815115876997941842707)
          ·
            refine ⟨12719722673815496912764061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8479815115876997941842707 12719722673815496912764061)
            ·
              refine ⟨4769896002680811342286523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12719722673815496912764061 4769896002680811342286523)
              ·
                refine ⟨7154844004021217013429785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769896002680811342286523 7154844004021217013429785)
                ·
                  refine ⟨5366133003015912760072339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7154844004021217013429785 5366133003015912760072339)
                  ·
                    refine ⟨8049199504523869140108509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366133003015912760072339 8049199504523869140108509)
                    ·
                      refine ⟨3018449814196450927540691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049199504523869140108509 3018449814196450927540691)
                      ·
                        rfl

theorem cell23_5878410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_5878410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878410 prefixEnd_5878410 := by exact prefixLift 5878410
  have htrace : WordTrace (prefixWord ++ tailWord_5878410) baseStart_5878410 baseEnd_5878410 := by
    simpa [prefixWord, tailWord_5878410, baseEnd_5878410] using wordTrace_append hprefix tailTrace_5878410
  have hstable : (prefixWord ++ tailWord_5878410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878410).length < 2 ^ (prefixWord ++ tailWord_5878410).sum := by decide
  have hdescent : baseEnd_5878410 < baseStart_5878410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878412 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_5878412 : Nat := 118140960795 + 5878412 * 2 ^ 59
def prefixEnd_5878412 : Nat := 4983230072969 + 3 ^ 40 * 5878412 * 2
def baseEnd_5878412 : Nat := 3018450841157759919715681

theorem tailTrace_5878412 : CollatzResearch.WordTrace tailWord_5878412 prefixEnd_5878412 3018450841157759919715681 := by
  unfold tailWord_5878412
  simp only [CollatzResearch.WordTrace]
  refine ⟨107201649789762375842970745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142935533053016501123960993 107201649789762375842970745)
  ·
    refine ⟨80401237342321781882228059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107201649789762375842970745 80401237342321781882228059)
    ·
      refine ⟨120601856013482672823342089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80401237342321781882228059 120601856013482672823342089)
      ·
        refine ⟨90451392010112004617506567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120601856013482672823342089 90451392010112004617506567)
        ·
          refine ⟨135677088015168006926259851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90451392010112004617506567 135677088015168006926259851)
          ·
            refine ⟨203515632022752010389389777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135677088015168006926259851 203515632022752010389389777)
            ·
              refine ⟨152636724017064007792042333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203515632022752010389389777 152636724017064007792042333)
              ·
                refine ⟨57238771506399002922015875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152636724017064007792042333 57238771506399002922015875)
                ·
                  refine ⟨85858157259598504383023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57238771506399002922015875 85858157259598504383023813)
                  ·
                    refine ⟨16098404486174719571816965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85858157259598504383023813 16098404486174719571816965)
                    ·
                      refine ⟨3018450841157759919715681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16098404486174719571816965 3018450841157759919715681)
                      ·
                        rfl

theorem cell23_5878412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_5878412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878412 prefixEnd_5878412 := by exact prefixLift 5878412
  have htrace : WordTrace (prefixWord ++ tailWord_5878412) baseStart_5878412 baseEnd_5878412 := by
    simpa [prefixWord, tailWord_5878412, baseEnd_5878412] using wordTrace_append hprefix tailTrace_5878412
  have hstable : (prefixWord ++ tailWord_5878412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878412).length < 2 ^ (prefixWord ++ tailWord_5878412).sum := by decide
  have hdescent : baseEnd_5878412 < baseStart_5878412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878420 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5878420 : Nat := 118140960795 + 5878420 * 2 ^ 59
def prefixEnd_5878420 : Nat := 4983230072969 + 3 ^ 40 * 5878420 * 2
def baseEnd_5878420 : Nat := 3018454949002995888415645

theorem tailTrace_5878420 : CollatzResearch.WordTrace tailWord_5878420 prefixEnd_5878420 3018454949002995888415645 := by
  unfold tailWord_5878420
  simp only [CollatzResearch.WordTrace]
  refine ⟨107201795681747884526116357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142935727575663846034821809 107201795681747884526116357)
  ·
    refine ⟨20100336690327728348646817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107201795681747884526116357 20100336690327728348646817)
    ·
      refine ⟨15075252517745796261485113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20100336690327728348646817 15075252517745796261485113)
      ·
        refine ⟨11306439388309347196113835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15075252517745796261485113 11306439388309347196113835)
        ·
          refine ⟨16959659082464020794170753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11306439388309347196113835 16959659082464020794170753)
          ·
            refine ⟨12719744311848015595628065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16959659082464020794170753 12719744311848015595628065)
            ·
              refine ⟨9539808233886011696721049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12719744311848015595628065 9539808233886011696721049)
              ·
                refine ⟨7154856175414508772540787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9539808233886011696721049 7154856175414508772540787)
                ·
                  refine ⟨10732284263121763158811181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7154856175414508772540787 10732284263121763158811181)
                  ·
                    refine ⟨4024606598670661184554193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10732284263121763158811181 4024606598670661184554193)
                    ·
                      refine ⟨3018454949002995888415645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024606598670661184554193 3018454949002995888415645)
                      ·
                        rfl

theorem cell23_5878420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5878420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878420 prefixEnd_5878420 := by exact prefixLift 5878420
  have htrace : WordTrace (prefixWord ++ tailWord_5878420) baseStart_5878420 baseEnd_5878420 := by
    simpa [prefixWord, tailWord_5878420, baseEnd_5878420] using wordTrace_append hprefix tailTrace_5878420
  have hstable : (prefixWord ++ tailWord_5878420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878420).length < 2 ^ (prefixWord ++ tailWord_5878420).sum := by decide
  have hdescent : baseEnd_5878420 < baseStart_5878420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878506 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_5878506 : Nat := 118140960795 + 5878506 * 2 ^ 59
def prefixEnd_5878506 : Nat := 4983230072969 + 3 ^ 40 * 5878506 * 2
def baseEnd_5878506 : Nat := 3018499108339282551940249

theorem tailTrace_5878506 : CollatzResearch.WordTrace tailWord_5878506 prefixEnd_5878506 3018499108339282551940249 := by
  unfold tailWord_5878506
  simp only [CollatzResearch.WordTrace]
  refine ⟨53601682010296051434965843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142937818694122803826575581 53601682010296051434965843)
  ·
    refine ⟨80402523015444077152448765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53601682010296051434965843 80402523015444077152448765)
    ·
      refine ⟨30150946130791528932168287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80402523015444077152448765 30150946130791528932168287)
      ·
        refine ⟨45226419196187293398252431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30150946130791528932168287 45226419196187293398252431)
        ·
          refine ⟨67839628794280940097378647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45226419196187293398252431 67839628794280940097378647)
          ·
            refine ⟨101759443191421410146067971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67839628794280940097378647 101759443191421410146067971)
            ·
              refine ⟨152639164787132115219101957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101759443191421410146067971 152639164787132115219101957)
              ·
                refine ⟨28619843397587271603581617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152639164787132115219101957 28619843397587271603581617)
                ·
                  refine ⟨21464882548190453702686213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28619843397587271603581617 21464882548190453702686213)
                  ·
                    refine ⟨4024665477785710069253665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21464882548190453702686213 4024665477785710069253665)
                    ·
                      refine ⟨3018499108339282551940249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4024665477785710069253665 3018499108339282551940249)
                      ·
                        rfl

theorem cell23_5878506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_5878506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878506 prefixEnd_5878506 := by exact prefixLift 5878506
  have htrace : WordTrace (prefixWord ++ tailWord_5878506) baseStart_5878506 baseEnd_5878506 := by
    simpa [prefixWord, tailWord_5878506, baseEnd_5878506] using wordTrace_append hprefix tailTrace_5878506
  have hstable : (prefixWord ++ tailWord_5878506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878506).length < 2 ^ (prefixWord ++ tailWord_5878506).sum := by decide
  have hdescent : baseEnd_5878506 < baseStart_5878506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878509 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5878509 : Nat := 118140960795 + 5878509 * 2 ^ 59
def prefixEnd_5878509 : Nat := 4983230072969 + 3 ^ 40 * 5878509 * 2
def baseEnd_5878509 : Nat := 3018500648781246040202735

theorem tailTrace_5878509 : CollatzResearch.WordTrace tailWord_5878509 prefixEnd_5878509 3018500648781246040202735 := by
  unfold tailWord_5878509
  simp only [CollatzResearch.WordTrace]
  refine ⟨214406837460173337252222581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142937891640115558168148387 214406837460173337252222581)
  ·
    refine ⟨20100641011891250367395867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 214406837460173337252222581 20100641011891250367395867)
    ·
      refine ⟨30150961517836875551093801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20100641011891250367395867 30150961517836875551093801)
      ·
        refine ⟨22613221138377656663320351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30150961517836875551093801 22613221138377656663320351)
        ·
          refine ⟨33919831707566484994980527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22613221138377656663320351 33919831707566484994980527)
          ·
            refine ⟨50879747561349727492470791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33919831707566484994980527 50879747561349727492470791)
            ·
              refine ⟨76319621342024591238706187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50879747561349727492470791 76319621342024591238706187)
              ·
                refine ⟨114479432013036886858059281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76319621342024591238706187 114479432013036886858059281)
                ·
                  refine ⟨85859574009777665143544461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114479432013036886858059281 85859574009777665143544461)
                  ·
                    refine ⟨32197340253666624428829173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85859574009777665143544461 32197340253666624428829173)
                    ·
                      refine ⟨3018500648781246040202735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32197340253666624428829173 3018500648781246040202735)
                      ·
                        rfl

theorem cell23_5878509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5878509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878509 prefixEnd_5878509 := by exact prefixLift 5878509
  have htrace : WordTrace (prefixWord ++ tailWord_5878509) baseStart_5878509 baseEnd_5878509 := by
    simpa [prefixWord, tailWord_5878509, baseEnd_5878509] using wordTrace_append hprefix tailTrace_5878509
  have hstable : (prefixWord ++ tailWord_5878509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878509).length < 2 ^ (prefixWord ++ tailWord_5878509).sum := by decide
  have hdescent : baseEnd_5878509 < baseStart_5878509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878580 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 6]
def baseStart_5878580 : Nat := 118140960795 + 5878580 * 2 ^ 59
def prefixEnd_5878580 : Nat := 4983230072969 + 3 ^ 40 * 5878580 * 2
def baseEnd_5878580 : Nat := 335393011767523918046101

theorem tailTrace_5878580 : CollatzResearch.WordTrace tailWord_5878580 prefixEnd_5878580 335393011767523918046101 := by
  unfold tailWord_5878580
  simp only [CollatzResearch.WordTrace]
  refine ⟨107204713521458058189028597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142939618028610744252038129 107204713521458058189028597)
  ·
    refine ⟨10050441892636692955221431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107204713521458058189028597 10050441892636692955221431)
    ·
      refine ⟨15075662838955039432832147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10050441892636692955221431 15075662838955039432832147)
      ·
        refine ⟨22613494258432559149248221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15075662838955039432832147 22613494258432559149248221)
        ·
          refine ⟨8480060346912209680968083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22613494258432559149248221 8480060346912209680968083)
          ·
            refine ⟨12720090520368314521452125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8480060346912209680968083 12720090520368314521452125)
            ·
              refine ⟨4770033945138117945544547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12720090520368314521452125 4770033945138117945544547)
              ·
                refine ⟨7155050917707176918316821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770033945138117945544547 7155050917707176918316821)
                ·
                  refine ⟨335393011767523918046101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7155050917707176918316821 335393011767523918046101)
                  ·
                    rfl

theorem cell23_5878580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_5878580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878580 prefixEnd_5878580 := by exact prefixLift 5878580
  have htrace : WordTrace (prefixWord ++ tailWord_5878580) baseStart_5878580 baseEnd_5878580 := by
    simpa [prefixWord, tailWord_5878580, baseEnd_5878580] using wordTrace_append hprefix tailTrace_5878580
  have hstable : (prefixWord ++ tailWord_5878580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878580).length < 2 ^ (prefixWord ++ tailWord_5878580).sum := by decide
  have hdescent : baseEnd_5878580 < baseStart_5878580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878599 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_5878599 : Nat := 118140960795 + 5878599 * 2 ^ 59
def prefixEnd_5878599 : Nat := 4983230072969 + 3 ^ 40 * 5878599 * 2
def baseEnd_5878599 : Nat := 3018546862040150688077321

theorem tailTrace_5878599 : CollatzResearch.WordTrace tailWord_5878599 prefixEnd_5878599 3018546862040150688077321 := by
  unfold tailWord_5878599
  simp only [CollatzResearch.WordTrace]
  refine ⟨214410120029847282622998851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142940080019898188415332567 214410120029847282622998851)
  ·
    refine ⟨321615180044770923934498277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214410120029847282622998851 321615180044770923934498277)
    ·
      refine ⟨60302846258394548237718427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321615180044770923934498277 60302846258394548237718427)
      ·
        refine ⟨90454269387591822356577641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60302846258394548237718427 90454269387591822356577641)
        ·
          refine ⟨67840702040693866767433231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90454269387591822356577641 67840702040693866767433231)
          ·
            refine ⟨101761053061040800151149847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67840702040693866767433231 101761053061040800151149847)
            ·
              refine ⟨152641579591561200226724771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101761053061040800151149847 152641579591561200226724771)
              ·
                refine ⟨228962369387341800340087157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152641579591561200226724771 228962369387341800340087157)
                ·
                  refine ⟨21465222130063293781883171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228962369387341800340087157 21465222130063293781883171)
                  ·
                    refine ⟨32197833195094940672824757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21465222130063293781883171 32197833195094940672824757)
                    ·
                      refine ⟨3018546862040150688077321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32197833195094940672824757 3018546862040150688077321)
                      ·
                        rfl

theorem cell23_5878599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_5878599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878599 prefixEnd_5878599 := by exact prefixLift 5878599
  have htrace : WordTrace (prefixWord ++ tailWord_5878599) baseStart_5878599 baseEnd_5878599 := by
    simpa [prefixWord, tailWord_5878599, baseEnd_5878599] using wordTrace_append hprefix tailTrace_5878599
  have hstable : (prefixWord ++ tailWord_5878599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878599).length < 2 ^ (prefixWord ++ tailWord_5878599).sum := by decide
  have hdescent : baseEnd_5878599 < baseStart_5878599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5878663 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_5878663 : Nat := 118140960795 + 5878663 * 2 ^ 59
def prefixEnd_5878663 : Nat := 4983230072969 + 3 ^ 40 * 5878663 * 2
def baseEnd_5878663 : Nat := 3018579724802038437677027

theorem tailTrace_5878663 : CollatzResearch.WordTrace tailWord_5878663 prefixEnd_5878663 3018579724802038437677027 := by
  unfold tailWord_5878663
  simp only [CollatzResearch.WordTrace]
  refine ⟨214412454301615421553328643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142941636201076947702219095 214412454301615421553328643)
  ·
    refine ⟨321618681452423132329992965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214412454301615421553328643 321618681452423132329992965)
    ·
      refine ⟨60303502772329337311873681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 321618681452423132329992965 60303502772329337311873681)
      ·
        refine ⟨45227627079247002983905261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60303502772329337311873681 45227627079247002983905261)
        ·
          refine ⟨16960360154717626118964473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45227627079247002983905261 16960360154717626118964473)
          ·
            refine ⟨12720270116038219589223355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16960360154717626118964473 12720270116038219589223355)
            ·
              refine ⟨19080405174057329383835033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12720270116038219589223355 19080405174057329383835033)
              ·
                refine ⟨14310303880542997037876275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19080405174057329383835033 14310303880542997037876275)
                ·
                  refine ⟨21465455820814495556814413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14310303880542997037876275 21465455820814495556814413)
                  ·
                    refine ⟨8049545932805435833805405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21465455820814495556814413 8049545932805435833805405)
                    ·
                      refine ⟨3018579724802038437677027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8049545932805435833805405 3018579724802038437677027)
                      ·
                        rfl

theorem cell23_5878663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_5878663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5878663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5878663 prefixEnd_5878663 := by exact prefixLift 5878663
  have htrace : WordTrace (prefixWord ++ tailWord_5878663) baseStart_5878663 baseEnd_5878663 := by
    simpa [prefixWord, tailWord_5878663, baseEnd_5878663] using wordTrace_append hprefix tailTrace_5878663
  have hstable : (prefixWord ++ tailWord_5878663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5878663).length < 2 ^ (prefixWord ++ tailWord_5878663).sum := by decide
  have hdescent : baseEnd_5878663 < baseStart_5878663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5878663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
