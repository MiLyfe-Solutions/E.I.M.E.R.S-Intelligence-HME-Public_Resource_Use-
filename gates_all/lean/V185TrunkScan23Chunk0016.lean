import V185TrunkScan23Chunk0015

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_95018 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_95018 : Nat := 118140960795 + 95018 * 2 ^ 59
def prefixEnd_95018 : Nat := 4983230072969 + 3 ^ 40 * 95018 * 2
def baseEnd_95018 : Nat := 48789904829014475338027

theorem tailTrace_95018 : CollatzResearch.WordTrace tailWord_95018 prefixEnd_95018 48789904829014475338027 := by
  unfold tailWord_95018
  simp only [CollatzResearch.WordTrace]
  refine ⟨866397792443372156887427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2310394113182325751699805 866397792443372156887427)
  ·
    refine ⟨1299596688665058235331141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 866397792443372156887427 1299596688665058235331141)
    ·
      refine ⟨243674379124698419124589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1299596688665058235331141 243674379124698419124589)
      ·
        refine ⟨91377892171761907171721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243674379124698419124589 91377892171761907171721)
        ·
          refine ⟨68533419128821430378791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91377892171761907171721 68533419128821430378791)
          ·
            refine ⟨102800128693232145568187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68533419128821430378791 102800128693232145568187)
            ·
              refine ⟨154200193039848218352281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102800128693232145568187 154200193039848218352281)
              ·
                refine ⟨115650144779886163764211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154200193039848218352281 115650144779886163764211)
                ·
                  refine ⟨173475217169829245646317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115650144779886163764211 173475217169829245646317)
                  ·
                    refine ⟨65053206438685967117369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173475217169829245646317 65053206438685967117369)
                    ·
                      refine ⟨48789904829014475338027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65053206438685967117369 48789904829014475338027)
                      ·
                        rfl

theorem cell23_95018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_95018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95018 prefixEnd_95018 := by exact prefixLift 95018
  have htrace : WordTrace (prefixWord ++ tailWord_95018) baseStart_95018 baseEnd_95018 := by
    simpa [prefixWord, tailWord_95018, baseEnd_95018] using wordTrace_append hprefix tailTrace_95018
  have hstable : (prefixWord ++ tailWord_95018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95018).length < 2 ^ (prefixWord ++ tailWord_95018).sum := by decide
  have hdescent : baseEnd_95018 < baseStart_95018 := by decide
  rcases family_descends (prefixWord ++ tailWord_95018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95080 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 5, 4]
def baseStart_95080 : Nat := 118140960795 + 95080 * 2 ^ 59
def prefixEnd_95080 : Nat := 4983230072969 + 3 ^ 40 * 95080 * 2
def baseEnd_95080 : Nat := 16273913543197744254247

theorem tailTrace_95080 : CollatzResearch.WordTrace tailWord_95080 prefixEnd_95080 16273913543197744254247 := by
  unfold tailWord_95080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733926247774436608153347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2311901663699248810871129 1733926247774436608153347)
  ·
    refine ⟨2600889371661654912230021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733926247774436608153347 2600889371661654912230021)
    ·
      refine ⟨487666757186560296043129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2600889371661654912230021 487666757186560296043129)
      ·
        refine ⟨365750067889920222032347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487666757186560296043129 365750067889920222032347)
        ·
          refine ⟨548625101834880333048521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365750067889920222032347 548625101834880333048521)
          ·
            refine ⟨411468826376160249786391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548625101834880333048521 411468826376160249786391)
            ·
              refine ⟨617203239564240374679587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411468826376160249786391 617203239564240374679587)
              ·
                refine ⟨925804859346360562019381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617203239564240374679587 925804859346360562019381)
                ·
                  refine ⟨86794205563721302689317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 925804859346360562019381 86794205563721302689317)
                  ·
                    refine ⟨16273913543197744254247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86794205563721302689317 16273913543197744254247)
                    ·
                      rfl

theorem cell23_95080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_95080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95080 prefixEnd_95080 := by exact prefixLift 95080
  have htrace : WordTrace (prefixWord ++ tailWord_95080) baseStart_95080 baseEnd_95080 := by
    simpa [prefixWord, tailWord_95080, baseEnd_95080] using wordTrace_append hprefix tailTrace_95080
  have hstable : (prefixWord ++ tailWord_95080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95080).length < 2 ^ (prefixWord ++ tailWord_95080).sum := by decide
  have hdescent : baseEnd_95080 < baseStart_95080 := by decide
  rcases family_descends (prefixWord ++ tailWord_95080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95097 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 1, 4]
def baseStart_95097 : Nat := 118140960795 + 95097 * 2 ^ 59
def prefixEnd_95097 : Nat := 4983230072969 + 3 ^ 40 * 95097 * 2
def baseEnd_95097 : Nat := 16276823266906555416721

theorem tailTrace_95097 : CollatzResearch.WordTrace tailWord_95097 prefixEnd_95097 16276823266906555416721 := by
  unfold tailWord_95097
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468472536487285119675545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2312315024324856746450363 3468472536487285119675545)
  ·
    refine ⟨2601354402365463839756659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3468472536487285119675545 2601354402365463839756659)
    ·
      refine ⟨3902031603548195759634989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2601354402365463839756659 3902031603548195759634989)
      ·
        refine ⟨1463261851330573409863121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3902031603548195759634989 1463261851330573409863121)
        ·
          refine ⟨1097446388497930057397341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463261851330573409863121 1097446388497930057397341)
          ·
            refine ⟨411542395686723771524003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1097446388497930057397341 411542395686723771524003)
            ·
              refine ⟨617313593530085657286005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411542395686723771524003 617313593530085657286005)
              ·
                refine ⟨57873149393445530370563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617313593530085657286005 57873149393445530370563)
                ·
                  refine ⟨86809724090168295555845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57873149393445530370563 86809724090168295555845)
                  ·
                    refine ⟨16276823266906555416721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86809724090168295555845 16276823266906555416721)
                    ·
                      rfl

theorem cell23_95097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 1, 4].length) (baseStart_95097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95097 prefixEnd_95097 := by exact prefixLift 95097
  have htrace : WordTrace (prefixWord ++ tailWord_95097) baseStart_95097 baseEnd_95097 := by
    simpa [prefixWord, tailWord_95097, baseEnd_95097] using wordTrace_append hprefix tailTrace_95097
  have hstable : (prefixWord ++ tailWord_95097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95097).length < 2 ^ (prefixWord ++ tailWord_95097).sum := by decide
  have hdescent : baseEnd_95097 < baseStart_95097 := by decide
  rcases family_descends (prefixWord ++ tailWord_95097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95113 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_95113 : Nat := 118140960795 + 95113 * 2 ^ 59
def prefixEnd_95113 : Nat := 4983230072969 + 3 ^ 40 * 95113 * 2
def baseEnd_95113 : Nat := 48838685491191603650089

theorem tailTrace_95113 : CollatzResearch.WordTrace tailWord_95113 prefixEnd_95113 48838685491191603650089 := by
  unfold tailWord_95113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3469056104429319852257993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2312704069619546568171995 3469056104429319852257993)
  ·
    refine ⟨2601792078321989889193495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3469056104429319852257993 2601792078321989889193495)
    ·
      refine ⟨3902688117482984833790243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2601792078321989889193495 3902688117482984833790243)
      ·
        refine ⟨5854032176224477250685365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3902688117482984833790243 5854032176224477250685365)
        ·
          refine ⟨548815516521044742251753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5854032176224477250685365 548815516521044742251753)
          ·
            refine ⟨411611637390783556688815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548815516521044742251753 411611637390783556688815)
            ·
              refine ⟨617417456086175335033223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411611637390783556688815 617417456086175335033223)
              ·
                refine ⟨926126184129263002549835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617417456086175335033223 926126184129263002549835)
                ·
                  refine ⟨1389189276193894503824753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926126184129263002549835 1389189276193894503824753)
                  ·
                    refine ⟨1041891957145420877868565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1389189276193894503824753 1041891957145420877868565)
                    ·
                      refine ⟨48838685491191603650089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1041891957145420877868565 48838685491191603650089)
                      ·
                        rfl

theorem cell23_95113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_95113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95113 prefixEnd_95113 := by exact prefixLift 95113
  have htrace : WordTrace (prefixWord ++ tailWord_95113) baseStart_95113 baseEnd_95113 := by
    simpa [prefixWord, tailWord_95113, baseEnd_95113] using wordTrace_append hprefix tailTrace_95113
  have hstable : (prefixWord ++ tailWord_95113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95113).length < 2 ^ (prefixWord ++ tailWord_95113).sum := by decide
  have hdescent : baseEnd_95113 < baseStart_95113 := by decide
  rcases family_descends (prefixWord ++ tailWord_95113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95114 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_95114 : Nat := 118140960795 + 95114 * 2 ^ 59
def prefixEnd_95114 : Nat := 4983230072969 + 3 ^ 40 * 95114 * 2
def baseEnd_95114 : Nat := 16279732990615366579195

theorem tailTrace_95114 : CollatzResearch.WordTrace tailWord_95114 prefixEnd_95114 16279732990615366579195 := by
  unfold tailWord_95114
  simp only [CollatzResearch.WordTrace]
  refine ⟨867273144356424255761099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2312728384950464682029597 867273144356424255761099)
  ·
    refine ⟨1300909716534636383641649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867273144356424255761099 1300909716534636383641649)
    ·
      refine ⟨975682287400977287731237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1300909716534636383641649 975682287400977287731237)
      ·
        refine ⟨182940428887683241449607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 975682287400977287731237 182940428887683241449607)
        ·
          refine ⟨274410643331524862174411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182940428887683241449607 274410643331524862174411)
          ·
            refine ⟨411615964997287293261617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274410643331524862174411 411615964997287293261617)
            ·
              refine ⟨308711973747965469946213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411615964997287293261617 308711973747965469946213)
              ·
                refine ⟨57883495077743525614915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308711973747965469946213 57883495077743525614915)
                ·
                  refine ⟨86825242616615288422373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57883495077743525614915 86825242616615288422373)
                  ·
                    refine ⟨16279732990615366579195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86825242616615288422373 16279732990615366579195)
                    ·
                      rfl

theorem cell23_95114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_95114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95114 prefixEnd_95114 := by exact prefixLift 95114
  have htrace : WordTrace (prefixWord ++ tailWord_95114) baseStart_95114 baseEnd_95114 := by
    simpa [prefixWord, tailWord_95114, baseEnd_95114] using wordTrace_append hprefix tailTrace_95114
  have hstable : (prefixWord ++ tailWord_95114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95114).length < 2 ^ (prefixWord ++ tailWord_95114).sum := by decide
  have hdescent : baseEnd_95114 < baseStart_95114 := by decide
  rcases family_descends (prefixWord ++ tailWord_95114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95123 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 3, 5]
def baseStart_95123 : Nat := 118140960795 + 95123 * 2 ^ 59
def prefixEnd_95123 : Nat := 4983230072969 + 3 ^ 40 * 95123 * 2
def baseEnd_95123 : Nat := 16281273432578854841681

theorem tailTrace_95123 : CollatzResearch.WordTrace tailWord_95123 prefixEnd_95123 16281273432578854841681 := by
  unfold tailWord_95123
  simp only [CollatzResearch.WordTrace]
  refine ⟨3469420834393091560122023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2312947222928727706748015 3469420834393091560122023)
  ·
    refine ⟨5204131251589637340183035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3469420834393091560122023 5204131251589637340183035)
    ·
      refine ⟨7806196877384456010274553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5204131251589637340183035 7806196877384456010274553)
      ·
        refine ⟨5854647658038342007705915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7806196877384456010274553 5854647658038342007705915)
        ·
          refine ⟨8781971487057513011558873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5854647658038342007705915 8781971487057513011558873)
          ·
            refine ⟨6586478615293134758669155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8781971487057513011558873 6586478615293134758669155)
            ·
              refine ⟨9879717922939702138003733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586478615293134758669155 9879717922939702138003733)
              ·
                refine ⟨463111777637798537718925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9879717922939702138003733 463111777637798537718925)
                ·
                  refine ⟨173666916614174451644597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463111777637798537718925 173666916614174451644597)
                  ·
                    refine ⟨16281273432578854841681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173666916614174451644597 16281273432578854841681)
                    ·
                      rfl

theorem cell23_95123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 5].length) (baseStart_95123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95123 prefixEnd_95123 := by exact prefixLift 95123
  have htrace : WordTrace (prefixWord ++ tailWord_95123) baseStart_95123 baseEnd_95123 := by
    simpa [prefixWord, tailWord_95123, baseEnd_95123] using wordTrace_append hprefix tailTrace_95123
  have hstable : (prefixWord ++ tailWord_95123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95123).length < 2 ^ (prefixWord ++ tailWord_95123).sum := by decide
  have hdescent : baseEnd_95123 < baseStart_95123 := by decide
  rcases family_descends (prefixWord ++ tailWord_95123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95158 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_95158 : Nat := 118140960795 + 95158 * 2 ^ 59
def prefixEnd_95158 : Nat := 4983230072969 + 3 ^ 40 * 95158 * 2
def baseEnd_95158 : Nat := 48861792120643927587383

theorem tailTrace_95158 : CollatzResearch.WordTrace tailWord_95158 prefixEnd_95158 48861792120643927587383 := by
  unfold tailWord_95158
  simp only [CollatzResearch.WordTrace]
  refine ⟨216918586829143283602883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2313798259510861691764085 216918586829143283602883)
  ·
    refine ⟨325377880243714925404325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216918586829143283602883 325377880243714925404325)
    ·
      refine ⟨61008352545696548513311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325377880243714925404325 61008352545696548513311)
      ·
        refine ⟨91512528818544822769967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61008352545696548513311 91512528818544822769967)
        ·
          refine ⟨137268793227817234154951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91512528818544822769967 137268793227817234154951)
          ·
            refine ⟨205903189841725851232427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137268793227817234154951 205903189841725851232427)
            ·
              refine ⟨308854784762588776848641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205903189841725851232427 308854784762588776848641)
              ·
                refine ⟨231641088571941582636481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308854784762588776848641 231641088571941582636481)
                ·
                  refine ⟨173730816428956186977361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231641088571941582636481 173730816428956186977361)
                  ·
                    refine ⟨130298112321717140233021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173730816428956186977361 130298112321717140233021)
                    ·
                      refine ⟨48861792120643927587383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 130298112321717140233021 48861792120643927587383)
                      ·
                        rfl

theorem cell23_95158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_95158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95158 prefixEnd_95158 := by exact prefixLift 95158
  have htrace : WordTrace (prefixWord ++ tailWord_95158) baseStart_95158 baseEnd_95158 := by
    simpa [prefixWord, tailWord_95158, baseEnd_95158] using wordTrace_append hprefix tailTrace_95158
  have hstable : (prefixWord ++ tailWord_95158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95158).length < 2 ^ (prefixWord ++ tailWord_95158).sum := by decide
  have hdescent : baseEnd_95158 < baseStart_95158 := by decide
  rcases family_descends (prefixWord ++ tailWord_95158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95180 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_95180 : Nat := 118140960795 + 95180 * 2 ^ 59
def prefixEnd_95180 : Nat := 4983230072969 + 3 ^ 40 * 95180 * 2
def baseEnd_95180 : Nat := 48873088695042841512281

theorem tailTrace_95180 : CollatzResearch.WordTrace tailWord_95180 prefixEnd_95180 48873088695042841512281 := by
  unfold tailWord_95180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735749897593295147473497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2314333196791060196631329 1735749897593295147473497)
  ·
    refine ⟨1301812423194971360605123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1735749897593295147473497 1301812423194971360605123)
    ·
      refine ⟨1952718634792457040907685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301812423194971360605123 1952718634792457040907685)
      ·
        refine ⟨366134744023585695170191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1952718634792457040907685 366134744023585695170191)
        ·
          refine ⟨549202116035378542755287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366134744023585695170191 549202116035378542755287)
          ·
            refine ⟨823803174053067814132931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549202116035378542755287 823803174053067814132931)
            ·
              refine ⟨1235704761079601721199397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823803174053067814132931 1235704761079601721199397)
              ·
                refine ⟨231694642702425322724887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1235704761079601721199397 231694642702425322724887)
                ·
                  refine ⟨347541964053637984087331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231694642702425322724887 347541964053637984087331)
                  ·
                    refine ⟨521312946080456976130997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347541964053637984087331 521312946080456976130997)
                    ·
                      refine ⟨48873088695042841512281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 521312946080456976130997 48873088695042841512281)
                      ·
                        rfl

theorem cell23_95180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_95180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95180 prefixEnd_95180 := by exact prefixLift 95180
  have htrace : WordTrace (prefixWord ++ tailWord_95180) baseStart_95180 baseEnd_95180 := by
    simpa [prefixWord, tailWord_95180, baseEnd_95180] using wordTrace_append hprefix tailTrace_95180
  have hstable : (prefixWord ++ tailWord_95180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95180).length < 2 ^ (prefixWord ++ tailWord_95180).sum := by decide
  have hdescent : baseEnd_95180 < baseStart_95180 := by decide
  rcases family_descends (prefixWord ++ tailWord_95180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95183 : List Nat := [1, 1, 2, 1, 1, 6, 1, 10]
def baseStart_95183 : Nat := 118140960795 + 95183 * 2 ^ 59
def prefixEnd_95183 : Nat := 4983230072969 + 3 ^ 40 * 95183 * 2
def baseEnd_95183 : Nat := 1810171449518752954621

theorem tailTrace_95183 : CollatzResearch.WordTrace tailWord_95183 prefixEnd_95183 1810171449518752954621 := by
  unfold tailWord_95183
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471609214175721807306203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2314406142783814538204135 3471609214175721807306203)
  ·
    refine ⟨5207413821263582710959305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471609214175721807306203 5207413821263582710959305)
    ·
      refine ⟨3905560365947687033219479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5207413821263582710959305 3905560365947687033219479)
      ·
        refine ⟨5858340548921530549829219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905560365947687033219479 5858340548921530549829219)
        ·
          refine ⟨8787510823382295824743829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5858340548921530549829219 8787510823382295824743829)
          ·
            refine ⟨411914569846045116784867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8787510823382295824743829 411914569846045116784867)
            ·
              refine ⟨617871854769067675177301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411914569846045116784867 617871854769067675177301)
              ·
                refine ⟨1810171449518752954621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 617871854769067675177301 1810171449518752954621)
                ·
                  rfl

theorem cell23_95183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 10].length) (baseStart_95183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95183 prefixEnd_95183 := by exact prefixLift 95183
  have htrace : WordTrace (prefixWord ++ tailWord_95183) baseStart_95183 baseEnd_95183 := by
    simpa [prefixWord, tailWord_95183, baseEnd_95183] using wordTrace_append hprefix tailTrace_95183
  have hstable : (prefixWord ++ tailWord_95183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95183).length < 2 ^ (prefixWord ++ tailWord_95183).sum := by decide
  have hdescent : baseEnd_95183 < baseStart_95183 := by decide
  rcases family_descends (prefixWord ++ tailWord_95183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95194 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_95194 : Nat := 118140960795 + 95194 * 2 ^ 59
def prefixEnd_95194 : Nat := 4983230072969 + 3 ^ 40 * 95194 * 2
def baseEnd_95194 : Nat := 48880277424205786737217

theorem tailTrace_95194 : CollatzResearch.WordTrace tailWord_95194 prefixEnd_95194 48880277424205786737217 := by
  unfold tailWord_95194
  simp only [CollatzResearch.WordTrace]
  refine ⟨868002604283967671489159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2314673611423913790637757 868002604283967671489159)
  ·
    refine ⟨1302003906425951507233739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868002604283967671489159 1302003906425951507233739)
    ·
      refine ⟨1953005859638927260850609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302003906425951507233739 1953005859638927260850609)
      ·
        refine ⟨1464754394729195445637957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1953005859638927260850609 1464754394729195445637957)
        ·
          refine ⟨274641449011724146057117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1464754394729195445637957 274641449011724146057117)
          ·
            refine ⟨102990543379396554771419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274641449011724146057117 102990543379396554771419)
            ·
              refine ⟨154485815069094832157129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102990543379396554771419 154485815069094832157129)
              ·
                refine ⟨115864361301821124117847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154485815069094832157129 115864361301821124117847)
                ·
                  refine ⟨173796541952731686176771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115864361301821124117847 173796541952731686176771)
                  ·
                    refine ⟨260694812929097529265157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173796541952731686176771 260694812929097529265157)
                    ·
                      refine ⟨48880277424205786737217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 260694812929097529265157 48880277424205786737217)
                      ·
                        rfl

theorem cell23_95194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_95194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95194 prefixEnd_95194 := by exact prefixLift 95194
  have htrace : WordTrace (prefixWord ++ tailWord_95194) baseStart_95194 baseEnd_95194 := by
    simpa [prefixWord, tailWord_95194, baseEnd_95194] using wordTrace_append hprefix tailTrace_95194
  have hstable : (prefixWord ++ tailWord_95194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95194).length < 2 ^ (prefixWord ++ tailWord_95194).sum := by decide
  have hdescent : baseEnd_95194 < baseStart_95194 := by decide
  rcases family_descends (prefixWord ++ tailWord_95194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95207 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_95207 : Nat := 118140960795 + 95207 * 2 ^ 59
def prefixEnd_95207 : Nat := 4983230072969 + 3 ^ 40 * 95207 * 2
def baseEnd_95207 : Nat := 48886952672714235874657

theorem tailTrace_95207 : CollatzResearch.WordTrace tailWord_95207 prefixEnd_95207 48886952672714235874657 := by
  unfold tailWord_95207
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472484566088773906179875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2314989710725849270786583 3472484566088773906179875)
  ·
    refine ⟨5208726849133160859269813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3472484566088773906179875 5208726849133160859269813)
    ·
      refine ⟨488318142106233830556545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5208726849133160859269813 488318142106233830556545)
      ·
        refine ⟨366238606579675372917409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488318142106233830556545 366238606579675372917409)
        ·
          refine ⟨274678954934756529688057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366238606579675372917409 274678954934756529688057)
          ·
            refine ⟨206009216201067397266043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274678954934756529688057 206009216201067397266043)
            ·
              refine ⟨309013824301601095899065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206009216201067397266043 309013824301601095899065)
              ·
                refine ⟨231760368226200821924299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309013824301601095899065 231760368226200821924299)
                ·
                  refine ⟨347640552339301232886449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231760368226200821924299 347640552339301232886449)
                  ·
                    refine ⟨260730414254475924664837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 347640552339301232886449 260730414254475924664837)
                    ·
                      refine ⟨48886952672714235874657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 260730414254475924664837 48886952672714235874657)
                      ·
                        rfl

theorem cell23_95207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_95207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95207 prefixEnd_95207 := by exact prefixLift 95207
  have htrace : WordTrace (prefixWord ++ tailWord_95207) baseStart_95207 baseEnd_95207 := by
    simpa [prefixWord, tailWord_95207, baseEnd_95207] using wordTrace_append hprefix tailTrace_95207
  have hstable : (prefixWord ++ tailWord_95207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95207).length < 2 ^ (prefixWord ++ tailWord_95207).sum := by decide
  have hdescent : baseEnd_95207 < baseStart_95207 := by decide
  rcases family_descends (prefixWord ++ tailWord_95207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95214 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_95214 : Nat := 118140960795 + 95214 * 2 ^ 59
def prefixEnd_95214 : Nat := 4983230072969 + 3 ^ 40 * 95214 * 2
def baseEnd_95214 : Nat := 48890547037295708487125

theorem tailTrace_95214 : CollatzResearch.WordTrace tailWord_95214 prefixEnd_95214 48890547037295708487125 := by
  unfold tailWord_95214
  simp only [CollatzResearch.WordTrace]
  refine ⟨434092484632926762710587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2315159918042276067789797 434092484632926762710587)
  ·
    refine ⟨651138726949390144065881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 434092484632926762710587 651138726949390144065881)
    ·
      refine ⟨488354045212042608049411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 651138726949390144065881 488354045212042608049411)
      ·
        refine ⟨732531067818063912074117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488354045212042608049411 732531067818063912074117)
        ·
          refine ⟨137349575215886983513897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 732531067818063912074117 137349575215886983513897)
          ·
            refine ⟨103012181411915237635423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137349575215886983513897 103012181411915237635423)
            ·
              refine ⟨154518272117872856453135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103012181411915237635423 154518272117872856453135)
              ·
                refine ⟨231777408176809284679703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154518272117872856453135 231777408176809284679703)
                ·
                  refine ⟨347666112265213927019555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231777408176809284679703 347666112265213927019555)
                  ·
                    refine ⟨521499168397820890529333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347666112265213927019555 521499168397820890529333)
                    ·
                      refine ⟨48890547037295708487125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 521499168397820890529333 48890547037295708487125)
                      ·
                        rfl

theorem cell23_95214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_95214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95214 prefixEnd_95214 := by exact prefixLift 95214
  have htrace : WordTrace (prefixWord ++ tailWord_95214) baseStart_95214 baseEnd_95214 := by
    simpa [prefixWord, tailWord_95214, baseEnd_95214] using wordTrace_append hprefix tailTrace_95214
  have hstable : (prefixWord ++ tailWord_95214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95214).length < 2 ^ (prefixWord ++ tailWord_95214).sum := by decide
  have hdescent : baseEnd_95214 < baseStart_95214 := by decide
  rcases family_descends (prefixWord ++ tailWord_95214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95223 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_95223 : Nat := 118140960795 + 95223 * 2 ^ 59
def prefixEnd_95223 : Nat := 4983230072969 + 3 ^ 40 * 95223 * 2
def baseEnd_95223 : Nat := 48895168363186173274583

theorem tailTrace_95223 : CollatzResearch.WordTrace tailWord_95223 prefixEnd_95223 48895168363186173274583 := by
  unfold tailWord_95223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473068134030808638762323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2315378756020539092508215 3473068134030808638762323)
  ·
    refine ⟨5209602201046212958143485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3473068134030808638762323 5209602201046212958143485)
    ·
      refine ⟨1953600825392329859303807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5209602201046212958143485 1953600825392329859303807)
      ·
        refine ⟨2930401238088494788955711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953600825392329859303807 2930401238088494788955711)
        ·
          refine ⟨4395601857132742183433567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930401238088494788955711 4395601857132742183433567)
          ·
            refine ⟨6593402785699113275150351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395601857132742183433567 6593402785699113275150351)
            ·
              refine ⟨9890104178548669912725527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593402785699113275150351 9890104178548669912725527)
              ·
                refine ⟨14835156267823004869088291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890104178548669912725527 14835156267823004869088291)
                ·
                  refine ⟨22252734401734507303632437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14835156267823004869088291 22252734401734507303632437)
                  ·
                    refine ⟨2086193850162610059715541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22252734401734507303632437 2086193850162610059715541)
                    ·
                      refine ⟨48895168363186173274583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2086193850162610059715541 48895168363186173274583)
                      ·
                        rfl

theorem cell23_95223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_95223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95223 prefixEnd_95223 := by exact prefixLift 95223
  have htrace : WordTrace (prefixWord ++ tailWord_95223) baseStart_95223 baseEnd_95223 := by
    simpa [prefixWord, tailWord_95223, baseEnd_95223] using wordTrace_append hprefix tailTrace_95223
  have hstable : (prefixWord ++ tailWord_95223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95223).length < 2 ^ (prefixWord ++ tailWord_95223).sum := by decide
  have hdescent : baseEnd_95223 < baseStart_95223 := by decide
  rcases family_descends (prefixWord ++ tailWord_95223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95228 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_95228 : Nat := 118140960795 + 95228 * 2 ^ 59
def prefixEnd_95228 : Nat := 4983230072969 + 3 ^ 40 * 95228 * 2
def baseEnd_95228 : Nat := 48897735766458653712061

theorem tailTrace_95228 : CollatzResearch.WordTrace tailWord_95228 prefixEnd_95228 48897735766458653712061 := by
  unfold tailWord_95228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736625249506347246347169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2315500332675129661796225 1736625249506347246347169)
  ·
    refine ⟨1302468937129760434760377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1736625249506347246347169 1302468937129760434760377)
    ·
      refine ⟨976851702847320326070283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1302468937129760434760377 976851702847320326070283)
      ·
        refine ⟨1465277554270980489105425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976851702847320326070283 1465277554270980489105425)
        ·
          refine ⟨1098958165703235366829069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1465277554270980489105425 1098958165703235366829069)
          ·
            refine ⟨412109312138713262560901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1098958165703235366829069 412109312138713262560901)
            ·
              refine ⟨77270496026008736730169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 412109312138713262560901 77270496026008736730169)
              ·
                refine ⟨57952872019506552547627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77270496026008736730169 57952872019506552547627)
                ·
                  refine ⟨86929308029259828821441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57952872019506552547627 86929308029259828821441)
                  ·
                    refine ⟨65196981021944871616081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86929308029259828821441 65196981021944871616081)
                    ·
                      refine ⟨48897735766458653712061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65196981021944871616081 48897735766458653712061)
                      ·
                        rfl

theorem cell23_95228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_95228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95228 prefixEnd_95228 := by exact prefixLift 95228
  have htrace : WordTrace (prefixWord ++ tailWord_95228) baseStart_95228 baseEnd_95228 := by
    simpa [prefixWord, tailWord_95228, baseEnd_95228] using wordTrace_append hprefix tailTrace_95228
  have hstable : (prefixWord ++ tailWord_95228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95228).length < 2 ^ (prefixWord ++ tailWord_95228).sum := by decide
  have hdescent : baseEnd_95228 < baseStart_95228 := by decide
  rcases family_descends (prefixWord ++ tailWord_95228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95237 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 5, 3, 2]
def baseStart_95237 : Nat := 118140960795 + 95237 * 2 ^ 59
def prefixEnd_95237 : Nat := 4983230072969 + 3 ^ 40 * 95237 * 2
def baseEnd_95237 : Nat := 48902357092349118499519

theorem tailTrace_95237 : CollatzResearch.WordTrace tailWord_95237 prefixEnd_95237 48902357092349118499519 := by
  unfold tailWord_95237
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473578755980089029771965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2315719170653392686514643 3473578755980089029771965)
  ·
    refine ⟨1302592033492533386164487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3473578755980089029771965 1302592033492533386164487)
    ·
      refine ⟨1953888050238800079246731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302592033492533386164487 1953888050238800079246731)
      ·
        refine ⟨2930832075358200118870097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953888050238800079246731 2930832075358200118870097)
        ·
          refine ⟨2198124056518650089152573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2930832075358200118870097 2198124056518650089152573)
          ·
            refine ⟨824296521194493783432215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2198124056518650089152573 824296521194493783432215)
            ·
              refine ⟨1236444781791740675148323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824296521194493783432215 1236444781791740675148323)
              ·
                refine ⟨1854667172687611012722485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236444781791740675148323 1854667172687611012722485)
                ·
                  refine ⟨173875047439463532442733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1854667172687611012722485 173875047439463532442733)
                  ·
                    refine ⟨65203142789798824666025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 173875047439463532442733 65203142789798824666025)
                    ·
                      refine ⟨48902357092349118499519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65203142789798824666025 48902357092349118499519)
                      ·
                        rfl

theorem cell23_95237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_95237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95237 prefixEnd_95237 := by exact prefixLift 95237
  have htrace : WordTrace (prefixWord ++ tailWord_95237) baseStart_95237 baseEnd_95237 := by
    simpa [prefixWord, tailWord_95237, baseEnd_95237] using wordTrace_append hprefix tailTrace_95237
  have hstable : (prefixWord ++ tailWord_95237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95237).length < 2 ^ (prefixWord ++ tailWord_95237).sum := by decide
  have hdescent : baseEnd_95237 < baseStart_95237 := by decide
  rcases family_descends (prefixWord ++ tailWord_95237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95244 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_95244 : Nat := 118140960795 + 95244 * 2 ^ 59
def prefixEnd_95244 : Nat := 4983230072969 + 3 ^ 40 * 95244 * 2
def baseEnd_95244 : Nat := 48905951456930591111987

theorem tailTrace_95244 : CollatzResearch.WordTrace tailWord_95244 prefixEnd_95244 48905951456930591111987 := by
  unfold tailWord_95244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736917033477364612638393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2315889377969819483517857 1736917033477364612638393)
  ·
    refine ⟨1302687775108023459478795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1736917033477364612638393 1302687775108023459478795)
    ·
      refine ⟨1954031662662035189218193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302687775108023459478795 1954031662662035189218193)
      ·
        refine ⟨1465523746996526391913645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1954031662662035189218193 1465523746996526391913645)
        ·
          refine ⟨549571405123697396967617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1465523746996526391913645 549571405123697396967617)
          ·
            refine ⟨412178553842773047725713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549571405123697396967617 412178553842773047725713)
            ·
              refine ⟨309133915382079785794285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412178553842773047725713 309133915382079785794285)
              ·
                refine ⟨115925218268279919672857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309133915382079785794285 115925218268279919672857)
                ·
                  refine ⟨86943913701209939754643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115925218268279919672857 86943913701209939754643)
                  ·
                    refine ⟨130415870551814909631965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86943913701209939754643 130415870551814909631965)
                    ·
                      refine ⟨48905951456930591111987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 130415870551814909631965 48905951456930591111987)
                      ·
                        rfl

theorem cell23_95244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_95244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95244 prefixEnd_95244 := by exact prefixLift 95244
  have htrace : WordTrace (prefixWord ++ tailWord_95244) baseStart_95244 baseEnd_95244 := by
    simpa [prefixWord, tailWord_95244, baseEnd_95244] using wordTrace_append hprefix tailTrace_95244
  have hstable : (prefixWord ++ tailWord_95244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95244).length < 2 ^ (prefixWord ++ tailWord_95244).sum := by decide
  have hdescent : baseEnd_95244 < baseStart_95244 := by decide
  rcases family_descends (prefixWord ++ tailWord_95244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95280 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_95280 : Nat := 118140960795 + 95280 * 2 ^ 59
def prefixEnd_95280 : Nat := 4983230072969 + 3 ^ 40 * 95280 * 2
def baseEnd_95280 : Nat := 48924436760492450261821

theorem tailTrace_95280 : CollatzResearch.WordTrace tailWord_95280 prefixEnd_95280 48924436760492450261821 := by
  unfold tailWord_95280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737573547412153686793647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2316764729882871582391529 1737573547412153686793647)
  ·
    refine ⟨2606360321118230530190471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737573547412153686793647 2606360321118230530190471)
    ·
      refine ⟨3909540481677345795285707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606360321118230530190471 3909540481677345795285707)
      ·
        refine ⟨5864310722516018692928561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909540481677345795285707 5864310722516018692928561)
        ·
          refine ⟨4398233041887014019696421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5864310722516018692928561 4398233041887014019696421)
          ·
            refine ⟨824668695353815128693079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4398233041887014019696421 824668695353815128693079)
            ·
              refine ⟨1237003043030722693039619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824668695353815128693079 1237003043030722693039619)
              ·
                refine ⟨1855504564546084039559429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237003043030722693039619 1855504564546084039559429)
                ·
                  refine ⟨347907105852390757417393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855504564546084039559429 347907105852390757417393)
                  ·
                    refine ⟨260930329389293068063045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 347907105852390757417393 260930329389293068063045)
                    ·
                      refine ⟨48924436760492450261821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 260930329389293068063045 48924436760492450261821)
                      ·
                        rfl

theorem cell23_95280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_95280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95280 prefixEnd_95280 := by exact prefixLift 95280
  have htrace : WordTrace (prefixWord ++ tailWord_95280) baseStart_95280 baseEnd_95280 := by
    simpa [prefixWord, tailWord_95280, baseEnd_95280] using wordTrace_append hprefix tailTrace_95280
  have hstable : (prefixWord ++ tailWord_95280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95280).length < 2 ^ (prefixWord ++ tailWord_95280).sum := by decide
  have hdescent : baseEnd_95280 < baseStart_95280 := by decide
  rcases family_descends (prefixWord ++ tailWord_95280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95290 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_95290 : Nat := 118140960795 + 95290 * 2 ^ 59
def prefixEnd_95290 : Nat := 4983230072969 + 3 ^ 40 * 95290 * 2
def baseEnd_95290 : Nat := 5436619063004156792975

theorem tailTrace_95290 : CollatzResearch.WordTrace tailWord_95290 prefixEnd_95290 5436619063004156792975 := by
  unfold tailWord_95290
  simp only [CollatzResearch.WordTrace]
  refine ⟨868877956197019770362831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2317007883192052720967549 868877956197019770362831)
  ·
    refine ⟨1303316934295529655544247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 868877956197019770362831 1303316934295529655544247)
    ·
      refine ⟨1954975401443294483316371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303316934295529655544247 1954975401443294483316371)
      ·
        refine ⟨2932463102164941724974557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954975401443294483316371 2932463102164941724974557)
        ·
          refine ⟨1099673663311853146865459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2932463102164941724974557 1099673663311853146865459)
          ·
            refine ⟨1649510494967779720298189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099673663311853146865459 1649510494967779720298189)
            ·
              refine ⟨618566435612917395111821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1649510494967779720298189 618566435612917395111821)
              ·
                refine ⟨231962413354844023166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618566435612917395111821 231962413354844023166933)
                ·
                  refine ⟨5436619063004156792975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 231962413354844023166933 5436619063004156792975)
                  ·
                    rfl

theorem cell23_95290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_95290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95290 prefixEnd_95290 := by exact prefixLift 95290
  have htrace : WordTrace (prefixWord ++ tailWord_95290) baseStart_95290 baseEnd_95290 := by
    simpa [prefixWord, tailWord_95290, baseEnd_95290] using wordTrace_append hprefix tailTrace_95290
  have hstable : (prefixWord ++ tailWord_95290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95290).length < 2 ^ (prefixWord ++ tailWord_95290).sum := by decide
  have hdescent : baseEnd_95290 < baseStart_95290 := by decide
  rcases family_descends (prefixWord ++ tailWord_95290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95320 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_95320 : Nat := 118140960795 + 95320 * 2 ^ 59
def prefixEnd_95320 : Nat := 4983230072969 + 3 ^ 40 * 95320 * 2
def baseEnd_95320 : Nat := 16314991995557431253879

theorem tailTrace_95320 : CollatzResearch.WordTrace tailWord_95320 prefixEnd_95320 16314991995557431253879 := by
  unfold tailWord_95320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738303007339697102521707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2317737343119596136695609 1738303007339697102521707)
  ·
    refine ⟨2607454511009545653782561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1738303007339697102521707 2607454511009545653782561)
    ·
      refine ⟨1955590883257159240336921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2607454511009545653782561 1955590883257159240336921)
      ·
        refine ⟨1466693162442869430252691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1955590883257159240336921 1466693162442869430252691)
        ·
          refine ⟨2200039743664304145379037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466693162442869430252691 2200039743664304145379037)
          ·
            refine ⟨825014903874114054517139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2200039743664304145379037 825014903874114054517139)
            ·
              refine ⟨1237522355811171081775709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825014903874114054517139 1237522355811171081775709)
              ·
                refine ⟨464070883429189155665891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1237522355811171081775709 464070883429189155665891)
                ·
                  refine ⟨696106325143783733498837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464070883429189155665891 696106325143783733498837)
                  ·
                    refine ⟨16314991995557431253879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 696106325143783733498837 16314991995557431253879)
                    ·
                      rfl

theorem cell23_95320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_95320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95320 prefixEnd_95320 := by exact prefixLift 95320
  have htrace : WordTrace (prefixWord ++ tailWord_95320) baseStart_95320 baseEnd_95320 := by
    simpa [prefixWord, tailWord_95320, baseEnd_95320] using wordTrace_append hprefix tailTrace_95320
  have hstable : (prefixWord ++ tailWord_95320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95320).length < 2 ^ (prefixWord ++ tailWord_95320).sum := by decide
  have hdescent : baseEnd_95320 < baseStart_95320 := by decide
  rcases family_descends (prefixWord ++ tailWord_95320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95337 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_95337 : Nat := 118140960795 + 95337 * 2 ^ 59
def prefixEnd_95337 : Nat := 4983230072969 + 3 ^ 40 * 95337 * 2
def baseEnd_95337 : Nat := 16317901719266242416353

theorem tailTrace_95337 : CollatzResearch.WordTrace tailWord_95337 prefixEnd_95337 16317901719266242416353 := by
  unfold tailWord_95337
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477226055617806108412265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318150703745204072274843 3477226055617806108412265)
  ·
    refine ⟨2607919541713354581309199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3477226055617806108412265 2607919541713354581309199)
    ·
      refine ⟨3911879312570031871963799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607919541713354581309199 3911879312570031871963799)
      ·
        refine ⟨5867818968855047807945699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911879312570031871963799 5867818968855047807945699)
        ·
          refine ⟨8801728453282571711918549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867818968855047807945699 8801728453282571711918549)
          ·
            refine ⟨206290510623810274498091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8801728453282571711918549 206290510623810274498091)
            ·
              refine ⟨309435765935715411747137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206290510623810274498091 309435765935715411747137)
              ·
                refine ⟨232076824451786558810353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309435765935715411747137 232076824451786558810353)
                ·
                  refine ⟨174057618338839919107765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232076824451786558810353 174057618338839919107765)
                  ·
                    refine ⟨16317901719266242416353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174057618338839919107765 16317901719266242416353)
                    ·
                      rfl

theorem cell23_95337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_95337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95337 prefixEnd_95337 := by exact prefixLift 95337
  have htrace : WordTrace (prefixWord ++ tailWord_95337) baseStart_95337 baseEnd_95337 := by
    simpa [prefixWord, tailWord_95337, baseEnd_95337] using wordTrace_append hprefix tailTrace_95337
  have hstable : (prefixWord ++ tailWord_95337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95337).length < 2 ^ (prefixWord ++ tailWord_95337).sum := by decide
  have hdescent : baseEnd_95337 < baseStart_95337 := by decide
  rcases family_descends (prefixWord ++ tailWord_95337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95341 : List Nat := [1, 5, 1, 1, 2, 3, 3, 2, 5]
def baseStart_95341 : Nat := 118140960795 + 95341 * 2 ^ 59
def prefixEnd_95341 : Nat := 4983230072969 + 3 ^ 40 * 95341 * 2
def baseEnd_95341 : Nat := 5439528786712967955449

theorem tailTrace_95341 : CollatzResearch.WordTrace tailWord_95341 prefixEnd_95341 5439528786712967955449 := by
  unfold tailWord_95341
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477371947603314791557877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318247965068876527705251 3477371947603314791557877)
  ·
    refine ⟨326003620087810761708551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3477371947603314791557877 326003620087810761708551)
    ·
      refine ⟨489005430131716142562827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326003620087810761708551 489005430131716142562827)
      ·
        refine ⟨733508145197574213844241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489005430131716142562827 733508145197574213844241)
        ·
          refine ⟨550131108898180660383181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733508145197574213844241 550131108898180660383181)
          ·
            refine ⟨206299165836817747643693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 550131108898180660383181 206299165836817747643693)
            ·
              refine ⟨77362187188806655366385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206299165836817747643693 77362187188806655366385)
              ·
                refine ⟨58021640391604991524789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77362187188806655366385 58021640391604991524789)
                ·
                  refine ⟨5439528786712967955449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58021640391604991524789 5439528786712967955449)
                  ·
                    rfl

theorem cell23_95341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_95341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95341 prefixEnd_95341 := by exact prefixLift 95341
  have htrace : WordTrace (prefixWord ++ tailWord_95341) baseStart_95341 baseEnd_95341 := by
    simpa [prefixWord, tailWord_95341, baseEnd_95341] using wordTrace_append hprefix tailTrace_95341
  have hstable : (prefixWord ++ tailWord_95341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95341).length < 2 ^ (prefixWord ++ tailWord_95341).sum := by decide
  have hdescent : baseEnd_95341 < baseStart_95341 := by decide
  rcases family_descends (prefixWord ++ tailWord_95341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95357 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_95357 : Nat := 118140960795 + 95357 * 2 ^ 59
def prefixEnd_95357 : Nat := 4983230072969 + 3 ^ 40 * 95357 * 2
def baseEnd_95357 : Nat := 48963974770888648998967

theorem tailTrace_95357 : CollatzResearch.WordTrace tailWord_95357 prefixEnd_95357 48963974770888648998967 := by
  unfold tailWord_95357
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477955515545349524140325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318637010363566349426883 3477955515545349524140325)
  ·
    refine ⟨652116659164753035776311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3477955515545349524140325 652116659164753035776311)
    ·
      refine ⟨978174988747129553664467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652116659164753035776311 978174988747129553664467)
      ·
        refine ⟨1467262483120694330496701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978174988747129553664467 1467262483120694330496701)
        ·
          refine ⟨550223431170260373936263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1467262483120694330496701 550223431170260373936263)
          ·
            refine ⟨825335146755390560904395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550223431170260373936263 825335146755390560904395)
            ·
              refine ⟨1238002720133085841356593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825335146755390560904395 1238002720133085841356593)
              ·
                refine ⟨928502040099814381017445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238002720133085841356593 928502040099814381017445)
                ·
                  refine ⟨174094132518715196440771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 928502040099814381017445 174094132518715196440771)
                  ·
                    refine ⟨261141198778072794661157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174094132518715196440771 261141198778072794661157)
                    ·
                      refine ⟨48963974770888648998967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 261141198778072794661157 48963974770888648998967)
                      ·
                        rfl

theorem cell23_95357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_95357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95357 prefixEnd_95357 := by exact prefixLift 95357
  have htrace : WordTrace (prefixWord ++ tailWord_95357) baseStart_95357 baseEnd_95357 := by
    simpa [prefixWord, tailWord_95357, baseEnd_95357] using wordTrace_append hprefix tailTrace_95357
  have hstable : (prefixWord ++ tailWord_95357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95357).length < 2 ^ (prefixWord ++ tailWord_95357).sum := by decide
  have hdescent : baseEnd_95357 < baseStart_95357 := by decide
  rcases family_descends (prefixWord ++ tailWord_95357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95367 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 5, 4]
def baseStart_95367 : Nat := 118140960795 + 95367 * 2 ^ 59
def prefixEnd_95367 : Nat := 4983230072969 + 3 ^ 40 * 95367 * 2
def baseEnd_95367 : Nat := 16323036525811203291307

theorem tailTrace_95367 : CollatzResearch.WordTrace tailWord_95367 prefixEnd_95367 16323036525811203291307 := by
  unfold tailWord_95367
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478320245509121232004355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2318880163672747488002903 3478320245509121232004355)
  ·
    refine ⟨5217480368263681848006533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3478320245509121232004355 5217480368263681848006533)
    ·
      refine ⟨978277569049440346501225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5217480368263681848006533 978277569049440346501225)
      ·
        refine ⟨733708176787080259875919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978277569049440346501225 733708176787080259875919)
        ·
          refine ⟨1100562265180620389813879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733708176787080259875919 1100562265180620389813879)
          ·
            refine ⟨1650843397770930584720819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100562265180620389813879 1650843397770930584720819)
            ·
              refine ⟨2476265096656395877081229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650843397770930584720819 2476265096656395877081229)
              ·
                refine ⟨928599411246148453905461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2476265096656395877081229 928599411246148453905461)
                ·
                  refine ⟨87056194804326417553637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 928599411246148453905461 87056194804326417553637)
                  ·
                    refine ⟨16323036525811203291307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87056194804326417553637 16323036525811203291307)
                    ·
                      rfl

theorem cell23_95367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_95367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95367 prefixEnd_95367 := by exact prefixLift 95367
  have htrace : WordTrace (prefixWord ++ tailWord_95367) baseStart_95367 baseEnd_95367 := by
    simpa [prefixWord, tailWord_95367, baseEnd_95367] using wordTrace_append hprefix tailTrace_95367
  have hstable : (prefixWord ++ tailWord_95367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95367).length < 2 ^ (prefixWord ++ tailWord_95367).sum := by decide
  have hdescent : baseEnd_95367 < baseStart_95367 := by decide
  rcases family_descends (prefixWord ++ tailWord_95367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95374 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_95374 : Nat := 118140960795 + 95374 * 2 ^ 59
def prefixEnd_95374 : Nat := 4983230072969 + 3 ^ 40 * 95374 * 2
def baseEnd_95374 : Nat := 48972703942015082486389

theorem tailTrace_95374 : CollatzResearch.WordTrace tailWord_95374 prefixEnd_95374 48972703942015082486389 := by
  unfold tailWord_95374
  simp only [CollatzResearch.WordTrace]
  refine ⟨434821944560470178438647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2319050370989174285006117 434821944560470178438647)
  ·
    refine ⟨652232916840705267657971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 434821944560470178438647 652232916840705267657971)
    ·
      refine ⟨978349375261057901486957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652232916840705267657971 978349375261057901486957)
      ·
        refine ⟨366881015722896713057609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 978349375261057901486957 366881015722896713057609)
        ·
          refine ⟨275160761792172534793207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366881015722896713057609 275160761792172534793207)
          ·
            refine ⟨412741142688258802189811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275160761792172534793207 412741142688258802189811)
            ·
              refine ⟨619111714032388203284717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412741142688258802189811 619111714032388203284717)
              ·
                refine ⟨232166892762145576231769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619111714032388203284717 232166892762145576231769)
                ·
                  refine ⟨174125169571609182173827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232166892762145576231769 174125169571609182173827)
                  ·
                    refine ⟨261187754357413773260741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174125169571609182173827 261187754357413773260741)
                    ·
                      refine ⟨48972703942015082486389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 261187754357413773260741 48972703942015082486389)
                      ·
                        rfl

theorem cell23_95374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_95374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95374 prefixEnd_95374 := by exact prefixLift 95374
  have htrace : WordTrace (prefixWord ++ tailWord_95374) baseStart_95374 baseEnd_95374 := by
    simpa [prefixWord, tailWord_95374, baseEnd_95374] using wordTrace_append hprefix tailTrace_95374
  have hstable : (prefixWord ++ tailWord_95374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95374).length < 2 ^ (prefixWord ++ tailWord_95374).sum := by decide
  have hdescent : baseEnd_95374 < baseStart_95374 := by decide
  rcases family_descends (prefixWord ++ tailWord_95374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95397 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 6]
def baseStart_95397 : Nat := 118140960795 + 95397 * 2 ^ 59
def prefixEnd_95397 : Nat := 4983230072969 + 3 ^ 40 * 95397 * 2
def baseEnd_95397 : Nat := 5442723777452054722087

theorem tailTrace_95397 : CollatzResearch.WordTrace tailWord_95397 prefixEnd_95397 5442723777452054722087 := by
  unfold tailWord_95397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479414435400436355596445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2319609623600290903730963 3479414435400436355596445)
  ·
    refine ⟨1304780413275163633348667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3479414435400436355596445 1304780413275163633348667)
    ·
      refine ⟨1957170619912745450023001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304780413275163633348667 1957170619912745450023001)
      ·
        refine ⟨1467877964934559087517251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1957170619912745450023001 1467877964934559087517251)
        ·
          refine ⟨2201816947401838631275877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467877964934559087517251 2201816947401838631275877)
          ·
            refine ⟨412840677637844743364227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2201816947401838631275877 412840677637844743364227)
            ·
              refine ⟨619261016456767115046341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412840677637844743364227 619261016456767115046341)
              ·
                refine ⟨116111440585643834071189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619261016456767115046341 116111440585643834071189)
                ·
                  refine ⟨5442723777452054722087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116111440585643834071189 5442723777452054722087)
                  ·
                    rfl

theorem cell23_95397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_95397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95397 prefixEnd_95397 := by exact prefixLift 95397
  have htrace : WordTrace (prefixWord ++ tailWord_95397) baseStart_95397 baseEnd_95397 := by
    simpa [prefixWord, tailWord_95397, baseEnd_95397] using wordTrace_append hprefix tailTrace_95397
  have hstable : (prefixWord ++ tailWord_95397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95397).length < 2 ^ (prefixWord ++ tailWord_95397).sum := by decide
  have hdescent : baseEnd_95397 < baseStart_95397 := by decide
  rcases family_descends (prefixWord ++ tailWord_95397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95428 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_95428 : Nat := 118140960795 + 95428 * 2 ^ 59
def prefixEnd_95428 : Nat := 4983230072969 + 3 ^ 40 * 95428 * 2
def baseEnd_95428 : Nat := 49000431897357871211141

theorem tailTrace_95428 : CollatzResearch.WordTrace tailWord_95428 prefixEnd_95428 49000431897357871211141 := by
  unfold tailWord_95428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740272549144064324987469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2320363398858752433316625 1740272549144064324987469)
  ·
    refine ⟨652602205929024121870301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1740272549144064324987469 652602205929024121870301)
    ·
      refine ⟨244725827223384045701363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 652602205929024121870301 244725827223384045701363)
      ·
        refine ⟨367088740835076068552045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244725827223384045701363 367088740835076068552045)
        ·
          refine ⟨137658277813153525707017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367088740835076068552045 137658277813153525707017)
          ·
            refine ⟨103243708359865144280263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137658277813153525707017 103243708359865144280263)
            ·
              refine ⟨154865562539797716420395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103243708359865144280263 154865562539797716420395)
              ·
                refine ⟨232298343809696574630593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154865562539797716420395 232298343809696574630593)
                ·
                  refine ⟨174223757857272430972945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232298343809696574630593 174223757857272430972945)
                  ·
                    refine ⟨130667818392954323229709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174223757857272430972945 130667818392954323229709)
                    ·
                      refine ⟨49000431897357871211141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 130667818392954323229709 49000431897357871211141)
                      ·
                        rfl

theorem cell23_95428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_95428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95428 prefixEnd_95428 := by exact prefixLift 95428
  have htrace : WordTrace (prefixWord ++ tailWord_95428) baseStart_95428 baseEnd_95428 := by
    simpa [prefixWord, tailWord_95428, baseEnd_95428] using wordTrace_append hprefix tailTrace_95428
  have hstable : (prefixWord ++ tailWord_95428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95428).length < 2 ^ (prefixWord ++ tailWord_95428).sum := by decide
  have hdescent : baseEnd_95428 < baseStart_95428 := by decide
  rcases family_descends (prefixWord ++ tailWord_95428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95467 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5]
def baseStart_95467 : Nat := 118140960795 + 95467 * 2 ^ 59
def prefixEnd_95467 : Nat := 4983230072969 + 3 ^ 40 * 95467 * 2
def baseEnd_95467 : Nat := 49020457642883218623461

theorem tailTrace_95467 : CollatzResearch.WordTrace tailWord_95467 prefixEnd_95467 49020457642883218623461 := by
  unfold tailWord_95467
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481967545146838310644655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2321311696764558873763103 3481967545146838310644655)
  ·
    refine ⟨5222951317720257465966983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481967545146838310644655 5222951317720257465966983)
    ·
      refine ⟨7834426976580386198950475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222951317720257465966983 7834426976580386198950475)
      ·
        refine ⟨11751640464870579298425713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7834426976580386198950475 11751640464870579298425713)
        ·
          refine ⟨8813730348652934473819285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11751640464870579298425713 8813730348652934473819285)
          ·
            refine ⟨413143610093106303460279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8813730348652934473819285 413143610093106303460279)
            ·
              refine ⟨619715415139659455190419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413143610093106303460279 619715415139659455190419)
              ·
                refine ⟨929573122709489182785629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619715415139659455190419 929573122709489182785629)
                ·
                  refine ⟨348589921016058443544611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929573122709489182785629 348589921016058443544611)
                  ·
                    refine ⟨522884881524087665316917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348589921016058443544611 522884881524087665316917)
                    ·
                      refine ⟨49020457642883218623461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 522884881524087665316917 49020457642883218623461)
                      ·
                        rfl

theorem cell23_95467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_95467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95467 prefixEnd_95467 := by exact prefixLift 95467
  have htrace : WordTrace (prefixWord ++ tailWord_95467) baseStart_95467 baseEnd_95467 := by
    simpa [prefixWord, tailWord_95467, baseEnd_95467] using wordTrace_append hprefix tailTrace_95467
  have hstable : (prefixWord ++ tailWord_95467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95467).length < 2 ^ (prefixWord ++ tailWord_95467).sum := by decide
  have hdescent : baseEnd_95467 < baseStart_95467 := by decide
  rcases family_descends (prefixWord ++ tailWord_95467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95481 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 3, 2, 2]
def baseStart_95481 : Nat := 118140960795 + 95481 * 2 ^ 59
def prefixEnd_95481 : Nat := 4983230072969 + 3 ^ 40 * 95481 * 2
def baseEnd_95481 : Nat := 49027646372046163848397

theorem tailTrace_95481 : CollatzResearch.WordTrace tailWord_95481 prefixEnd_95481 49027646372046163848397 := by
  unfold tailWord_95481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482478167096118701654297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2321652111397412467769531 3482478167096118701654297)
  ·
    refine ⟨2611858625322089026240723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3482478167096118701654297 2611858625322089026240723)
    ·
      refine ⟨3917787937983133539361085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611858625322089026240723 3917787937983133539361085)
      ·
        refine ⟨1469170476743675077260407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3917787937983133539361085 1469170476743675077260407)
        ·
          refine ⟨2203755715115512615890611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469170476743675077260407 2203755715115512615890611)
          ·
            refine ⟨3305633572673268923835917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203755715115512615890611 3305633572673268923835917)
            ·
              refine ⟨1239612589752475846438469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3305633572673268923835917 1239612589752475846438469)
              ·
                refine ⟨232427360578589221207213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1239612589752475846438469 232427360578589221207213)
                ·
                  refine ⟨87160260216970957952705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232427360578589221207213 87160260216970957952705)
                  ·
                    refine ⟨65370195162728218464529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87160260216970957952705 65370195162728218464529)
                    ·
                      refine ⟨49027646372046163848397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65370195162728218464529 49027646372046163848397)
                      ·
                        rfl

theorem cell23_95481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_95481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95481 prefixEnd_95481 := by exact prefixLift 95481
  have htrace : WordTrace (prefixWord ++ tailWord_95481) baseStart_95481 baseEnd_95481 := by
    simpa [prefixWord, tailWord_95481, baseEnd_95481] using wordTrace_append hprefix tailTrace_95481
  have hstable : (prefixWord ++ tailWord_95481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95481).length < 2 ^ (prefixWord ++ tailWord_95481).sum := by decide
  have hdescent : baseEnd_95481 < baseStart_95481 := by decide
  rcases family_descends (prefixWord ++ tailWord_95481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95487 : List Nat := [1, 1, 2, 2, 1, 6, 1, 9]
def baseStart_95487 : Nat := 118140960795 + 95487 * 2 ^ 59
def prefixEnd_95487 : Nat := 4983230072969 + 3 ^ 40 * 95487 * 2
def baseEnd_95487 : Nat := 1815952861332338532347

theorem tailTrace_95487 : CollatzResearch.WordTrace tailWord_95487 prefixEnd_95487 1815952861332338532347 := by
  unfold tailWord_95487
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482697005074381726372715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2321798003382921150915143 3482697005074381726372715)
  ·
    refine ⟨5224045507611572589559073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3482697005074381726372715 5224045507611572589559073)
    ·
      refine ⟨3918034130708679442169305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5224045507611572589559073 3918034130708679442169305)
      ·
        refine ⟨2938525598031509581626979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3918034130708679442169305 2938525598031509581626979)
        ·
          refine ⟨4407788397047264372440469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938525598031509581626979 4407788397047264372440469)
          ·
            refine ⟨206615081111590517458147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4407788397047264372440469 206615081111590517458147)
            ·
              refine ⟨309922621667385776187221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206615081111590517458147 309922621667385776187221)
              ·
                refine ⟨1815952861332338532347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 309922621667385776187221 1815952861332338532347)
                ·
                  rfl

theorem cell23_95487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 9].length) (baseStart_95487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95487 prefixEnd_95487 := by exact prefixLift 95487
  have htrace : WordTrace (prefixWord ++ tailWord_95487) baseStart_95487 baseEnd_95487 := by
    simpa [prefixWord, tailWord_95487, baseEnd_95487] using wordTrace_append hprefix tailTrace_95487
  have hstable : (prefixWord ++ tailWord_95487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95487).length < 2 ^ (prefixWord ++ tailWord_95487).sum := by decide
  have hdescent : baseEnd_95487 < baseStart_95487 := by decide
  rcases family_descends (prefixWord ++ tailWord_95487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95584 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_95584 : Nat := 118140960795 + 95584 * 2 ^ 59
def prefixEnd_95584 : Nat := 4983230072969 + 3 ^ 40 * 95584 * 2
def baseEnd_95584 : Nat := 49080534879459260860423

theorem tailTrace_95584 : CollatzResearch.WordTrace tailWord_95584 prefixEnd_95584 49080534879459260860423 := by
  unfold tailWord_95584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743117442861483646326903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2324156590481978195102537 1743117442861483646326903)
  ·
    refine ⟨2614676164292225469490355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743117442861483646326903 2614676164292225469490355)
    ·
      refine ⟨3922014246438338204235533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614676164292225469490355 3922014246438338204235533)
      ·
        refine ⟨1470755342414376826588325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3922014246438338204235533 1470755342414376826588325)
        ·
          refine ⟨275766626702695654985311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1470755342414376826588325 275766626702695654985311)
          ·
            refine ⟨413649940054043482477967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275766626702695654985311 413649940054043482477967)
            ·
              refine ⟨620474910081065223716951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413649940054043482477967 620474910081065223716951)
              ·
                refine ⟨930712365121597835575427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620474910081065223716951 930712365121597835575427)
                ·
                  refine ⟨1396068547682396753363141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930712365121597835575427 1396068547682396753363141)
                  ·
                    refine ⟨261762852690449391255589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1396068547682396753363141 261762852690449391255589)
                    ·
                      refine ⟨49080534879459260860423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 261762852690449391255589 49080534879459260860423)
                      ·
                        rfl

theorem cell23_95584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_95584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95584 prefixEnd_95584 := by exact prefixLift 95584
  have htrace : WordTrace (prefixWord ++ tailWord_95584) baseStart_95584 baseEnd_95584 := by
    simpa [prefixWord, tailWord_95584, baseEnd_95584] using wordTrace_append hprefix tailTrace_95584
  have hstable : (prefixWord ++ tailWord_95584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95584).length < 2 ^ (prefixWord ++ tailWord_95584).sum := by decide
  have hdescent : baseEnd_95584 < baseStart_95584 := by decide
  rcases family_descends (prefixWord ++ tailWord_95584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95588 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_95588 : Nat := 118140960795 + 95588 * 2 ^ 59
def prefixEnd_95588 : Nat := 4983230072969 + 3 ^ 40 * 95588 * 2
def baseEnd_95588 : Nat := 49082588802077245210405

theorem tailTrace_95588 : CollatzResearch.WordTrace tailWord_95588 prefixEnd_95588 49082588802077245210405 := by
  unfold tailWord_95588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743190388854237987899709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2324253851805650650532945 1743190388854237987899709)
  ·
    refine ⟨653696395820339245462391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1743190388854237987899709 653696395820339245462391)
    ·
      refine ⟨980544593730508868193587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653696395820339245462391 980544593730508868193587)
      ·
        refine ⟨1470816890595763302290381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980544593730508868193587 1470816890595763302290381)
        ·
          refine ⟨551556333973411238358893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1470816890595763302290381 551556333973411238358893)
          ·
            refine ⟨206833625240029214384585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 551556333973411238358893 206833625240029214384585)
            ·
              refine ⟨155125218930021910788439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206833625240029214384585 155125218930021910788439)
              ·
                refine ⟨232687828395032866182659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155125218930021910788439 232687828395032866182659)
                ·
                  refine ⟨349031742592549299273989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232687828395032866182659 349031742592549299273989)
                  ·
                    refine ⟨65443451736102993613873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349031742592549299273989 65443451736102993613873)
                    ·
                      refine ⟨49082588802077245210405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65443451736102993613873 49082588802077245210405)
                      ·
                        rfl

theorem cell23_95588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_95588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95588 prefixEnd_95588 := by exact prefixLift 95588
  have htrace : WordTrace (prefixWord ++ tailWord_95588) baseStart_95588 baseEnd_95588 := by
    simpa [prefixWord, tailWord_95588, baseEnd_95588] using wordTrace_append hprefix tailTrace_95588
  have hstable : (prefixWord ++ tailWord_95588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95588).length < 2 ^ (prefixWord ++ tailWord_95588).sum := by decide
  have hdescent : baseEnd_95588 < baseStart_95588 := by decide
  rcases family_descends (prefixWord ++ tailWord_95588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95611 : List Nat := [1, 1, 1, 1, 1, 6, 4, 3, 5]
def baseStart_95611 : Nat := 118140960795 + 95611 * 2 ^ 59
def prefixEnd_95611 : Nat := 4983230072969 + 3 ^ 40 * 95611 * 2
def baseEnd_95611 : Nat := 5454933206347850580311

theorem tailTrace_95611 : CollatzResearch.WordTrace tailWord_95611 prefixEnd_95611 5454933206347850580311 := by
  unfold tailWord_95611
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487219656625150903886687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2324813104416767269257791 3487219656625150903886687)
  ·
    refine ⟨5230829484937726355830031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487219656625150903886687 5230829484937726355830031)
    ·
      refine ⟨7846244227406589533745047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230829484937726355830031 7846244227406589533745047)
      ·
        refine ⟨11769366341109884300617571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7846244227406589533745047 11769366341109884300617571)
        ·
          refine ⟨17654049511664826450926357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769366341109884300617571 17654049511664826450926357)
          ·
            refine ⟨827533570859288739887173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17654049511664826450926357 827533570859288739887173)
            ·
              refine ⟨155162544536116638728845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 827533570859288739887173 155162544536116638728845)
              ·
                refine ⟨58185954201043739523317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155162544536116638728845 58185954201043739523317)
                ·
                  refine ⟨5454933206347850580311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58185954201043739523317 5454933206347850580311)
                  ·
                    rfl

theorem cell23_95611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 5].length) (baseStart_95611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95611 prefixEnd_95611 := by exact prefixLift 95611
  have htrace : WordTrace (prefixWord ++ tailWord_95611) baseStart_95611 baseEnd_95611 := by
    simpa [prefixWord, tailWord_95611, baseEnd_95611] using wordTrace_append hprefix tailTrace_95611
  have hstable : (prefixWord ++ tailWord_95611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95611).length < 2 ^ (prefixWord ++ tailWord_95611).sum := by decide
  have hdescent : baseEnd_95611 < baseStart_95611 := by decide
  rcases family_descends (prefixWord ++ tailWord_95611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95618 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_95618 : Nat := 118140960795 + 95618 * 2 ^ 59
def prefixEnd_95618 : Nat := 4983230072969 + 3 ^ 40 * 95618 * 2
def baseEnd_95618 : Nat := 49097993221712127835267

theorem tailTrace_95618 : CollatzResearch.WordTrace tailWord_95618 prefixEnd_95618 49097993221712127835267 := by
  unfold tailWord_95618
  simp only [CollatzResearch.WordTrace]
  refine ⟨871868741899947774847877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2324983311733194066261005 871868741899947774847877)
  ·
    refine ⟨163475389106240207783977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 871868741899947774847877 163475389106240207783977)
    ·
      refine ⟨122606541829680155837983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163475389106240207783977 122606541829680155837983)
      ·
        refine ⟨183909812744520233756975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122606541829680155837983 183909812744520233756975)
        ·
          refine ⟨275864719116780350635463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183909812744520233756975 275864719116780350635463)
          ·
            refine ⟨413797078675170525953195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275864719116780350635463 413797078675170525953195)
            ·
              refine ⟨620695618012755788929793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413797078675170525953195 620695618012755788929793)
              ·
                refine ⟨465521713509566841697345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620695618012755788929793 465521713509566841697345)
                ·
                  refine ⟨349141285132175131273009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465521713509566841697345 349141285132175131273009)
                  ·
                    refine ⟨261855963849131348454757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349141285132175131273009 261855963849131348454757)
                    ·
                      refine ⟨49097993221712127835267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 261855963849131348454757 49097993221712127835267)
                      ·
                        rfl

theorem cell23_95618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_95618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95618 prefixEnd_95618 := by exact prefixLift 95618
  have htrace : WordTrace (prefixWord ++ tailWord_95618) baseStart_95618 baseEnd_95618 := by
    simpa [prefixWord, tailWord_95618, baseEnd_95618] using wordTrace_append hprefix tailTrace_95618
  have hstable : (prefixWord ++ tailWord_95618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95618).length < 2 ^ (prefixWord ++ tailWord_95618).sum := by decide
  have hdescent : baseEnd_95618 < baseStart_95618 := by decide
  rcases family_descends (prefixWord ++ tailWord_95618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95701 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 6]
def baseStart_95701 : Nat := 118140960795 + 95701 * 2 ^ 59
def prefixEnd_95701 : Nat := 4983230072969 + 3 ^ 40 * 95701 * 2
def baseEnd_95701 : Nat := 5460068012892811455265

theorem tailTrace_95701 : CollatzResearch.WordTrace tailWord_95701 prefixEnd_95701 5460068012892811455265 := by
  unfold tailWord_95701
  simp only [CollatzResearch.WordTrace]
  refine ⟨3490502226299096274662957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2327001484199397516441971 3490502226299096274662957)
  ·
    refine ⟨1308938334862161102998609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3490502226299096274662957 1308938334862161102998609)
    ·
      refine ⟨981703751146620827248957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308938334862161102998609 981703751146620827248957)
      ·
        refine ⟨368138906679982810218359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 981703751146620827248957 368138906679982810218359)
        ·
          refine ⟨552208360019974215327539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368138906679982810218359 552208360019974215327539)
          ·
            refine ⟨828312540029961322991309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552208360019974215327539 828312540029961322991309)
            ·
              refine ⟨310617202511235496121741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828312540029961322991309 310617202511235496121741)
              ·
                refine ⟨116481450941713311045653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310617202511235496121741 116481450941713311045653)
                ·
                  refine ⟨5460068012892811455265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116481450941713311045653 5460068012892811455265)
                  ·
                    rfl

theorem cell23_95701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_95701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95701 prefixEnd_95701 := by exact prefixLift 95701
  have htrace : WordTrace (prefixWord ++ tailWord_95701) baseStart_95701 baseEnd_95701 := by
    simpa [prefixWord, tailWord_95701, baseEnd_95701] using wordTrace_append hprefix tailTrace_95701
  have hstable : (prefixWord ++ tailWord_95701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95701).length < 2 ^ (prefixWord ++ tailWord_95701).sum := by decide
  have hdescent : baseEnd_95701 < baseStart_95701 := by decide
  rcases family_descends (prefixWord ++ tailWord_95701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95704 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_95704 : Nat := 118140960795 + 95704 * 2 ^ 59
def prefixEnd_95704 : Nat := 4983230072969 + 3 ^ 40 * 95704 * 2
def baseEnd_95704 : Nat := 49142152557998791359871

theorem tailTrace_95704 : CollatzResearch.WordTrace tailWord_95704 prefixEnd_95704 49142152557998791359871 := by
  unfold tailWord_95704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745305822644113893511083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2327074430192151858014777 1745305822644113893511083)
  ·
    refine ⟨2617958733966170840266625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745305822644113893511083 2617958733966170840266625)
    ·
      refine ⟨1963469050474628130199969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2617958733966170840266625 1963469050474628130199969)
      ·
        refine ⟨1472601787855971097649977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1963469050474628130199969 1472601787855971097649977)
        ·
          refine ⟨1104451340891978323237483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472601787855971097649977 1104451340891978323237483)
          ·
            refine ⟨1656677011337967484856225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104451340891978323237483 1656677011337967484856225)
            ·
              refine ⟨1242507758503475613642169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656677011337967484856225 1242507758503475613642169)
              ·
                refine ⟨931880818877606710231627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242507758503475613642169 931880818877606710231627)
                ·
                  refine ⟨1397821228316410065347441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931880818877606710231627 1397821228316410065347441)
                  ·
                    refine ⟨1048365921237307549010581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1397821228316410065347441 1048365921237307549010581)
                    ·
                      refine ⟨49142152557998791359871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1048365921237307549010581 49142152557998791359871)
                      ·
                        rfl

theorem cell23_95704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_95704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95704 prefixEnd_95704 := by exact prefixLift 95704
  have htrace : WordTrace (prefixWord ++ tailWord_95704) baseStart_95704 baseEnd_95704 := by
    simpa [prefixWord, tailWord_95704, baseEnd_95704] using wordTrace_append hprefix tailTrace_95704
  have hstable : (prefixWord ++ tailWord_95704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95704).length < 2 ^ (prefixWord ++ tailWord_95704).sum := by decide
  have hdescent : baseEnd_95704 < baseStart_95704 := by decide
  rcases family_descends (prefixWord ++ tailWord_95704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95721 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 5, 5, 2]
def baseStart_95721 : Nat := 118140960795 + 95721 * 2 ^ 59
def prefixEnd_95721 : Nat := 4983230072969 + 3 ^ 40 * 95721 * 2
def baseEnd_95721 : Nat := 49150881729125224847293

theorem tailTrace_95721 : CollatzResearch.WordTrace tailWord_95721 prefixEnd_95721 49150881729125224847293 := by
  unfold tailWord_95721
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491231686226639690391017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2327487790817759793594011 3491231686226639690391017)
  ·
    refine ⟨2618423764669979767793263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3491231686226639690391017 2618423764669979767793263)
    ·
      refine ⟨3927635647004969651689895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2618423764669979767793263 3927635647004969651689895)
      ·
        refine ⟨5891453470507454477534843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3927635647004969651689895 5891453470507454477534843)
        ·
          refine ⟨8837180205761181716302265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891453470507454477534843 8837180205761181716302265)
          ·
            refine ⟨6627885154320886287226699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8837180205761181716302265 6627885154320886287226699)
            ·
              refine ⟨9941827731481329430840049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627885154320886287226699 9941827731481329430840049)
              ·
                refine ⟨7456370798610997073130037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9941827731481329430840049 7456370798610997073130037)
                ·
                  refine ⟨699034762369780975605941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7456370798610997073130037 699034762369780975605941)
                  ·
                    refine ⟨65534508972166966463057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 699034762369780975605941 65534508972166966463057)
                    ·
                      refine ⟨49150881729125224847293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65534508972166966463057 49150881729125224847293)
                      ·
                        rfl

theorem cell23_95721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 5, 2].length) (baseStart_95721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95721 prefixEnd_95721 := by exact prefixLift 95721
  have htrace : WordTrace (prefixWord ++ tailWord_95721) baseStart_95721 baseEnd_95721 := by
    simpa [prefixWord, tailWord_95721, baseEnd_95721] using wordTrace_append hprefix tailTrace_95721
  have hstable : (prefixWord ++ tailWord_95721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95721).length < 2 ^ (prefixWord ++ tailWord_95721).sum := by decide
  have hdescent : baseEnd_95721 < baseStart_95721 := by decide
  rcases family_descends (prefixWord ++ tailWord_95721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95724 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_95724 : Nat := 118140960795 + 95724 * 2 ^ 59
def prefixEnd_95724 : Nat := 4983230072969 + 3 ^ 40 * 95724 * 2
def baseEnd_95724 : Nat := 49152422171088713109779

theorem tailTrace_95724 : CollatzResearch.WordTrace tailWord_95724 prefixEnd_95724 49152422171088713109779 := by
  unfold tailWord_95724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745670552607885601375113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2327560736810514135166817 1745670552607885601375113)
  ·
    refine ⟨1309252914455914201031335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1745670552607885601375113 1309252914455914201031335)
    ·
      refine ⟨1963879371683871301547003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309252914455914201031335 1963879371683871301547003)
      ·
        refine ⟨2945819057525806952320505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963879371683871301547003 2945819057525806952320505)
        ·
          refine ⟨2209364293144355214240379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945819057525806952320505 2209364293144355214240379)
          ·
            refine ⟨3314046439716532821360569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209364293144355214240379 3314046439716532821360569)
            ·
              refine ⟨2485534829787399616020427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314046439716532821360569 2485534829787399616020427)
              ·
                refine ⟨3728302244681099424030641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485534829787399616020427 3728302244681099424030641)
                ·
                  refine ⟨2796226683510824568022981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728302244681099424030641 2796226683510824568022981)
                  ·
                    refine ⟨524292503158279606504309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796226683510824568022981 524292503158279606504309)
                    ·
                      refine ⟨49152422171088713109779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 524292503158279606504309 49152422171088713109779)
                      ·
                        rfl

theorem cell23_95724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_95724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95724 prefixEnd_95724 := by exact prefixLift 95724
  have htrace : WordTrace (prefixWord ++ tailWord_95724) baseStart_95724 baseEnd_95724 := by
    simpa [prefixWord, tailWord_95724, baseEnd_95724] using wordTrace_append hprefix tailTrace_95724
  have hstable : (prefixWord ++ tailWord_95724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95724).length < 2 ^ (prefixWord ++ tailWord_95724).sum := by decide
  have hdescent : baseEnd_95724 < baseStart_95724 := by decide
  rcases family_descends (prefixWord ++ tailWord_95724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95738 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2]
def baseStart_95738 : Nat := 118140960795 + 95738 * 2 ^ 59
def prefixEnd_95738 : Nat := 4983230072969 + 3 ^ 40 * 95738 * 2
def baseEnd_95738 : Nat := 49159610900251658334715

theorem tailTrace_95738 : CollatzResearch.WordTrace tailWord_95738 prefixEnd_95738 49159610900251658334715 := by
  unfold tailWord_95738
  simp only [CollatzResearch.WordTrace]
  refine ⟨872962931791262898439967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2327901151443367729173245 872962931791262898439967)
  ·
    refine ⟨1309444397686894347659951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872962931791262898439967 1309444397686894347659951)
    ·
      refine ⟨1964166596530341521489927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309444397686894347659951 1964166596530341521489927)
      ·
        refine ⟨2946249894795512282234891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964166596530341521489927 2946249894795512282234891)
        ·
          refine ⟨4419374842193268423352337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946249894795512282234891 4419374842193268423352337)
          ·
            refine ⟨3314531131644951317514253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4419374842193268423352337 3314531131644951317514253)
            ·
              refine ⟨1242949174366856744067845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3314531131644951317514253 1242949174366856744067845)
              ·
                refine ⟨233052970193785639512721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1242949174366856744067845 233052970193785639512721)
                ·
                  refine ⟨174789727645339229634541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233052970193785639512721 174789727645339229634541)
                  ·
                    refine ⟨65546147867002211112953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174789727645339229634541 65546147867002211112953)
                    ·
                      refine ⟨49159610900251658334715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65546147867002211112953 49159610900251658334715)
                      ·
                        rfl

theorem cell23_95738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_95738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95738 prefixEnd_95738 := by exact prefixLift 95738
  have htrace : WordTrace (prefixWord ++ tailWord_95738) baseStart_95738 baseEnd_95738 := by
    simpa [prefixWord, tailWord_95738, baseEnd_95738] using wordTrace_append hprefix tailTrace_95738
  have hstable : (prefixWord ++ tailWord_95738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95738).length < 2 ^ (prefixWord ++ tailWord_95738).sum := by decide
  have hdescent : baseEnd_95738 < baseStart_95738 := by decide
  rcases family_descends (prefixWord ++ tailWord_95738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95761 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 1, 6]
def baseStart_95761 : Nat := 118140960795 + 95761 * 2 ^ 59
def prefixEnd_95761 : Nat := 4983230072969 + 3 ^ 40 * 95761 * 2
def baseEnd_95761 : Nat := 16390473651768356115703

theorem tailTrace_95761 : CollatzResearch.WordTrace tailWord_95761 prefixEnd_95761 16390473651768356115703 := by
  unfold tailWord_95761
  simp only [CollatzResearch.WordTrace]
  refine ⟨3492690606081726521847137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2328460404054484347898091 3492690606081726521847137)
  ·
    refine ⟨2619517954561294891385353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3492690606081726521847137 2619517954561294891385353)
    ·
      refine ⟨1964638465920971168539015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2619517954561294891385353 1964638465920971168539015)
      ·
        refine ⟨2946957698881456752808523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964638465920971168539015 2946957698881456752808523)
        ·
          refine ⟨4420436548322185129212785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946957698881456752808523 4420436548322185129212785)
          ·
            refine ⟨3315327411241638846909589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420436548322185129212785 3315327411241638846909589)
            ·
              refine ⟨155405972401951820948887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3315327411241638846909589 155405972401951820948887)
              ·
                refine ⟨233108958602927731423331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155405972401951820948887 233108958602927731423331)
                ·
                  refine ⟨349663437904391597134997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233108958602927731423331 349663437904391597134997)
                  ·
                    refine ⟨16390473651768356115703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 349663437904391597134997 16390473651768356115703)
                    ·
                      rfl

theorem cell23_95761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_95761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95761 prefixEnd_95761 := by exact prefixLift 95761
  have htrace : WordTrace (prefixWord ++ tailWord_95761) baseStart_95761 baseEnd_95761 := by
    simpa [prefixWord, tailWord_95761, baseEnd_95761] using wordTrace_append hprefix tailTrace_95761
  have hstable : (prefixWord ++ tailWord_95761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95761).length < 2 ^ (prefixWord ++ tailWord_95761).sum := by decide
  have hdescent : baseEnd_95761 < baseStart_95761 := by decide
  rcases family_descends (prefixWord ++ tailWord_95761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95795 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 2, 4]
def baseStart_95795 : Nat := 118140960795 + 95795 * 2 ^ 59
def prefixEnd_95795 : Nat := 4983230072969 + 3 ^ 40 * 95795 * 2
def baseEnd_95795 : Nat := 16396293099185978440651

theorem tailTrace_95795 : CollatzResearch.WordTrace tailWord_95795 prefixEnd_95795 16396293099185978440651 := by
  unfold tailWord_95795
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493930687958550328584839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2329287125305700219056559 3493930687958550328584839)
  ·
    refine ⟨5240896031937825492877259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3493930687958550328584839 5240896031937825492877259)
    ·
      refine ⟨7861344047906738239315889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240896031937825492877259 7861344047906738239315889)
      ·
        refine ⟨5896008035930053679486917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7861344047906738239315889 5896008035930053679486917)
        ·
          refine ⟨1105501506736885064903797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5896008035930053679486917 1105501506736885064903797)
          ·
            refine ⟨103640766256582974834731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1105501506736885064903797 103640766256582974834731)
            ·
              refine ⟨155461149384874462252097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103640766256582974834731 155461149384874462252097)
              ·
                refine ⟨116595862038655846689073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155461149384874462252097 116595862038655846689073)
                ·
                  refine ⟨87446896528991885016805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116595862038655846689073 87446896528991885016805)
                  ·
                    refine ⟨16396293099185978440651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87446896528991885016805 16396293099185978440651)
                    ·
                      rfl

theorem cell23_95795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 4].length) (baseStart_95795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95795 prefixEnd_95795 := by exact prefixLift 95795
  have htrace : WordTrace (prefixWord ++ tailWord_95795) baseStart_95795 baseEnd_95795 := by
    simpa [prefixWord, tailWord_95795, baseEnd_95795] using wordTrace_append hprefix tailTrace_95795
  have hstable : (prefixWord ++ tailWord_95795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95795).length < 2 ^ (prefixWord ++ tailWord_95795).sum := by decide
  have hdescent : baseEnd_95795 < baseStart_95795 := by decide
  rcases family_descends (prefixWord ++ tailWord_95795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95802 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2]
def baseStart_95802 : Nat := 118140960795 + 95802 * 2 ^ 59
def prefixEnd_95802 : Nat := 4983230072969 + 3 ^ 40 * 95802 * 2
def baseEnd_95802 : Nat := 49192473662139407934421

theorem tailTrace_95802 : CollatzResearch.WordTrace tailWord_95802 prefixEnd_95802 49192473662139407934421 := by
  unfold tailWord_95802
  simp only [CollatzResearch.WordTrace]
  refine ⟨873546499733297631022415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2329457332622127016059773 873546499733297631022415)
  ·
    refine ⟨1310319749599946446533623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873546499733297631022415 1310319749599946446533623)
    ·
      refine ⟨1965479624399919669800435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310319749599946446533623 1965479624399919669800435)
      ·
        refine ⟨2948219436599879504700653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965479624399919669800435 2948219436599879504700653)
        ·
          refine ⟨1105582288724954814262745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2948219436599879504700653 1105582288724954814262745)
          ·
            refine ⟨829186716543716110697059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105582288724954814262745 829186716543716110697059)
            ·
              refine ⟨1243780074815574166045589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829186716543716110697059 1243780074815574166045589)
              ·
                refine ⟨58302191006980039033387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1243780074815574166045589 58302191006980039033387)
                ·
                  refine ⟨87453286510470058550081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58302191006980039033387 87453286510470058550081)
                  ·
                    refine ⟨65589964882852543912561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87453286510470058550081 65589964882852543912561)
                    ·
                      refine ⟨49192473662139407934421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65589964882852543912561 49192473662139407934421)
                      ·
                        rfl

theorem cell23_95802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_95802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95802 prefixEnd_95802 := by exact prefixLift 95802
  have htrace : WordTrace (prefixWord ++ tailWord_95802) baseStart_95802 baseEnd_95802 := by
    simpa [prefixWord, tailWord_95802, baseEnd_95802] using wordTrace_append hprefix tailTrace_95802
  have hstable : (prefixWord ++ tailWord_95802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95802).length < 2 ^ (prefixWord ++ tailWord_95802).sum := by decide
  have hdescent : baseEnd_95802 < baseStart_95802 := by decide
  rcases family_descends (prefixWord ++ tailWord_95802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95815 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_95815 : Nat := 118140960795 + 95815 * 2 ^ 59
def prefixEnd_95815 : Nat := 4983230072969 + 3 ^ 40 * 95815 * 2
def baseEnd_95815 : Nat := 49199148910647857071861

theorem tailTrace_95815 : CollatzResearch.WordTrace tailWord_95815 prefixEnd_95815 49199148910647857071861 := by
  unfold tailWord_95815
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494660147886093744312899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2329773431924062496208599 3494660147886093744312899)
  ·
    refine ⟨5241990221829140616469349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494660147886093744312899 5241990221829140616469349)
    ·
      refine ⟨982873166592963865588003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5241990221829140616469349 982873166592963865588003)
      ·
        refine ⟨1474309749889445798382005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982873166592963865588003 1474309749889445798382005)
        ·
          refine ⟨138216539052135543598313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1474309749889445798382005 138216539052135543598313)
          ·
            refine ⟨103662404289101657698735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138216539052135543598313 103662404289101657698735)
            ·
              refine ⟨155493606433652486548103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103662404289101657698735 155493606433652486548103)
              ·
                refine ⟨233240409650478729822155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155493606433652486548103 233240409650478729822155)
                ·
                  refine ⟨349860614475718094733233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233240409650478729822155 349860614475718094733233)
                  ·
                    refine ⟨262395460856788571049925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349860614475718094733233 262395460856788571049925)
                    ·
                      refine ⟨49199148910647857071861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 262395460856788571049925 49199148910647857071861)
                      ·
                        rfl

theorem cell23_95815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_95815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95815 prefixEnd_95815 := by exact prefixLift 95815
  have htrace : WordTrace (prefixWord ++ tailWord_95815) baseStart_95815 baseEnd_95815 := by
    simpa [prefixWord, tailWord_95815, baseEnd_95815] using wordTrace_append hprefix tailTrace_95815
  have hstable : (prefixWord ++ tailWord_95815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95815).length < 2 ^ (prefixWord ++ tailWord_95815).sum := by decide
  have hdescent : baseEnd_95815 < baseStart_95815 := by decide
  rcases family_descends (prefixWord ++ tailWord_95815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95830 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_95830 : Nat := 118140960795 + 95830 * 2 ^ 59
def prefixEnd_95830 : Nat := 4983230072969 + 3 ^ 40 * 95830 * 2
def baseEnd_95830 : Nat := 49206851120465298384293

theorem tailTrace_95830 : CollatzResearch.WordTrace tailWord_95830 prefixEnd_95830 49206851120465298384293 := by
  unfold tailWord_95830
  simp only [CollatzResearch.WordTrace]
  refine ⟨218450452676984456631809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2330138161887834204072629 218450452676984456631809)
  ·
    refine ⟨163837839507738342473857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218450452676984456631809 163837839507738342473857)
    ·
      refine ⟨122878379630803756855393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163837839507738342473857 122878379630803756855393)
      ·
        refine ⟨92158784723102817641545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122878379630803756855393 92158784723102817641545)
        ·
          refine ⟨69119088542327113231159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92158784723102817641545 69119088542327113231159)
          ·
            refine ⟨103678632813490669846739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69119088542327113231159 103678632813490669846739)
            ·
              refine ⟨155517949220236004770109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103678632813490669846739 155517949220236004770109)
              ·
                refine ⟨58319230957588501788791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155517949220236004770109 58319230957588501788791)
                ·
                  refine ⟨87478846436382752683187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58319230957588501788791 87478846436382752683187)
                  ·
                    refine ⟨131218269654574129024781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87478846436382752683187 131218269654574129024781)
                    ·
                      refine ⟨49206851120465298384293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131218269654574129024781 49206851120465298384293)
                      ·
                        rfl

theorem cell23_95830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_95830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95830 prefixEnd_95830 := by exact prefixLift 95830
  have htrace : WordTrace (prefixWord ++ tailWord_95830) baseStart_95830 baseEnd_95830 := by
    simpa [prefixWord, tailWord_95830, baseEnd_95830] using wordTrace_append hprefix tailTrace_95830
  have hstable : (prefixWord ++ tailWord_95830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95830).length < 2 ^ (prefixWord ++ tailWord_95830).sum := by decide
  have hdescent : baseEnd_95830 < baseStart_95830 := by decide
  rcases family_descends (prefixWord ++ tailWord_95830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95831 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_95831 : Nat := 118140960795 + 95831 * 2 ^ 59
def prefixEnd_95831 : Nat := 4983230072969 + 3 ^ 40 * 95831 * 2
def baseEnd_95831 : Nat := 49207364601119794471787

theorem tailTrace_95831 : CollatzResearch.WordTrace tailWord_95831 prefixEnd_95831 49207364601119794471787 := by
  unfold tailWord_95831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495243715828128476895347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2330162477218752317930231 3495243715828128476895347)
  ·
    refine ⟨5242865573742192715343021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3495243715828128476895347 5242865573742192715343021)
    ·
      refine ⟨1966074590153322268253633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5242865573742192715343021 1966074590153322268253633)
      ·
        refine ⟨1474555942614991701190225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1966074590153322268253633 1474555942614991701190225)
        ·
          refine ⟨1105916956961243775892669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474555942614991701190225 1105916956961243775892669)
          ·
            refine ⟨414718858860466415959751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1105916956961243775892669 414718858860466415959751)
            ·
              refine ⟨622078288290699623939627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414718858860466415959751 622078288290699623939627)
              ·
                refine ⟨933117432436049435909441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622078288290699623939627 933117432436049435909441)
                ·
                  refine ⟨699838074327037076932081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 933117432436049435909441 699838074327037076932081)
                  ·
                    refine ⟨524878555745277807699061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 699838074327037076932081 524878555745277807699061)
                    ·
                      refine ⟨49207364601119794471787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 524878555745277807699061 49207364601119794471787)
                      ·
                        rfl

theorem cell23_95831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_95831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95831 prefixEnd_95831 := by exact prefixLift 95831
  have htrace : WordTrace (prefixWord ++ tailWord_95831) baseStart_95831 baseEnd_95831 := by
    simpa [prefixWord, tailWord_95831, baseEnd_95831] using wordTrace_append hprefix tailTrace_95831
  have hstable : (prefixWord ++ tailWord_95831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95831).length < 2 ^ (prefixWord ++ tailWord_95831).sum := by decide
  have hdescent : baseEnd_95831 < baseStart_95831 := by decide
  rcases family_descends (prefixWord ++ tailWord_95831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95836 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_95836 : Nat := 118140960795 + 95836 * 2 ^ 59
def prefixEnd_95836 : Nat := 4983230072969 + 3 ^ 40 * 95836 * 2
def baseEnd_95836 : Nat := 49209932004392274909265

theorem tailTrace_95836 : CollatzResearch.WordTrace tailWord_95836 prefixEnd_95836 49209932004392274909265 := by
  unfold tailWord_95836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747713040405007165413681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2330284053873342887218241 1747713040405007165413681)
  ·
    refine ⟨1310784780303755374060261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1747713040405007165413681 1310784780303755374060261)
    ·
      refine ⟨245772146306954132636299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1310784780303755374060261 245772146306954132636299)
      ·
        refine ⟨368658219460431198954449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245772146306954132636299 368658219460431198954449)
        ·
          refine ⟨276493664595323399215837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368658219460431198954449 276493664595323399215837)
          ·
            refine ⟨103685124223246274705939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276493664595323399215837 103685124223246274705939)
            ·
              refine ⟨155527686334869412058909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103685124223246274705939 155527686334869412058909)
              ·
                refine ⟨58322882375576029522091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155527686334869412058909 58322882375576029522091)
                ·
                  refine ⟨87484323563364044283137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58322882375576029522091 87484323563364044283137)
                  ·
                    refine ⟨65613242672523033212353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87484323563364044283137 65613242672523033212353)
                    ·
                      refine ⟨49209932004392274909265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65613242672523033212353 49209932004392274909265)
                      ·
                        rfl

theorem cell23_95836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_95836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95836 prefixEnd_95836 := by exact prefixLift 95836
  have htrace : WordTrace (prefixWord ++ tailWord_95836) baseStart_95836 baseEnd_95836 := by
    simpa [prefixWord, tailWord_95836, baseEnd_95836] using wordTrace_append hprefix tailTrace_95836
  have hstable : (prefixWord ++ tailWord_95836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95836).length < 2 ^ (prefixWord ++ tailWord_95836).sum := by decide
  have hdescent : baseEnd_95836 < baseStart_95836 := by decide
  rcases family_descends (prefixWord ++ tailWord_95836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95869 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_95869 : Nat := 118140960795 + 95869 * 2 ^ 59
def prefixEnd_95869 : Nat := 4983230072969 + 3 ^ 40 * 95869 * 2
def baseEnd_95869 : Nat := 49226876865990645796613

theorem tailTrace_95869 : CollatzResearch.WordTrace tailWord_95869 prefixEnd_95869 49226876865990645796613 := by
  unfold tailWord_95869
  simp only [CollatzResearch.WordTrace]
  refine ⟨3496629689690460966778661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2331086459793640644519107 3496629689690460966778661)
  ·
    refine ⟨655618066816961431270999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3496629689690460966778661 655618066816961431270999)
    ·
      refine ⟨983427100225442146906499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655618066816961431270999 983427100225442146906499)
      ·
        refine ⟨1475140650338163220359749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983427100225442146906499 1475140650338163220359749)
        ·
          refine ⟨276588871938405603817453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1475140650338163220359749 276588871938405603817453)
          ·
            refine ⟨103720826976902101431545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276588871938405603817453 103720826976902101431545)
            ·
              refine ⟨77790620232676576073659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103720826976902101431545 77790620232676576073659)
              ·
                refine ⟨116685930349014864110489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77790620232676576073659 116685930349014864110489)
                ·
                  refine ⟨87514447761761148082867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116685930349014864110489 87514447761761148082867)
                  ·
                    refine ⟨131271671642641722124301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87514447761761148082867 131271671642641722124301)
                    ·
                      refine ⟨49226876865990645796613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131271671642641722124301 49226876865990645796613)
                      ·
                        rfl

theorem cell23_95869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_95869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95869 prefixEnd_95869 := by exact prefixLift 95869
  have htrace : WordTrace (prefixWord ++ tailWord_95869) baseStart_95869 baseEnd_95869 := by
    simpa [prefixWord, tailWord_95869, baseEnd_95869] using wordTrace_append hprefix tailTrace_95869
  have hstable : (prefixWord ++ tailWord_95869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95869).length < 2 ^ (prefixWord ++ tailWord_95869).sum := by decide
  have hdescent : baseEnd_95869 < baseStart_95869 := by decide
  rcases family_descends (prefixWord ++ tailWord_95869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95871 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_95871 : Nat := 118140960795 + 95871 * 2 ^ 59
def prefixEnd_95871 : Nat := 4983230072969 + 3 ^ 40 * 95871 * 2
def baseEnd_95871 : Nat := 49227903827299637971603

theorem tailTrace_95871 : CollatzResearch.WordTrace tailWord_95871 prefixEnd_95871 49227903827299637971603 := by
  unfold tailWord_95871
  simp only [CollatzResearch.WordTrace]
  refine ⟨3496702635683215308351467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2331135090455476872234311 3496702635683215308351467)
  ·
    refine ⟨5245053953524822962527201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3496702635683215308351467 5245053953524822962527201)
    ·
      refine ⟨3933790465143617221895401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5245053953524822962527201 3933790465143617221895401)
      ·
        refine ⟨2950342848857712916421551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3933790465143617221895401 2950342848857712916421551)
        ·
          refine ⟨4425514273286569374632327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950342848857712916421551 4425514273286569374632327)
          ·
            refine ⟨6638271409929854061948491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425514273286569374632327 6638271409929854061948491)
            ·
              refine ⟨9957407114894781092922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638271409929854061948491 9957407114894781092922737)
              ·
                refine ⟨7468055336171085819692053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9957407114894781092922737 7468055336171085819692053)
                ·
                  refine ⟨350065093883019647798065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7468055336171085819692053 350065093883019647798065)
                  ·
                    refine ⟨262548820412264735848549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 350065093883019647798065 262548820412264735848549)
                    ·
                      refine ⟨49227903827299637971603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 262548820412264735848549 49227903827299637971603)
                      ·
                        rfl

theorem cell23_95871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_95871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95871 prefixEnd_95871 := by exact prefixLift 95871
  have htrace : WordTrace (prefixWord ++ tailWord_95871) baseStart_95871 baseEnd_95871 := by
    simpa [prefixWord, tailWord_95871, baseEnd_95871] using wordTrace_append hprefix tailTrace_95871
  have hstable : (prefixWord ++ tailWord_95871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95871).length < 2 ^ (prefixWord ++ tailWord_95871).sum := by decide
  have hdescent : baseEnd_95871 < baseStart_95871 := by decide
  rcases family_descends (prefixWord ++ tailWord_95871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95881 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 7]
def baseStart_95881 : Nat := 118140960795 + 95881 * 2 ^ 59
def prefixEnd_95881 : Nat := 4983230072969 + 3 ^ 40 * 95881 * 2
def baseEnd_95881 : Nat := 5470337625982733205173

theorem tailTrace_95881 : CollatzResearch.WordTrace tailWord_95881 prefixEnd_95881 5470337625982733205173 := by
  unfold tailWord_95881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497067365646987016215497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2331378243764658010810331 3497067365646987016215497)
  ·
    refine ⟨2622800524235240262161623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3497067365646987016215497 2622800524235240262161623)
    ·
      refine ⟨3934200786352860393242435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622800524235240262161623 3934200786352860393242435)
      ·
        refine ⟨5901301179529290589863653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934200786352860393242435 5901301179529290589863653)
        ·
          refine ⟨1106493971161741985599435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5901301179529290589863653 1106493971161741985599435)
          ·
            refine ⟨1659740956742612978399153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106493971161741985599435 1659740956742612978399153)
            ·
              refine ⟨1244805717556959733799365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659740956742612978399153 1244805717556959733799365)
              ·
                refine ⟨233401072041929950087381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1244805717556959733799365 233401072041929950087381)
                ·
                  refine ⟨5470337625982733205173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 233401072041929950087381 5470337625982733205173)
                  ·
                    rfl

theorem cell23_95881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_95881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95881 prefixEnd_95881 := by exact prefixLift 95881
  have htrace : WordTrace (prefixWord ++ tailWord_95881) baseStart_95881 baseEnd_95881 := by
    simpa [prefixWord, tailWord_95881, baseEnd_95881] using wordTrace_append hprefix tailTrace_95881
  have hstable : (prefixWord ++ tailWord_95881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95881).length < 2 ^ (prefixWord ++ tailWord_95881).sum := by decide
  have hdescent : baseEnd_95881 < baseStart_95881 := by decide
  rcases family_descends (prefixWord ++ tailWord_95881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95926 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_95926 : Nat := 118140960795 + 95926 * 2 ^ 59
def prefixEnd_95926 : Nat := 4983230072969 + 3 ^ 40 * 95926 * 2
def baseEnd_95926 : Nat := 49256145263296922783851

theorem tailTrace_95926 : CollatzResearch.WordTrace tailWord_95926 prefixEnd_95926 49256145263296922783851 := by
  unfold tailWord_95926
  simp only [CollatzResearch.WordTrace]
  refine ⟨218669290655247481350227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2332472433655973134402421 218669290655247481350227)
  ·
    refine ⟨328003935982871222025341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218669290655247481350227 328003935982871222025341)
    ·
      refine ⟨123001475993576708259503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328003935982871222025341 123001475993576708259503)
      ·
        refine ⟨184502213990365062389255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123001475993576708259503 184502213990365062389255)
        ·
          refine ⟨276753320985547593583883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184502213990365062389255 276753320985547593583883)
          ·
            refine ⟨415129981478321390375825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276753320985547593583883 415129981478321390375825)
            ·
              refine ⟨311347486108741042781869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415129981478321390375825 311347486108741042781869)
              ·
                refine ⟨116755307290777891043201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311347486108741042781869 116755307290777891043201)
                ·
                  refine ⟨87566480468083418282401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116755307290777891043201 87566480468083418282401)
                  ·
                    refine ⟨65674860351062563711801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87566480468083418282401 65674860351062563711801)
                    ·
                      refine ⟨49256145263296922783851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65674860351062563711801 49256145263296922783851)
                      ·
                        rfl

theorem cell23_95926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_95926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95926 prefixEnd_95926 := by exact prefixLift 95926
  have htrace : WordTrace (prefixWord ++ tailWord_95926) baseStart_95926 baseEnd_95926 := by
    simpa [prefixWord, tailWord_95926, baseEnd_95926] using wordTrace_append hprefix tailTrace_95926
  have hstable : (prefixWord ++ tailWord_95926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95926).length < 2 ^ (prefixWord ++ tailWord_95926).sum := by decide
  have hdescent : baseEnd_95926 < baseStart_95926 := by decide
  rcases family_descends (prefixWord ++ tailWord_95926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95941 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_95941 : Nat := 118140960795 + 95941 * 2 ^ 59
def prefixEnd_95941 : Nat := 4983230072969 + 3 ^ 40 * 95941 * 2
def baseEnd_95941 : Nat := 16421282491038121365427

theorem tailTrace_95941 : CollatzResearch.WordTrace tailWord_95941 prefixEnd_95941 16421282491038121365427 := by
  unfold tailWord_95941
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499255745429617263399677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2332837163619744842266451 3499255745429617263399677)
  ·
    refine ⟨1312220904536106473774879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3499255745429617263399677 1312220904536106473774879)
    ·
      refine ⟨1968331356804159710662319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312220904536106473774879 1968331356804159710662319)
      ·
        refine ⟨2952497035206239565993479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968331356804159710662319 2952497035206239565993479)
        ·
          refine ⟨4428745552809359348990219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952497035206239565993479 4428745552809359348990219)
          ·
            refine ⟨6643118329214039023485329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428745552809359348990219 6643118329214039023485329)
            ·
              refine ⟨4982338746910529267613997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6643118329214039023485329 4982338746910529267613997)
              ·
                refine ⟨1868377030091448475355249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4982338746910529267613997 1868377030091448475355249)
                ·
                  refine ⟨1401282772568586356516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868377030091448475355249 1401282772568586356516437)
                  ·
                    refine ⟨16421282491038121365427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1401282772568586356516437 16421282491038121365427)
                    ·
                      rfl

theorem cell23_95941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_95941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95941 prefixEnd_95941 := by exact prefixLift 95941
  have htrace : WordTrace (prefixWord ++ tailWord_95941) baseStart_95941 baseEnd_95941 := by
    simpa [prefixWord, tailWord_95941, baseEnd_95941] using wordTrace_append hprefix tailTrace_95941
  have hstable : (prefixWord ++ tailWord_95941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95941).length < 2 ^ (prefixWord ++ tailWord_95941).sum := by decide
  have hdescent : baseEnd_95941 < baseStart_95941 := by decide
  rcases family_descends (prefixWord ++ tailWord_95941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95949 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 5]
def baseStart_95949 : Nat := 118140960795 + 95949 * 2 ^ 59
def prefixEnd_95949 : Nat := 4983230072969 + 3 ^ 40 * 95949 * 2
def baseEnd_95949 : Nat := 5474217257594481421805

theorem tailTrace_95949 : CollatzResearch.WordTrace tailWord_95949 prefixEnd_95949 5474217257594481421805 := by
  unfold tailWord_95949
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499547529400634629690901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2333031686267089753127267 3499547529400634629690901)
  ·
    refine ⟨164041290440654748266761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3499547529400634629690901 164041290440654748266761)
    ·
      refine ⟨123030967830491061200071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164041290440654748266761 123030967830491061200071)
      ·
        refine ⟨184546451745736591800107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123030967830491061200071 184546451745736591800107)
        ·
          refine ⟨276819677618604887700161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184546451745736591800107 276819677618604887700161)
          ·
            refine ⟨207614758213953665775121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276819677618604887700161 207614758213953665775121)
            ·
              refine ⟨155711068660465249331341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207614758213953665775121 155711068660465249331341)
              ·
                refine ⟨58391650747674468499253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155711068660465249331341 58391650747674468499253)
                ·
                  refine ⟨5474217257594481421805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58391650747674468499253 5474217257594481421805)
                  ·
                    rfl

theorem cell23_95949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_95949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_95949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_95949 prefixEnd_95949 := by exact prefixLift 95949
  have htrace : WordTrace (prefixWord ++ tailWord_95949) baseStart_95949 baseEnd_95949 := by
    simpa [prefixWord, tailWord_95949, baseEnd_95949] using wordTrace_append hprefix tailTrace_95949
  have hstable : (prefixWord ++ tailWord_95949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95949).length < 2 ^ (prefixWord ++ tailWord_95949).sum := by decide
  have hdescent : baseEnd_95949 < baseStart_95949 := by decide
  rcases family_descends (prefixWord ++ tailWord_95949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96002 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_96002 : Nat := 118140960795 + 96002 * 2 ^ 59
def prefixEnd_96002 : Nat := 4983230072969 + 3 ^ 40 * 96002 * 2
def baseEnd_96002 : Nat := 49295169793038625433501

theorem tailTrace_96002 : CollatzResearch.WordTrace tailWord_96002 prefixEnd_96002 49295169793038625433501 := by
  unfold tailWord_96002
  simp only [CollatzResearch.WordTrace]
  refine ⟨875370149552156170342565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2334320398805749787580173 875370149552156170342565)
  ·
    refine ⟨164131903041029281939231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 875370149552156170342565 164131903041029281939231)
    ·
      refine ⟨246197854561543922908847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164131903041029281939231 246197854561543922908847)
      ·
        refine ⟨369296781842315884363271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246197854561543922908847 369296781842315884363271)
        ·
          refine ⟨553945172763473826544907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369296781842315884363271 553945172763473826544907)
          ·
            refine ⟨830917759145210739817361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553945172763473826544907 830917759145210739817361)
            ·
              refine ⟨623188319358908054863021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830917759145210739817361 623188319358908054863021)
              ·
                refine ⟨233695619759590520573633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623188319358908054863021 233695619759590520573633)
                ·
                  refine ⟨175271714819692890430225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233695619759590520573633 175271714819692890430225)
                  ·
                    refine ⟨131453786114769667822669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175271714819692890430225 131453786114769667822669)
                    ·
                      refine ⟨49295169793038625433501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131453786114769667822669 49295169793038625433501)
                      ·
                        rfl

theorem cell23_96002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_96002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96002 prefixEnd_96002 := by exact prefixLift 96002
  have htrace : WordTrace (prefixWord ++ tailWord_96002) baseStart_96002 baseEnd_96002 := by
    simpa [prefixWord, tailWord_96002, baseEnd_96002] using wordTrace_append hprefix tailTrace_96002
  have hstable : (prefixWord ++ tailWord_96002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96002).length < 2 ^ (prefixWord ++ tailWord_96002).sum := by decide
  have hdescent : baseEnd_96002 < baseStart_96002 := by decide
  rcases family_descends (prefixWord ++ tailWord_96002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96052 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_96052 : Nat := 118140960795 + 96052 * 2 ^ 59
def prefixEnd_96052 : Nat := 4983230072969 + 3 ^ 40 * 96052 * 2
def baseEnd_96052 : Nat := 16440281275254476602757

theorem tailTrace_96052 : CollatzResearch.WordTrace tailWord_96052 prefixEnd_96052 16440281275254476602757 := by
  unfold tailWord_96052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751652124013741610345205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2335536165351655480460273 1751652124013741610345205)
  ·
    refine ⟨164217386626288275969863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1751652124013741610345205 164217386626288275969863)
    ·
      refine ⟨246326079939432413954795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164217386626288275969863 246326079939432413954795)
      ·
        refine ⟨369489119909148620932193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246326079939432413954795 369489119909148620932193)
        ·
          refine ⟨277116839931861465699145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369489119909148620932193 277116839931861465699145)
          ·
            refine ⟨207837629948896099274359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277116839931861465699145 207837629948896099274359)
            ·
              refine ⟨311756444923344148911539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207837629948896099274359 311756444923344148911539)
              ·
                refine ⟨467634667385016223367309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311756444923344148911539 467634667385016223367309)
                ·
                  refine ⟨175363000269381083762741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 467634667385016223367309 175363000269381083762741)
                  ·
                    refine ⟨16440281275254476602757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175363000269381083762741 16440281275254476602757)
                    ·
                      rfl

theorem cell23_96052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_96052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96052 prefixEnd_96052 := by exact prefixLift 96052
  have htrace : WordTrace (prefixWord ++ tailWord_96052) baseStart_96052 baseEnd_96052 := by
    simpa [prefixWord, tailWord_96052, baseEnd_96052] using wordTrace_append hprefix tailTrace_96052
  have hstable : (prefixWord ++ tailWord_96052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96052).length < 2 ^ (prefixWord ++ tailWord_96052).sum := by decide
  have hdescent : baseEnd_96052 < baseStart_96052 := by decide
  rcases family_descends (prefixWord ++ tailWord_96052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96055 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_96055 : Nat := 118140960795 + 96055 * 2 ^ 59
def prefixEnd_96055 : Nat := 4983230072969 + 3 ^ 40 * 96055 * 2
def baseEnd_96055 : Nat := 49322384267726918070757

theorem tailTrace_96055 : CollatzResearch.WordTrace tailWord_96055 prefixEnd_96055 49322384267726918070757 := by
  unfold tailWord_96055
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503413667016614733049619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2335609111344409822033079 3503413667016614733049619)
  ·
    refine ⟨5255120500524922099574429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3503413667016614733049619 5255120500524922099574429)
    ·
      refine ⟨1970670187696845787340411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5255120500524922099574429 1970670187696845787340411)
      ·
        refine ⟨2956005281545268681010617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970670187696845787340411 2956005281545268681010617)
        ·
          refine ⟨2217003961158951510757963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2956005281545268681010617 2217003961158951510757963)
          ·
            refine ⟨3325505941738427266136945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217003961158951510757963 3325505941738427266136945)
            ·
              refine ⟨2494129456303820449602709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325505941738427266136945 2494129456303820449602709)
              ·
                refine ⟨116912318264241583575127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2494129456303820449602709 116912318264241583575127)
                ·
                  refine ⟨175368477396362375362691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116912318264241583575127 175368477396362375362691)
                  ·
                    refine ⟨263052716094543563044037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175368477396362375362691 263052716094543563044037)
                    ·
                      refine ⟨49322384267726918070757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 263052716094543563044037 49322384267726918070757)
                      ·
                        rfl

theorem cell23_96055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_96055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96055 prefixEnd_96055 := by exact prefixLift 96055
  have htrace : WordTrace (prefixWord ++ tailWord_96055) baseStart_96055 baseEnd_96055 := by
    simpa [prefixWord, tailWord_96055, baseEnd_96055] using wordTrace_append hprefix tailTrace_96055
  have hstable : (prefixWord ++ tailWord_96055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96055).length < 2 ^ (prefixWord ++ tailWord_96055).sum := by decide
  have hdescent : baseEnd_96055 < baseStart_96055 := by decide
  rcases family_descends (prefixWord ++ tailWord_96055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96082 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_96082 : Nat := 118140960795 + 96082 * 2 ^ 59
def prefixEnd_96082 : Nat := 4983230072969 + 3 ^ 40 * 96082 * 2
def baseEnd_96082 : Nat := 16445416081799437477711

theorem tailTrace_96082 : CollatzResearch.WordTrace tailWord_96082 prefixEnd_96082 16445416081799437477711 := by
  unfold tailWord_96082
  simp only [CollatzResearch.WordTrace]
  refine ⟨876099609479699586070625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2336265625279198896188333 876099609479699586070625)
  ·
    refine ⟨657074707109774689552969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 876099609479699586070625 657074707109774689552969)
    ·
      refine ⟨492806030332331017164727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 657074707109774689552969 492806030332331017164727)
      ·
        refine ⟨739209045498496525747091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492806030332331017164727 739209045498496525747091)
        ·
          refine ⟨1108813568247744788620637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739209045498496525747091 1108813568247744788620637)
          ·
            refine ⟨415805088092904295732739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1108813568247744788620637 415805088092904295732739)
            ·
              refine ⟨623707632139356443599109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415805088092904295732739 623707632139356443599109)
              ·
                refine ⟨116945181026129333174833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623707632139356443599109 116945181026129333174833)
                ·
                  refine ⟨87708885769596999881125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116945181026129333174833 87708885769596999881125)
                  ·
                    refine ⟨16445416081799437477711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87708885769596999881125 16445416081799437477711)
                    ·
                      rfl

theorem cell23_96082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_96082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96082 prefixEnd_96082 := by exact prefixLift 96082
  have htrace : WordTrace (prefixWord ++ tailWord_96082) baseStart_96082 baseEnd_96082 := by
    simpa [prefixWord, tailWord_96082, baseEnd_96082] using wordTrace_append hprefix tailTrace_96082
  have hstable : (prefixWord ++ tailWord_96082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96082).length < 2 ^ (prefixWord ++ tailWord_96082).sum := by decide
  have hdescent : baseEnd_96082 < baseStart_96082 := by decide
  rcases family_descends (prefixWord ++ tailWord_96082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96095 : List Nat := [1, 1, 2, 3, 1, 6, 1, 8]
def baseStart_96095 : Nat := 118140960795 + 96095 * 2 ^ 59
def prefixEnd_96095 : Nat := 4983230072969 + 3 ^ 40 * 96095 * 2
def baseEnd_96095 : Nat := 1827515684959509687799

theorem tailTrace_96095 : CollatzResearch.WordTrace tailWord_96095 prefixEnd_96095 1827515684959509687799 := by
  unfold tailWord_96095
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504872586871701564505739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2336581724581134376337159 3504872586871701564505739)
  ·
    refine ⟨5257308880307552346758609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3504872586871701564505739 5257308880307552346758609)
    ·
      refine ⟨3942981660230664260068957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5257308880307552346758609 3942981660230664260068957)
      ·
        refine ⟨1478618122586499097525859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3942981660230664260068957 1478618122586499097525859)
        ·
          refine ⟨2217927183879748646288789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478618122586499097525859 2217927183879748646288789)
          ·
            refine ⟨103965336744363217794787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2217927183879748646288789 103965336744363217794787)
            ·
              refine ⟨155948005116544826692181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103965336744363217794787 155948005116544826692181)
              ·
                refine ⟨1827515684959509687799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 155948005116544826692181 1827515684959509687799)
                ·
                  rfl

theorem cell23_96095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 8].length) (baseStart_96095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96095 prefixEnd_96095 := by exact prefixLift 96095
  have htrace : WordTrace (prefixWord ++ tailWord_96095) baseStart_96095 baseEnd_96095 := by
    simpa [prefixWord, tailWord_96095, baseEnd_96095] using wordTrace_append hprefix tailTrace_96095
  have hstable : (prefixWord ++ tailWord_96095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96095).length < 2 ^ (prefixWord ++ tailWord_96095).sum := by decide
  have hdescent : baseEnd_96095 < baseStart_96095 := by decide
  rcases family_descends (prefixWord ++ tailWord_96095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96126 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_96126 : Nat := 118140960795 + 96126 * 2 ^ 59
def prefixEnd_96126 : Nat := 4983230072969 + 3 ^ 40 * 96126 * 2
def baseEnd_96126 : Nat := 49358841394196140282931

theorem tailTrace_96126 : CollatzResearch.WordTrace tailWord_96126 prefixEnd_96126 49358841394196140282931 := by
  unfold tailWord_96126
  simp only [CollatzResearch.WordTrace]
  refine ⟨438250406219924232360529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2337335499839595905922821 438250406219924232360529)
  ·
    refine ⟨328687804664943174270397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 438250406219924232360529 328687804664943174270397)
    ·
      refine ⟨123257926749353690351399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328687804664943174270397 123257926749353690351399)
      ·
        refine ⟨184886890124030535527099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123257926749353690351399 184886890124030535527099)
        ·
          refine ⟨277330335186045803290649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184886890124030535527099 277330335186045803290649)
          ·
            refine ⟨207997751389534352467987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277330335186045803290649 207997751389534352467987)
            ·
              refine ⟨311996627084301528701981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207997751389534352467987 311996627084301528701981)
              ·
                refine ⟨116998735156613073263243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311996627084301528701981 116998735156613073263243)
                ·
                  refine ⟨175498102734919609894865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116998735156613073263243 175498102734919609894865)
                  ·
                    refine ⟨131623577051189707421149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175498102734919609894865 131623577051189707421149)
                    ·
                      refine ⟨49358841394196140282931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131623577051189707421149 49358841394196140282931)
                      ·
                        rfl

theorem cell23_96126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_96126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96126 prefixEnd_96126 := by exact prefixLift 96126
  have htrace : WordTrace (prefixWord ++ tailWord_96126) baseStart_96126 baseEnd_96126 := by
    simpa [prefixWord, tailWord_96126, baseEnd_96126] using wordTrace_append hprefix tailTrace_96126
  have hstable : (prefixWord ++ tailWord_96126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96126).length < 2 ^ (prefixWord ++ tailWord_96126).sum := by decide
  have hdescent : baseEnd_96126 < baseStart_96126 := by decide
  rcases family_descends (prefixWord ++ tailWord_96126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96150 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_96150 : Nat := 118140960795 + 96150 * 2 ^ 59
def prefixEnd_96150 : Nat := 4983230072969 + 3 ^ 40 * 96150 * 2
def baseEnd_96150 : Nat := 16457054976634682127607

theorem tailTrace_96150 : CollatzResearch.WordTrace tailWord_96150 prefixEnd_96150 16457054976634682127607 := by
  unfold tailWord_96150
  simp only [CollatzResearch.WordTrace]
  refine ⟨219179912604527872359869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2337919067781630638505269 219179912604527872359869)
  ·
    refine ⟨82192467226697952134951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219179912604527872359869 82192467226697952134951)
    ·
      refine ⟨123288700840046928202427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82192467226697952134951 123288700840046928202427)
      ·
        refine ⟨184933051260070392303641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123288700840046928202427 184933051260070392303641)
        ·
          refine ⟨138699788445052794227731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184933051260070392303641 138699788445052794227731)
          ·
            refine ⟨208049682667579191341597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138699788445052794227731 208049682667579191341597)
            ·
              refine ⟨78018631000342196753099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208049682667579191341597 78018631000342196753099)
              ·
                refine ⟨117027946500513295129649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78018631000342196753099 117027946500513295129649)
                ·
                  refine ⟨87770959875384971347237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117027946500513295129649 87770959875384971347237)
                  ·
                    refine ⟨16457054976634682127607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87770959875384971347237 16457054976634682127607)
                    ·
                      rfl

theorem cell23_96150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_96150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96150 prefixEnd_96150 := by exact prefixLift 96150
  have htrace : WordTrace (prefixWord ++ tailWord_96150) baseStart_96150 baseEnd_96150 := by
    simpa [prefixWord, tailWord_96150, baseEnd_96150] using wordTrace_append hprefix tailTrace_96150
  have hstable : (prefixWord ++ tailWord_96150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96150).length < 2 ^ (prefixWord ++ tailWord_96150).sum := by decide
  have hdescent : baseEnd_96150 < baseStart_96150 := by decide
  rcases family_descends (prefixWord ++ tailWord_96150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96165 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_96165 : Nat := 118140960795 + 96165 * 2 ^ 59
def prefixEnd_96165 : Nat := 4983230072969 + 3 ^ 40 * 96165 * 2
def baseEnd_96165 : Nat := 49378867139721487695251

theorem tailTrace_96165 : CollatzResearch.WordTrace tailWord_96165 prefixEnd_96165 49378867139721487695251 := by
  unfold tailWord_96165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507425696618103519553949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2338283797745402346369299 3507425696618103519553949)
  ·
    refine ⟨1315284636231788819832731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3507425696618103519553949 1315284636231788819832731)
    ·
      refine ⟨1972926954347683229749097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315284636231788819832731 1972926954347683229749097)
      ·
        refine ⟨1479695215760762422311823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972926954347683229749097 1479695215760762422311823)
        ·
          refine ⟨2219542823641143633467735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479695215760762422311823 2219542823641143633467735)
          ·
            refine ⟨3329314235461715450201603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219542823641143633467735 3329314235461715450201603)
            ·
              refine ⟨4993971353192573175302405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329314235461715450201603 4993971353192573175302405)
              ·
                refine ⟨936369628723607470369201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4993971353192573175302405 936369628723607470369201)
                ·
                  refine ⟨702277221542705602776901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 936369628723607470369201 702277221542705602776901)
                  ·
                    refine ⟨131676979039257300520669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702277221542705602776901 131676979039257300520669)
                    ·
                      refine ⟨49378867139721487695251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131676979039257300520669 49378867139721487695251)
                      ·
                        rfl

theorem cell23_96165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_96165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96165 prefixEnd_96165 := by exact prefixLift 96165
  have htrace : WordTrace (prefixWord ++ tailWord_96165) baseStart_96165 baseEnd_96165 := by
    simpa [prefixWord, tailWord_96165, baseEnd_96165] using wordTrace_append hprefix tailTrace_96165
  have hstable : (prefixWord ++ tailWord_96165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96165).length < 2 ^ (prefixWord ++ tailWord_96165).sum := by decide
  have hdescent : baseEnd_96165 < baseStart_96165 := by decide
  rcases family_descends (prefixWord ++ tailWord_96165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96174 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_96174 : Nat := 118140960795 + 96174 * 2 ^ 59
def prefixEnd_96174 : Nat := 4983230072969 + 3 ^ 40 * 96174 * 2
def baseEnd_96174 : Nat := 49383488465611952482711

theorem tailTrace_96174 : CollatzResearch.WordTrace tailWord_96174 prefixEnd_96174 49383488465611952482711 := by
  unfold tailWord_96174
  simp only [CollatzResearch.WordTrace]
  refine ⟨438469244198187257078947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2338502635723665371087717 438469244198187257078947)
  ·
    refine ⟨657703866297280885618421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438469244198187257078947 657703866297280885618421)
    ·
      refine ⟨61659737465370083026727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 657703866297280885618421 61659737465370083026727)
      ·
        refine ⟨92489606198055124540091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61659737465370083026727 92489606198055124540091)
        ·
          refine ⟨138734409297082686810137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92489606198055124540091 138734409297082686810137)
          ·
            refine ⟨104050806972812015107603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138734409297082686810137 104050806972812015107603)
            ·
              refine ⟨156076210459218022661405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104050806972812015107603 156076210459218022661405)
              ·
                refine ⟨58528578922206758498027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156076210459218022661405 58528578922206758498027)
                ·
                  refine ⟨87792868383310137747041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58528578922206758498027 87792868383310137747041)
                  ·
                    refine ⟨65844651287482603310281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87792868383310137747041 65844651287482603310281)
                    ·
                      refine ⟨49383488465611952482711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65844651287482603310281 49383488465611952482711)
                      ·
                        rfl

theorem cell23_96174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_96174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96174 prefixEnd_96174 := by exact prefixLift 96174
  have htrace : WordTrace (prefixWord ++ tailWord_96174) baseStart_96174 baseEnd_96174 := by
    simpa [prefixWord, tailWord_96174, baseEnd_96174] using wordTrace_append hprefix tailTrace_96174
  have hstable : (prefixWord ++ tailWord_96174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96174).length < 2 ^ (prefixWord ++ tailWord_96174).sum := by decide
  have hdescent : baseEnd_96174 < baseStart_96174 := by decide
  rcases family_descends (prefixWord ++ tailWord_96174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96202 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_96202 : Nat := 118140960795 + 96202 * 2 ^ 59
def prefixEnd_96202 : Nat := 4983230072969 + 3 ^ 40 * 96202 * 2
def baseEnd_96202 : Nat := 5488651769326426992509

theorem tailTrace_96202 : CollatzResearch.WordTrace tailWord_96202 prefixEnd_96202 5488651769326426992509 := by
  unfold tailWord_96202
  simp only [CollatzResearch.WordTrace]
  refine ⟨877193799371014709662715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2339183464989372559100573 877193799371014709662715)
  ·
    refine ⟨1315790699056522064494073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 877193799371014709662715 1315790699056522064494073)
    ·
      refine ⟨986843024292391548370555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1315790699056522064494073 986843024292391548370555)
      ·
        refine ⟨1480264536438587322555833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986843024292391548370555 1480264536438587322555833)
        ·
          refine ⟨1110198402328940491916875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480264536438587322555833 1110198402328940491916875)
          ·
            refine ⟨1665297603493410737875313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110198402328940491916875 1665297603493410737875313)
            ·
              refine ⟨1248973202620058053406485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665297603493410737875313 1248973202620058053406485)
              ·
                refine ⟨58545618872815221253429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1248973202620058053406485 58545618872815221253429)
                ·
                  refine ⟨5488651769326426992509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58545618872815221253429 5488651769326426992509)
                  ·
                    rfl

theorem cell23_96202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_96202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96202 prefixEnd_96202 := by exact prefixLift 96202
  have htrace : WordTrace (prefixWord ++ tailWord_96202) baseStart_96202 baseEnd_96202 := by
    simpa [prefixWord, tailWord_96202, baseEnd_96202] using wordTrace_append hprefix tailTrace_96202
  have hstable : (prefixWord ++ tailWord_96202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96202).length < 2 ^ (prefixWord ++ tailWord_96202).sum := by decide
  have hdescent : baseEnd_96202 < baseStart_96202 := by decide
  rcases family_descends (prefixWord ++ tailWord_96202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96212 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_96212 : Nat := 118140960795 + 96212 * 2 ^ 59
def prefixEnd_96212 : Nat := 4983230072969 + 3 ^ 40 * 96212 * 2
def baseEnd_96212 : Nat := 49403000730482803807535

theorem tailTrace_96212 : CollatzResearch.WordTrace tailWord_96212 prefixEnd_96212 49403000730482803807535 := by
  unfold tailWord_96212
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754569963723915273257445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2339426618298553697676593 1754569963723915273257445)
  ·
    refine ⟨328981868198234113735771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1754569963723915273257445 328981868198234113735771)
    ·
      refine ⟨493472802297351170603657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328981868198234113735771 493472802297351170603657)
      ·
        refine ⟨370104601723013377952743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493472802297351170603657 370104601723013377952743)
        ·
          refine ⟨555156902584520066929115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370104601723013377952743 555156902584520066929115)
          ·
            refine ⟨832735353876780100393673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555156902584520066929115 832735353876780100393673)
            ·
              refine ⟨624551515407585075295255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832735353876780100393673 624551515407585075295255)
              ·
                refine ⟨936827273111377612942883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624551515407585075295255 936827273111377612942883)
                ·
                  refine ⟨1405240909667066419414325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936827273111377612942883 1405240909667066419414325)
                  ·
                    refine ⟨131741335281287476820093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1405240909667066419414325 131741335281287476820093)
                    ·
                      refine ⟨49403000730482803807535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131741335281287476820093 49403000730482803807535)
                      ·
                        rfl

theorem cell23_96212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_96212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96212 prefixEnd_96212 := by exact prefixLift 96212
  have htrace : WordTrace (prefixWord ++ tailWord_96212) baseStart_96212 baseEnd_96212 := by
    simpa [prefixWord, tailWord_96212, baseEnd_96212] using wordTrace_append hprefix tailTrace_96212
  have hstable : (prefixWord ++ tailWord_96212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96212).length < 2 ^ (prefixWord ++ tailWord_96212).sum := by decide
  have hdescent : baseEnd_96212 < baseStart_96212 := by decide
  rcases family_descends (prefixWord ++ tailWord_96212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96213 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_96213 : Nat := 118140960795 + 96213 * 2 ^ 59
def prefixEnd_96213 : Nat := 4983230072969 + 3 ^ 40 * 96213 * 2
def baseEnd_96213 : Nat := 49403514211137299895031

theorem tailTrace_96213 : CollatzResearch.WordTrace tailWord_96213 prefixEnd_96213 49403514211137299895031 := by
  unfold tailWord_96213
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509176400444207717301293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2339450933629471811534195 3509176400444207717301293)
  ·
    refine ⟨1315941150166577893987985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3509176400444207717301293 1315941150166577893987985)
    ·
      refine ⟨986955862624933420490989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1315941150166577893987985 986955862624933420490989)
      ·
        refine ⟨370108448484350032684121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 986955862624933420490989 370108448484350032684121)
        ·
          refine ⟨277581336363262524513091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370108448484350032684121 277581336363262524513091)
          ·
            refine ⟨416372004544893786769637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277581336363262524513091 416372004544893786769637)
            ·
              refine ⟨78069750852167585019307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416372004544893786769637 78069750852167585019307)
              ·
                refine ⟨117104626278251377528961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78069750852167585019307 117104626278251377528961)
                ·
                  refine ⟨87828469708688533146721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117104626278251377528961 87828469708688533146721)
                  ·
                    refine ⟨65871352281516399860041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87828469708688533146721 65871352281516399860041)
                    ·
                      refine ⟨49403514211137299895031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 65871352281516399860041 49403514211137299895031)
                      ·
                        rfl

theorem cell23_96213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_96213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96213 prefixEnd_96213 := by exact prefixLift 96213
  have htrace : WordTrace (prefixWord ++ tailWord_96213) baseStart_96213 baseEnd_96213 := by
    simpa [prefixWord, tailWord_96213, baseEnd_96213] using wordTrace_append hprefix tailTrace_96213
  have hstable : (prefixWord ++ tailWord_96213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96213).length < 2 ^ (prefixWord ++ tailWord_96213).sum := by decide
  have hdescent : baseEnd_96213 < baseStart_96213 := by decide
  rcases family_descends (prefixWord ++ tailWord_96213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96215 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 4, 5]
def baseStart_96215 : Nat := 118140960795 + 96215 * 2 ^ 59
def prefixEnd_96215 : Nat := 4983230072969 + 3 ^ 40 * 96215 * 2
def baseEnd_96215 : Nat := 16468180390815430690007

theorem tailTrace_96215 : CollatzResearch.WordTrace tailWord_96215 prefixEnd_96215 16468180390815430690007 := by
  unfold tailWord_96215
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509249346436962058874099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2339499564291308039249399 3509249346436962058874099)
  ·
    refine ⟨5263874019655443088311149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509249346436962058874099 5263874019655443088311149)
    ·
      refine ⟨1973952757370791158116681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5263874019655443088311149 1973952757370791158116681)
      ·
        refine ⟨1480464568028093368587511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1973952757370791158116681 1480464568028093368587511)
        ·
          refine ⟨2220696852042140052881267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480464568028093368587511 2220696852042140052881267)
          ·
            refine ⟨3331045278063210079321901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220696852042140052881267 3331045278063210079321901)
            ·
              refine ⟨1249141979273703779745713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3331045278063210079321901 1249141979273703779745713)
              ·
                refine ⟨936856484455277834809285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249141979273703779745713 936856484455277834809285)
                ·
                  refine ⟨175660590835364594026741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936856484455277834809285 175660590835364594026741)
                  ·
                    refine ⟨16468180390815430690007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175660590835364594026741 16468180390815430690007)
                    ·
                      rfl

theorem cell23_96215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_96215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96215 prefixEnd_96215 := by exact prefixLift 96215
  have htrace : WordTrace (prefixWord ++ tailWord_96215) baseStart_96215 baseEnd_96215 := by
    simpa [prefixWord, tailWord_96215, baseEnd_96215] using wordTrace_append hprefix tailTrace_96215
  have hstable : (prefixWord ++ tailWord_96215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96215).length < 2 ^ (prefixWord ++ tailWord_96215).sum := by decide
  have hdescent : baseEnd_96215 < baseStart_96215 := by decide
  rcases family_descends (prefixWord ++ tailWord_96215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96235 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4]
def baseStart_96235 : Nat := 118140960795 + 96235 * 2 ^ 59
def prefixEnd_96235 : Nat := 4983230072969 + 3 ^ 40 * 96235 * 2
def baseEnd_96235 : Nat := 49414810785536213819929

theorem tailTrace_96235 : CollatzResearch.WordTrace tailWord_96235 prefixEnd_96235 49414810785536213819929 := by
  unfold tailWord_96235
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509978806364505474602159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2339985870909670316401439 3509978806364505474602159)
  ·
    refine ⟨5264968209546758211903239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509978806364505474602159 5264968209546758211903239)
    ·
      refine ⟨7897452314320137317854859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264968209546758211903239 7897452314320137317854859)
      ·
        refine ⟨11846178471480205976782289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7897452314320137317854859 11846178471480205976782289)
        ·
          refine ⟨8884633853610154482586717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11846178471480205976782289 8884633853610154482586717)
          ·
            refine ⟨3331737695103807930970019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8884633853610154482586717 3331737695103807930970019)
            ·
              refine ⟨4997606542655711896455029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331737695103807930970019 4997606542655711896455029)
              ·
                refine ⟨468525613373972990292659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4997606542655711896455029 468525613373972990292659)
                ·
                  refine ⟨702788420060959485438989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468525613373972990292659 702788420060959485438989)
                  ·
                    refine ⟨263545657522859807039621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702788420060959485438989 263545657522859807039621)
                    ·
                      refine ⟨49414810785536213819929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 263545657522859807039621 49414810785536213819929)
                      ·
                        rfl

theorem cell23_96235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_96235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96235 prefixEnd_96235 := by exact prefixLift 96235
  have htrace : WordTrace (prefixWord ++ tailWord_96235) baseStart_96235 baseEnd_96235 := by
    simpa [prefixWord, tailWord_96235, baseEnd_96235] using wordTrace_append hprefix tailTrace_96235
  have hstable : (prefixWord ++ tailWord_96235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96235).length < 2 ^ (prefixWord ++ tailWord_96235).sum := by decide
  have hdescent : baseEnd_96235 < baseStart_96235 := by decide
  rcases family_descends (prefixWord ++ tailWord_96235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96252 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_96252 : Nat := 118140960795 + 96252 * 2 ^ 59
def prefixEnd_96252 : Nat := 4983230072969 + 3 ^ 40 * 96252 * 2
def baseEnd_96252 : Nat := 49423539956662647307351

theorem tailTrace_96252 : CollatzResearch.WordTrace tailWord_96252 prefixEnd_96252 49423539956662647307351 := by
  unfold tailWord_96252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755299423651458688985505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2340399231535278251980673 1755299423651458688985505)
  ·
    refine ⟨1316474567738594016739129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1755299423651458688985505 1316474567738594016739129)
    ·
      refine ⟨987355925803945512554347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1316474567738594016739129 987355925803945512554347)
      ·
        refine ⟨1481033888705918268831521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987355925803945512554347 1481033888705918268831521)
        ·
          refine ⟨1110775416529438701623641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481033888705918268831521 1110775416529438701623641)
          ·
            refine ⟨833081562397079026217731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110775416529438701623641 833081562397079026217731)
            ·
              refine ⟨1249622343595618539326597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833081562397079026217731 1249622343595618539326597)
              ·
                refine ⟨234304189424178476123737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1249622343595618539326597 234304189424178476123737)
                ·
                  refine ⟨175728142068133857092803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234304189424178476123737 175728142068133857092803)
                  ·
                    refine ⟨263592213102200785639205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175728142068133857092803 263592213102200785639205)
                    ·
                      refine ⟨49423539956662647307351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 263592213102200785639205 49423539956662647307351)
                      ·
                        rfl

theorem cell23_96252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_96252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96252 prefixEnd_96252 := by exact prefixLift 96252
  have htrace : WordTrace (prefixWord ++ tailWord_96252) baseStart_96252 baseEnd_96252 := by
    simpa [prefixWord, tailWord_96252, baseEnd_96252] using wordTrace_append hprefix tailTrace_96252
  have hstable : (prefixWord ++ tailWord_96252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96252).length < 2 ^ (prefixWord ++ tailWord_96252).sum := by decide
  have hdescent : baseEnd_96252 < baseStart_96252 := by decide
  rcases family_descends (prefixWord ++ tailWord_96252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96265 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_96265 : Nat := 118140960795 + 96265 * 2 ^ 59
def prefixEnd_96265 : Nat := 4983230072969 + 3 ^ 40 * 96265 * 2
def baseEnd_96265 : Nat := 49430215205171096444791

theorem tailTrace_96265 : CollatzResearch.WordTrace tailWord_96265 prefixEnd_96265 49430215205171096444791 := by
  unfold tailWord_96265
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511072996255820598194249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2340715330837213732129499 3511072996255820598194249)
  ·
    refine ⟨2633304747191865448645687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3511072996255820598194249 2633304747191865448645687)
    ·
      refine ⟨3949957120787798172968531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2633304747191865448645687 3949957120787798172968531)
      ·
        refine ⟨5924935681181697259452797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949957120787798172968531 5924935681181697259452797)
        ·
          refine ⟨2221850880443136472294799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5924935681181697259452797 2221850880443136472294799)
          ·
            refine ⟨3332776320664704708442199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221850880443136472294799 3332776320664704708442199)
            ·
              refine ⟨4999164480997057062663299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332776320664704708442199 4999164480997057062663299)
              ·
                refine ⟨7498746721495585593994949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999164480997057062663299 7498746721495585593994949)
                ·
                  refine ⟨1406015010280422298874053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7498746721495585593994949 1406015010280422298874053)
                  ·
                    refine ⟨263627814427579181038885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1406015010280422298874053 263627814427579181038885)
                    ·
                      refine ⟨49430215205171096444791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 263627814427579181038885 49430215205171096444791)
                      ·
                        rfl

theorem cell23_96265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_96265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96265 prefixEnd_96265 := by exact prefixLift 96265
  have htrace : WordTrace (prefixWord ++ tailWord_96265) baseStart_96265 baseEnd_96265 := by
    simpa [prefixWord, tailWord_96265, baseEnd_96265] using wordTrace_append hprefix tailTrace_96265
  have hstable : (prefixWord ++ tailWord_96265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96265).length < 2 ^ (prefixWord ++ tailWord_96265).sum := by decide
  have hdescent : baseEnd_96265 < baseStart_96265 := by decide
  rcases family_descends (prefixWord ++ tailWord_96265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96289 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_96289 : Nat := 118140960795 + 96289 * 2 ^ 59
def prefixEnd_96289 : Nat := 4983230072969 + 3 ^ 40 * 96289 * 2
def baseEnd_96289 : Nat := 49442538740879002544681

theorem tailTrace_96289 : CollatzResearch.WordTrace tailWord_96289 prefixEnd_96289 49442538740879002544681 := by
  unfold tailWord_96289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511948348168872697067921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2341298898779248464711947 3511948348168872697067921)
  ·
    refine ⟨2633961261126654522800941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3511948348168872697067921 2633961261126654522800941)
    ·
      refine ⟨987735472922495446050353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2633961261126654522800941 987735472922495446050353)
      ·
        refine ⟨740801604691871584537765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 987735472922495446050353 740801604691871584537765)
        ·
          refine ⟨138900300879725922100831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 740801604691871584537765 138900300879725922100831)
          ·
            refine ⟨208350451319588883151247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138900300879725922100831 208350451319588883151247)
            ·
              refine ⟨312525676979383324726871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208350451319588883151247 312525676979383324726871)
              ·
                refine ⟨468788515469074987090307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312525676979383324726871 468788515469074987090307)
                ·
                  refine ⟨703182773203612480635461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468788515469074987090307 703182773203612480635461)
                  ·
                    refine ⟨131846769975677340119149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 703182773203612480635461 131846769975677340119149)
                    ·
                      refine ⟨49442538740879002544681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131846769975677340119149 49442538740879002544681)
                      ·
                        rfl

theorem cell23_96289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_96289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96289 prefixEnd_96289 := by exact prefixLift 96289
  have htrace : WordTrace (prefixWord ++ tailWord_96289) baseStart_96289 baseEnd_96289 := by
    simpa [prefixWord, tailWord_96289, baseEnd_96289] using wordTrace_append hprefix tailTrace_96289
  have hstable : (prefixWord ++ tailWord_96289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96289).length < 2 ^ (prefixWord ++ tailWord_96289).sum := by decide
  have hdescent : baseEnd_96289 < baseStart_96289 := by decide
  rcases family_descends (prefixWord ++ tailWord_96289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96315 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_96315 : Nat := 118140960795 + 96315 * 2 ^ 59
def prefixEnd_96315 : Nat := 4983230072969 + 3 ^ 40 * 96315 * 2
def baseEnd_96315 : Nat := 49455889237895900819561

theorem tailTrace_96315 : CollatzResearch.WordTrace tailWord_96315 prefixEnd_96315 49455889237895900819561 := by
  unfold tailWord_96315
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512896646074679137514399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2341931097383119425009599 3512896646074679137514399)
  ·
    refine ⟨5269344969112018706271599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512896646074679137514399 5269344969112018706271599)
    ·
      refine ⟨7904017453668028059407399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5269344969112018706271599 7904017453668028059407399)
      ·
        refine ⟨11856026180502042089111099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7904017453668028059407399 11856026180502042089111099)
        ·
          refine ⟨17784039270753063133666649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11856026180502042089111099 17784039270753063133666649)
          ·
            refine ⟨13338029453064797350249987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17784039270753063133666649 13338029453064797350249987)
            ·
              refine ⟨20007044179597196025374981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13338029453064797350249987 20007044179597196025374981)
              ·
                refine ⟨3751320783674474254757809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20007044179597196025374981 3751320783674474254757809)
                ·
                  refine ⟨2813490587755855691068357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3751320783674474254757809 2813490587755855691068357)
                  ·
                    refine ⟨527529485204222942075317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813490587755855691068357 527529485204222942075317)
                    ·
                      refine ⟨49455889237895900819561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 527529485204222942075317 49455889237895900819561)
                      ·
                        rfl

theorem cell23_96315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_96315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96315 prefixEnd_96315 := by exact prefixLift 96315
  have htrace : WordTrace (prefixWord ++ tailWord_96315) baseStart_96315 baseEnd_96315 := by
    simpa [prefixWord, tailWord_96315, baseEnd_96315] using wordTrace_append hprefix tailTrace_96315
  have hstable : (prefixWord ++ tailWord_96315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96315).length < 2 ^ (prefixWord ++ tailWord_96315).sum := by decide
  have hdescent : baseEnd_96315 < baseStart_96315 := by decide
  rcases family_descends (prefixWord ++ tailWord_96315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96319 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 3]
def baseStart_96319 : Nat := 118140960795 + 96319 * 2 ^ 59
def prefixEnd_96319 : Nat := 4983230072969 + 3 ^ 40 * 96319 * 2
def baseEnd_96319 : Nat := 49457943160513885169543

theorem tailTrace_96319 : CollatzResearch.WordTrace tailWord_96319 prefixEnd_96319 49457943160513885169543 := by
  unfold tailWord_96319
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513042538060187820660011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2342028358706791880440007 3513042538060187820660011)
  ·
    refine ⟨5269563807090281730990017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3513042538060187820660011 5269563807090281730990017)
    ·
      refine ⟨3952172855317711298242513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5269563807090281730990017 3952172855317711298242513)
      ·
        refine ⟨2964129641488283473681885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3952172855317711298242513 2964129641488283473681885)
        ·
          refine ⟨1111548615558106302630707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2964129641488283473681885 1111548615558106302630707)
          ·
            refine ⟨1667322923337159453946061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111548615558106302630707 1667322923337159453946061)
            ·
              refine ⟨625246096251434795229773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1667322923337159453946061 625246096251434795229773)
              ·
                refine ⟨234467286094288048211165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 625246096251434795229773 234467286094288048211165)
                ·
                  refine ⟨87925232285358018079187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234467286094288048211165 87925232285358018079187)
                  ·
                    refine ⟨131887848428037027118781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87925232285358018079187 131887848428037027118781)
                    ·
                      refine ⟨49457943160513885169543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131887848428037027118781 49457943160513885169543)
                      ·
                        rfl

theorem cell23_96319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_96319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96319 prefixEnd_96319 := by exact prefixLift 96319
  have htrace : WordTrace (prefixWord ++ tailWord_96319) baseStart_96319 baseEnd_96319 := by
    simpa [prefixWord, tailWord_96319, baseEnd_96319] using wordTrace_append hprefix tailTrace_96319
  have hstable : (prefixWord ++ tailWord_96319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96319).length < 2 ^ (prefixWord ++ tailWord_96319).sum := by decide
  have hdescent : baseEnd_96319 < baseStart_96319 := by decide
  rcases family_descends (prefixWord ++ tailWord_96319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96359 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_96359 : Nat := 118140960795 + 96359 * 2 ^ 59
def prefixEnd_96359 : Nat := 4983230072969 + 3 ^ 40 * 96359 * 2
def baseEnd_96359 : Nat := 49478482386693728669359

theorem tailTrace_96359 : CollatzResearch.WordTrace tailWord_96359 prefixEnd_96359 49478482386693728669359 := by
  unfold tailWord_96359
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514501457915274652116131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2343000971943516434744087 3514501457915274652116131)
  ·
    refine ⟨5271752186872911978174197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514501457915274652116131 5271752186872911978174197)
    ·
      refine ⟨494226767519335497953831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5271752186872911978174197 494226767519335497953831)
      ·
        refine ⟨741340151279003246930747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494226767519335497953831 741340151279003246930747)
        ·
          refine ⟨1112010226918504870396121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741340151279003246930747 1112010226918504870396121)
          ·
            refine ⟨834007670188878652797091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112010226918504870396121 834007670188878652797091)
            ·
              refine ⟨1251011505283317979195637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834007670188878652797091 1251011505283317979195637)
              ·
                refine ⟨117282328620311060549591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1251011505283317979195637 117282328620311060549591)
                ·
                  refine ⟨175923492930466590824387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117282328620311060549591 175923492930466590824387)
                  ·
                    refine ⟨263885239395699886236581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175923492930466590824387 263885239395699886236581)
                    ·
                      refine ⟨49478482386693728669359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 263885239395699886236581 49478482386693728669359)
                      ·
                        rfl

theorem cell23_96359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_96359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96359 prefixEnd_96359 := by exact prefixLift 96359
  have htrace : WordTrace (prefixWord ++ tailWord_96359) baseStart_96359 baseEnd_96359 := by
    simpa [prefixWord, tailWord_96359, baseEnd_96359] using wordTrace_append hprefix tailTrace_96359
  have hstable : (prefixWord ++ tailWord_96359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96359).length < 2 ^ (prefixWord ++ tailWord_96359).sum := by decide
  have hdescent : baseEnd_96359 < baseStart_96359 := by decide
  rcases family_descends (prefixWord ++ tailWord_96359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96369 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 2, 4]
def baseStart_96369 : Nat := 118140960795 + 96369 * 2 ^ 59
def prefixEnd_96369 : Nat := 4983230072969 + 3 ^ 40 * 96369 * 2
def baseEnd_96369 : Nat := 16494539064412896514771

theorem tailTrace_96369 : CollatzResearch.WordTrace tailWord_96369 prefixEnd_96369 16494539064412896514771 := by
  unfold tailWord_96369
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514866187879046359980161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2343244125252697573320107 3514866187879046359980161)
  ·
    refine ⟨2636149640909284769985121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3514866187879046359980161 2636149640909284769985121)
    ·
      refine ⟨1977112230681963577488841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2636149640909284769985121 1977112230681963577488841)
      ·
        refine ⟨1482834173011472683116631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1977112230681963577488841 1482834173011472683116631)
        ·
          refine ⟨2224251259517209024674947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482834173011472683116631 2224251259517209024674947)
          ·
            refine ⟨3336376889275813537012421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224251259517209024674947 3336376889275813537012421)
            ·
              refine ⟨625570666739215038189829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3336376889275813537012421 625570666739215038189829)
              ·
                refine ⟨117294500013602819660593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 625570666739215038189829 117294500013602819660593)
                ·
                  refine ⟨87970875010202114745445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117294500013602819660593 87970875010202114745445)
                  ·
                    refine ⟨16494539064412896514771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87970875010202114745445 16494539064412896514771)
                    ·
                      rfl

theorem cell23_96369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_96369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96369 prefixEnd_96369 := by exact prefixLift 96369
  have htrace : WordTrace (prefixWord ++ tailWord_96369) baseStart_96369 baseEnd_96369 := by
    simpa [prefixWord, tailWord_96369, baseEnd_96369] using wordTrace_append hprefix tailTrace_96369
  have hstable : (prefixWord ++ tailWord_96369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96369).length < 2 ^ (prefixWord ++ tailWord_96369).sum := by decide
  have hdescent : baseEnd_96369 < baseStart_96369 := by decide
  rcases family_descends (prefixWord ++ tailWord_96369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96370 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_96370 : Nat := 118140960795 + 96370 * 2 ^ 59
def prefixEnd_96370 : Nat := 4983230072969 + 3 ^ 40 * 96370 * 2
def baseEnd_96370 : Nat := 49484130673893185631809

theorem tailTrace_96370 : CollatzResearch.WordTrace tailWord_96370 prefixEnd_96370 49484130673893185631809 := by
  unfold tailWord_96370
  simp only [CollatzResearch.WordTrace]
  refine ⟨878725665218855882691641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2343268440583615687177709 878725665218855882691641)
  ·
    refine ⟨659044248914141912018731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 878725665218855882691641 659044248914141912018731)
    ·
      refine ⟨988566373371212868028097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659044248914141912018731 988566373371212868028097)
      ·
        refine ⟨741424780028409651021073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 988566373371212868028097 741424780028409651021073)
        ·
          refine ⟨556068585021307238265805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741424780028409651021073 556068585021307238265805)
          ·
            refine ⟨208525719382990214349677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556068585021307238265805 208525719382990214349677)
            ·
              refine ⟨78197144768621330381129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208525719382990214349677 78197144768621330381129)
              ·
                refine ⟨58647858576465997785847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78197144768621330381129 58647858576465997785847)
                ·
                  refine ⟨87971787864698996678771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58647858576465997785847 87971787864698996678771)
                  ·
                    refine ⟨131957681797048495018157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87971787864698996678771 131957681797048495018157)
                    ·
                      refine ⟨49484130673893185631809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 131957681797048495018157 49484130673893185631809)
                      ·
                        rfl

theorem cell23_96370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_96370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96370 prefixEnd_96370 := by exact prefixLift 96370
  have htrace : WordTrace (prefixWord ++ tailWord_96370) baseStart_96370 baseEnd_96370 := by
    simpa [prefixWord, tailWord_96370, baseEnd_96370] using wordTrace_append hprefix tailTrace_96370
  have hstable : (prefixWord ++ tailWord_96370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96370).length < 2 ^ (prefixWord ++ tailWord_96370).sum := by decide
  have hdescent : baseEnd_96370 < baseStart_96370 := by decide
  rcases family_descends (prefixWord ++ tailWord_96370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96409 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 3]
def baseStart_96409 : Nat := 118140960795 + 96409 * 2 ^ 59
def prefixEnd_96409 : Nat := 4983230072969 + 3 ^ 40 * 96409 * 2
def baseEnd_96409 : Nat := 49504156419418533044129

theorem tailTrace_96409 : CollatzResearch.WordTrace tailWord_96409 prefixEnd_96409 49504156419418533044129 := by
  unfold tailWord_96409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516325107734133191436281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2344216738489422127624187 3516325107734133191436281)
  ·
    refine ⟨2637243830800599893577211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3516325107734133191436281 2637243830800599893577211)
    ·
      refine ⟨3955865746200899840365817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637243830800599893577211 3955865746200899840365817)
      ·
        refine ⟨2966899309650674880274363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3955865746200899840365817 2966899309650674880274363)
        ·
          refine ⟨4450348964476012320411545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966899309650674880274363 4450348964476012320411545)
          ·
            refine ⟨3337761723357009240308659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450348964476012320411545 3337761723357009240308659)
            ·
              refine ⟨5006642585035513860462989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337761723357009240308659 5006642585035513860462989)
              ·
                refine ⟨1877490969388317697673621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5006642585035513860462989 1877490969388317697673621)
                ·
                  refine ⟨88007389190077392078451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1877490969388317697673621 88007389190077392078451)
                  ·
                    refine ⟨132011083785116088117677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88007389190077392078451 132011083785116088117677)
                    ·
                      refine ⟨49504156419418533044129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132011083785116088117677 49504156419418533044129)
                      ·
                        rfl

theorem cell23_96409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_96409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96409 prefixEnd_96409 := by exact prefixLift 96409
  have htrace : WordTrace (prefixWord ++ tailWord_96409) baseStart_96409 baseEnd_96409 := by
    simpa [prefixWord, tailWord_96409, baseEnd_96409] using wordTrace_append hprefix tailTrace_96409
  have hstable : (prefixWord ++ tailWord_96409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96409).length < 2 ^ (prefixWord ++ tailWord_96409).sum := by decide
  have hdescent : baseEnd_96409 < baseStart_96409 := by decide
  rcases family_descends (prefixWord ++ tailWord_96409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96413 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_96413 : Nat := 118140960795 + 96413 * 2 ^ 59
def prefixEnd_96413 : Nat := 4983230072969 + 3 ^ 40 * 96413 * 2
def baseEnd_96413 : Nat := 49506210342036517394111

theorem tailTrace_96413 : CollatzResearch.WordTrace tailWord_96413 prefixEnd_96413 49506210342036517394111 := by
  unfold tailWord_96413
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516470999719641874581893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2344313999813094583054595 3516470999719641874581893)
  ·
    refine ⟨659338312447432851484105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3516470999719641874581893 659338312447432851484105)
    ·
      refine ⟨494503734335574638613079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 659338312447432851484105 494503734335574638613079)
      ·
        refine ⟨741755601503361957919619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494503734335574638613079 741755601503361957919619)
        ·
          refine ⟨1112633402255042936879429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741755601503361957919619 1112633402255042936879429)
          ·
            refine ⟨208618762922820550664893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1112633402255042936879429 208618762922820550664893)
            ·
              refine ⟨78232036096057706499335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208618762922820550664893 78232036096057706499335)
              ·
                refine ⟨117348054144086559749003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78232036096057706499335 117348054144086559749003)
                ·
                  refine ⟨176022081216129839623505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117348054144086559749003 176022081216129839623505)
                  ·
                    refine ⟨132016560912097379717629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176022081216129839623505 132016560912097379717629)
                    ·
                      refine ⟨49506210342036517394111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132016560912097379717629 49506210342036517394111)
                      ·
                        rfl

theorem cell23_96413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_96413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96413 prefixEnd_96413 := by exact prefixLift 96413
  have htrace : WordTrace (prefixWord ++ tailWord_96413) baseStart_96413 baseEnd_96413 := by
    simpa [prefixWord, tailWord_96413, baseEnd_96413] using wordTrace_append hprefix tailTrace_96413
  have hstable : (prefixWord ++ tailWord_96413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96413).length < 2 ^ (prefixWord ++ tailWord_96413).sum := by decide
  have hdescent : baseEnd_96413 < baseStart_96413 := by decide
  rcases family_descends (prefixWord ++ tailWord_96413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96429 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_96429 : Nat := 118140960795 + 96429 * 2 ^ 59
def prefixEnd_96429 : Nat := 4983230072969 + 3 ^ 40 * 96429 * 2
def baseEnd_96429 : Nat := 16504808677502818264679

theorem tailTrace_96429 : CollatzResearch.WordTrace tailWord_96429 prefixEnd_96429 16504808677502818264679 := by
  unfold tailWord_96429
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517054567661676607164341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2344703045107784404776227 3517054567661676607164341)
  ·
    refine ⟨329723865718282181921657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3517054567661676607164341 329723865718282181921657)
    ·
      refine ⟨247292899288711636441243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329723865718282181921657 247292899288711636441243)
      ·
        refine ⟨370939348933067454661865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247292899288711636441243 370939348933067454661865)
        ·
          refine ⟨278204511699800590996399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370939348933067454661865 278204511699800590996399)
          ·
            refine ⟨417306767549700886494599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278204511699800590996399 417306767549700886494599)
            ·
              refine ⟨625960151324551329741899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417306767549700886494599 625960151324551329741899)
              ·
                refine ⟨938940226986826994612849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625960151324551329741899 938940226986826994612849)
                ·
                  refine ⟨704205170240120245959637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 938940226986826994612849 704205170240120245959637)
                  ·
                    refine ⟨16504808677502818264679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 704205170240120245959637 16504808677502818264679)
                    ·
                      rfl

theorem cell23_96429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_96429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96429 prefixEnd_96429 := by exact prefixLift 96429
  have htrace : WordTrace (prefixWord ++ tailWord_96429) baseStart_96429 baseEnd_96429 := by
    simpa [prefixWord, tailWord_96429, baseEnd_96429] using wordTrace_append hprefix tailTrace_96429
  have hstable : (prefixWord ++ tailWord_96429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96429).length < 2 ^ (prefixWord ++ tailWord_96429).sum := by decide
  have hdescent : baseEnd_96429 < baseStart_96429 := by decide
  rcases family_descends (prefixWord ++ tailWord_96429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96442 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_96442 : Nat := 118140960795 + 96442 * 2 ^ 59
def prefixEnd_96442 : Nat := 4983230072969 + 3 ^ 40 * 96442 * 2
def baseEnd_96442 : Nat := 16507033760338967977159

theorem tailTrace_96442 : CollatzResearch.WordTrace tailWord_96442 prefixEnd_96442 16507033760338967977159 := by
  unfold tailWord_96442
  simp only [CollatzResearch.WordTrace]
  refine ⟨879382179153644956846895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2345019144409719884925053 879382179153644956846895)
  ·
    refine ⟨1319073268730467435270343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879382179153644956846895 1319073268730467435270343)
    ·
      refine ⟨1978609903095701152905515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319073268730467435270343 1978609903095701152905515)
      ·
        refine ⟨2967914854643551729358273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978609903095701152905515 2967914854643551729358273)
        ·
          refine ⟨2225936140982663797018705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2967914854643551729358273 2225936140982663797018705)
          ·
            refine ⟨1669452105736997847764029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2225936140982663797018705 1669452105736997847764029)
            ·
              refine ⟨626044539651374192911511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669452105736997847764029 626044539651374192911511)
              ·
                refine ⟨939066809477061289367267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626044539651374192911511 939066809477061289367267)
                ·
                  refine ⟨1408600214215591934050901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939066809477061289367267 1408600214215591934050901)
                  ·
                    refine ⟨16507033760338967977159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1408600214215591934050901 16507033760338967977159)
                    ·
                      rfl

theorem cell23_96442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_96442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96442 prefixEnd_96442 := by exact prefixLift 96442
  have htrace : WordTrace (prefixWord ++ tailWord_96442) baseStart_96442 baseEnd_96442 := by
    simpa [prefixWord, tailWord_96442, baseEnd_96442] using wordTrace_append hprefix tailTrace_96442
  have hstable : (prefixWord ++ tailWord_96442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96442).length < 2 ^ (prefixWord ++ tailWord_96442).sum := by decide
  have hdescent : baseEnd_96442 < baseStart_96442 := by decide
  rcases family_descends (prefixWord ++ tailWord_96442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96499 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 3]
def baseStart_96499 : Nat := 118140960795 + 96499 * 2 ^ 59
def prefixEnd_96499 : Nat := 4983230072969 + 3 ^ 40 * 96499 * 2
def baseEnd_96499 : Nat := 49550369678323180918715

theorem tailTrace_96499 : CollatzResearch.WordTrace tailWord_96499 prefixEnd_96499 49550369678323180918715 := by
  unfold tailWord_96499
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519607677408078562212551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2346405118272052374808367 3519607677408078562212551)
  ·
    refine ⟨5279411516112117843318827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519607677408078562212551 5279411516112117843318827)
    ·
      refine ⟨7919117274168176764978241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279411516112117843318827 7919117274168176764978241)
      ·
        refine ⟨5939337955626132573733681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7919117274168176764978241 5939337955626132573733681)
        ·
          refine ⟨4454503466719599430300261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5939337955626132573733681 4454503466719599430300261)
          ·
            refine ⟨835219400009924893181299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4454503466719599430300261 835219400009924893181299)
            ·
              refine ⟨1252829100014887339771949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835219400009924893181299 1252829100014887339771949)
              ·
                refine ⟨469810912505582752414481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252829100014887339771949 469810912505582752414481)
                ·
                  refine ⟨352358184379187064310861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469810912505582752414481 352358184379187064310861)
                  ·
                    refine ⟨132134319142195149116573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352358184379187064310861 132134319142195149116573)
                    ·
                      refine ⟨49550369678323180918715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132134319142195149116573 49550369678323180918715)
                      ·
                        rfl

theorem cell23_96499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_96499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96499 prefixEnd_96499 := by exact prefixLift 96499
  have htrace : WordTrace (prefixWord ++ tailWord_96499) baseStart_96499 baseEnd_96499 := by
    simpa [prefixWord, tailWord_96499, baseEnd_96499] using wordTrace_append hprefix tailTrace_96499
  have hstable : (prefixWord ++ tailWord_96499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96499).length < 2 ^ (prefixWord ++ tailWord_96499).sum := by decide
  have hdescent : baseEnd_96499 < baseStart_96499 := by decide
  rcases family_descends (prefixWord ++ tailWord_96499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96539 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 4]
def baseStart_96539 : Nat := 118140960795 + 96539 * 2 ^ 59
def prefixEnd_96539 : Nat := 4983230072969 + 3 ^ 40 * 96539 * 2
def baseEnd_96539 : Nat := 49570908904503024418531

theorem tailTrace_96539 : CollatzResearch.WordTrace tailWord_96539 prefixEnd_96539 49570908904503024418531 := by
  unfold tailWord_96539
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521066597263165393668671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2347377731508776929112447 3521066597263165393668671)
  ·
    refine ⟨5281599895894748090503007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521066597263165393668671 5281599895894748090503007)
    ·
      refine ⟨7922399843842122135754511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5281599895894748090503007 7922399843842122135754511)
      ·
        refine ⟨11883599765763183203631767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7922399843842122135754511 11883599765763183203631767)
        ·
          refine ⟨17825399648644774805447651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11883599765763183203631767 17825399648644774805447651)
          ·
            refine ⟨26738099472967162208171477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17825399648644774805447651 26738099472967162208171477)
            ·
              refine ⟨626674206397667864254019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26738099472967162208171477 626674206397667864254019)
              ·
                refine ⟨940011309596501796381029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626674206397667864254019 940011309596501796381029)
                ·
                  refine ⟨176252120549344086821443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940011309596501796381029 176252120549344086821443)
                  ·
                    refine ⟨264378180824016130232165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176252120549344086821443 264378180824016130232165)
                    ·
                      refine ⟨49570908904503024418531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 264378180824016130232165 49570908904503024418531)
                      ·
                        rfl

theorem cell23_96539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 4].length) (baseStart_96539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96539 prefixEnd_96539 := by exact prefixLift 96539
  have htrace : WordTrace (prefixWord ++ tailWord_96539) baseStart_96539 baseEnd_96539 := by
    simpa [prefixWord, tailWord_96539, baseEnd_96539] using wordTrace_append hprefix tailTrace_96539
  have hstable : (prefixWord ++ tailWord_96539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96539).length < 2 ^ (prefixWord ++ tailWord_96539).sum := by decide
  have hdescent : baseEnd_96539 < baseStart_96539 := by decide
  rcases family_descends (prefixWord ++ tailWord_96539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96546 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_96546 : Nat := 118140960795 + 96546 * 2 ^ 59
def prefixEnd_96546 : Nat := 4983230072969 + 3 ^ 40 * 96546 * 2
def baseEnd_96546 : Nat := 49574503269084497030999

theorem tailTrace_96546 : CollatzResearch.WordTrace tailWord_96546 prefixEnd_96546 49574503269084497030999 := by
  unfold tailWord_96546
  simp only [CollatzResearch.WordTrace]
  refine ⟨880330477059451397293373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2347547938825203726115661 880330477059451397293373)
  ·
    refine ⟨330123928897294273985015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 880330477059451397293373 330123928897294273985015)
    ·
      refine ⟨495185893345941410977523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330123928897294273985015 495185893345941410977523)
      ·
        refine ⟨742778840018912116466285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495185893345941410977523 742778840018912116466285)
        ·
          refine ⟨278542065007092043674857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742778840018912116466285 278542065007092043674857)
          ·
            refine ⟨208906548755319032756143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278542065007092043674857 208906548755319032756143)
            ·
              refine ⟨313359823132978549134215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208906548755319032756143 313359823132978549134215)
              ·
                refine ⟨470039734699467823701323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313359823132978549134215 470039734699467823701323)
                ·
                  refine ⟨705059602049201735551985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470039734699467823701323 705059602049201735551985)
                  ·
                    refine ⟨528794701536901301663989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705059602049201735551985 528794701536901301663989)
                    ·
                      refine ⟨49574503269084497030999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 528794701536901301663989 49574503269084497030999)
                      ·
                        rfl

theorem cell23_96546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_96546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96546 prefixEnd_96546 := by exact prefixLift 96546
  have htrace : WordTrace (prefixWord ++ tailWord_96546) baseStart_96546 baseEnd_96546 := by
    simpa [prefixWord, tailWord_96546, baseEnd_96546] using wordTrace_append hprefix tailTrace_96546
  have hstable : (prefixWord ++ tailWord_96546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96546).length < 2 ^ (prefixWord ++ tailWord_96546).sum := by decide
  have hdescent : baseEnd_96546 < baseStart_96546 := by decide
  rcases family_descends (prefixWord ++ tailWord_96546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96556 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 2, 4, 2]
def baseStart_96556 : Nat := 118140960795 + 96556 * 2 ^ 59
def prefixEnd_96556 : Nat := 4983230072969 + 3 ^ 40 * 96556 * 2
def baseEnd_96556 : Nat := 49579638075629457905953

theorem tailTrace_96556 : CollatzResearch.WordTrace tailWord_96556 prefixEnd_96556 49579638075629457905953 := by
  unfold tailWord_96556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760843319100788648518761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2347791092134384864691681 1760843319100788648518761)
  ·
    refine ⟨1320632489325591486389071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1760843319100788648518761 1320632489325591486389071)
    ·
      refine ⟨1980948733988387229583607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320632489325591486389071 1980948733988387229583607)
      ·
        refine ⟨2971423100982580844375411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980948733988387229583607 2971423100982580844375411)
        ·
          refine ⟨4457134651473871266563117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971423100982580844375411 4457134651473871266563117)
          ·
            refine ⟨1671425494302701724961169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4457134651473871266563117 1671425494302701724961169)
            ·
              refine ⟨1253569120727026293720877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671425494302701724961169 1253569120727026293720877)
              ·
                refine ⟨470088420272634860145329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1253569120727026293720877 470088420272634860145329)
                ·
                  refine ⟨352566315204476145108997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470088420272634860145329 352566315204476145108997)
                  ·
                    refine ⟨66106184100839277207937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 352566315204476145108997 66106184100839277207937)
                    ·
                      refine ⟨49579638075629457905953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66106184100839277207937 49579638075629457905953)
                      ·
                        rfl

theorem cell23_96556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_96556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96556 prefixEnd_96556 := by exact prefixLift 96556
  have htrace : WordTrace (prefixWord ++ tailWord_96556) baseStart_96556 baseEnd_96556 := by
    simpa [prefixWord, tailWord_96556, baseEnd_96556] using wordTrace_append hprefix tailTrace_96556
  have hstable : (prefixWord ++ tailWord_96556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96556).length < 2 ^ (prefixWord ++ tailWord_96556).sum := by decide
  have hdescent : baseEnd_96556 < baseStart_96556 := by decide
  rcases family_descends (prefixWord ++ tailWord_96556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96559 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_96559 : Nat := 118140960795 + 96559 * 2 ^ 59
def prefixEnd_96559 : Nat := 4983230072969 + 3 ^ 40 * 96559 * 2
def baseEnd_96559 : Nat := 49581178517592946168439

theorem tailTrace_96559 : CollatzResearch.WordTrace tailWord_96559 prefixEnd_96559 49581178517592946168439 := by
  unfold tailWord_96559
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521796057190708809396731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2347864038127139206264487 3521796057190708809396731)
  ·
    refine ⟨5282694085786063214095097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521796057190708809396731 5282694085786063214095097)
    ·
      refine ⟨3962020564339547410571323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5282694085786063214095097 3962020564339547410571323)
      ·
        refine ⟨5943030846509321115856985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962020564339547410571323 5943030846509321115856985)
        ·
          refine ⟨4457273134881990836892739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943030846509321115856985 4457273134881990836892739)
          ·
            refine ⟨6685909702322986255339109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457273134881990836892739 6685909702322986255339109)
            ·
              refine ⟨1253608069185559922876083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6685909702322986255339109 1253608069185559922876083)
              ·
                refine ⟨1880412103778339884314125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253608069185559922876083 1880412103778339884314125)
                ·
                  refine ⟨705154538916877456617797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1880412103778339884314125 705154538916877456617797)
                  ·
                    refine ⟨132216476046914523115837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705154538916877456617797 132216476046914523115837)
                    ·
                      refine ⟨49581178517592946168439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132216476046914523115837 49581178517592946168439)
                      ·
                        rfl

theorem cell23_96559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_96559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96559 prefixEnd_96559 := by exact prefixLift 96559
  have htrace : WordTrace (prefixWord ++ tailWord_96559) baseStart_96559 baseEnd_96559 := by
    simpa [prefixWord, tailWord_96559, baseEnd_96559] using wordTrace_append hprefix tailTrace_96559
  have hstable : (prefixWord ++ tailWord_96559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96559).length < 2 ^ (prefixWord ++ tailWord_96559).sum := by decide
  have hdescent : baseEnd_96559 < baseStart_96559 := by decide
  rcases family_descends (prefixWord ++ tailWord_96559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96583 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 1, 4]
def baseStart_96583 : Nat := 118140960795 + 96583 * 2 ^ 59
def prefixEnd_96583 : Nat := 4983230072969 + 3 ^ 40 * 96583 * 2
def baseEnd_96583 : Nat := 16531167351100284089443

theorem tailTrace_96583 : CollatzResearch.WordTrace tailWord_96583 prefixEnd_96583 16531167351100284089443 := by
  unfold tailWord_96583
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522671409103760908270403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2348447606069173938846935 3522671409103760908270403)
  ·
    refine ⟨5284007113655641362405605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3522671409103760908270403 5284007113655641362405605)
    ·
      refine ⟨990751333810432755451051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5284007113655641362405605 990751333810432755451051)
      ·
        refine ⟨1486127000715649133176577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990751333810432755451051 1486127000715649133176577)
        ·
          refine ⟨1114595250536736849882433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1486127000715649133176577 1114595250536736849882433)
          ·
            refine ⟨835946437902552637411825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114595250536736849882433 835946437902552637411825)
            ·
              refine ⟨626959828426914478058869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835946437902552637411825 626959828426914478058869)
              ·
                refine ⟨58777483915023232318019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626959828426914478058869 58777483915023232318019)
                ·
                  refine ⟨88166225872534848477029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58777483915023232318019 88166225872534848477029)
                  ·
                    refine ⟨16531167351100284089443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88166225872534848477029 16531167351100284089443)
                    ·
                      rfl

theorem cell23_96583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_96583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96583 prefixEnd_96583 := by exact prefixLift 96583
  have htrace : WordTrace (prefixWord ++ tailWord_96583) baseStart_96583 baseEnd_96583 := by
    simpa [prefixWord, tailWord_96583, baseEnd_96583] using wordTrace_append hprefix tailTrace_96583
  have hstable : (prefixWord ++ tailWord_96583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96583).length < 2 ^ (prefixWord ++ tailWord_96583).sum := by decide
  have hdescent : baseEnd_96583 < baseStart_96583 := by decide
  rcases family_descends (prefixWord ++ tailWord_96583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96596 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 6]
def baseStart_96596 : Nat := 118140960795 + 96596 * 2 ^ 59
def prefixEnd_96596 : Nat := 4983230072969 + 3 ^ 40 * 96596 * 2
def baseEnd_96596 : Nat := 5511130811312144600641

theorem tailTrace_96596 : CollatzResearch.WordTrace tailWord_96596 prefixEnd_96596 5511130811312144600641 := by
  unfold tailWord_96596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761572779028332064246821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2348763705371109418995761 1761572779028332064246821)
  ·
    refine ⟨330294896067812262046279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1761572779028332064246821 330294896067812262046279)
    ·
      refine ⟨495442344101718393069419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330294896067812262046279 495442344101718393069419)
      ·
        refine ⟨743163516152577589604129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495442344101718393069419 743163516152577589604129)
        ·
          refine ⟨557372637114433192203097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743163516152577589604129 557372637114433192203097)
          ·
            refine ⟨418029477835824894152323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557372637114433192203097 418029477835824894152323)
            ·
              refine ⟨627044216753737341228485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418029477835824894152323 627044216753737341228485)
              ·
                refine ⟨117570790641325751480341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627044216753737341228485 117570790641325751480341)
                ·
                  refine ⟨5511130811312144600641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117570790641325751480341 5511130811312144600641)
                  ·
                    rfl

theorem cell23_96596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_96596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96596 prefixEnd_96596 := by exact prefixLift 96596
  have htrace : WordTrace (prefixWord ++ tailWord_96596) baseStart_96596 baseEnd_96596 := by
    simpa [prefixWord, tailWord_96596, baseEnd_96596] using wordTrace_append hprefix tailTrace_96596
  have hstable : (prefixWord ++ tailWord_96596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96596).length < 2 ^ (prefixWord ++ tailWord_96596).sum := by decide
  have hdescent : baseEnd_96596 < baseStart_96596 := by decide
  rcases family_descends (prefixWord ++ tailWord_96596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96599 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_96599 : Nat := 118140960795 + 96599 * 2 ^ 59
def prefixEnd_96599 : Nat := 4983230072969 + 3 ^ 40 * 96599 * 2
def baseEnd_96599 : Nat := 49601717743772789668255

theorem tailTrace_96599 : CollatzResearch.WordTrace tailWord_96599 prefixEnd_96599 49601717743772789668255 := by
  unfold tailWord_96599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523254977045795640852851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2348836651363863760568567 3523254977045795640852851)
  ·
    refine ⟨5284882465568693461279277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3523254977045795640852851 5284882465568693461279277)
    ·
      refine ⟨1981830924588260047979729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5284882465568693461279277 1981830924588260047979729)
      ·
        refine ⟨1486373193441195035984797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1981830924588260047979729 1486373193441195035984797)
        ·
          refine ⟨557389947540448138494299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1486373193441195035984797 557389947540448138494299)
          ·
            refine ⟨836084921310672207741449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557389947540448138494299 836084921310672207741449)
            ·
              refine ⟨627063690983004155806087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836084921310672207741449 627063690983004155806087)
              ·
                refine ⟨940595536474506233709131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627063690983004155806087 940595536474506233709131)
                ·
                  refine ⟨1410893304711759350563697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940595536474506233709131 1410893304711759350563697)
                  ·
                    refine ⟨1058169978533819512922773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1410893304711759350563697 1058169978533819512922773)
                    ·
                      refine ⟨49601717743772789668255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1058169978533819512922773 49601717743772789668255)
                      ·
                        rfl

theorem cell23_96599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_96599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96599 prefixEnd_96599 := by exact prefixLift 96599
  have htrace : WordTrace (prefixWord ++ tailWord_96599) baseStart_96599 baseEnd_96599 := by
    simpa [prefixWord, tailWord_96599, baseEnd_96599] using wordTrace_append hprefix tailTrace_96599
  have hstable : (prefixWord ++ tailWord_96599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96599).length < 2 ^ (prefixWord ++ tailWord_96599).sum := by decide
  have hdescent : baseEnd_96599 < baseStart_96599 := by decide
  rcases family_descends (prefixWord ++ tailWord_96599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96626 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_96626 : Nat := 118140960795 + 96626 * 2 ^ 59
def prefixEnd_96626 : Nat := 4983230072969 + 3 ^ 40 * 96626 * 2
def baseEnd_96626 : Nat := 16538527240481394676877

theorem tailTrace_96626 : CollatzResearch.WordTrace tailWord_96626 prefixEnd_96626 16538527240481394676877 := by
  unfold tailWord_96626
  simp only [CollatzResearch.WordTrace]
  refine ⟨881059936986994813021433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2349493165298652834723821 881059936986994813021433)
  ·
    refine ⟨660794952740246109766075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 881059936986994813021433 660794952740246109766075)
    ·
      refine ⟨991192429110369164649113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660794952740246109766075 991192429110369164649113)
      ·
        refine ⟨743394321832776873486835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 991192429110369164649113 743394321832776873486835)
        ·
          refine ⟨1115091482749165310230253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743394321832776873486835 1115091482749165310230253)
          ·
            refine ⟨418159306030936991336345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1115091482749165310230253 418159306030936991336345)
            ·
              refine ⟨313619479523202743502259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418159306030936991336345 313619479523202743502259)
              ·
                refine ⟨470429219284804115253389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313619479523202743502259 470429219284804115253389)
                ·
                  refine ⟨176410957231801543220021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470429219284804115253389 176410957231801543220021)
                  ·
                    refine ⟨16538527240481394676877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176410957231801543220021 16538527240481394676877)
                    ·
                      rfl

theorem cell23_96626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_96626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96626 prefixEnd_96626 := by exact prefixLift 96626
  have htrace : WordTrace (prefixWord ++ tailWord_96626) baseStart_96626 baseEnd_96626 := by
    simpa [prefixWord, tailWord_96626, baseEnd_96626] using wordTrace_append hprefix tailTrace_96626
  have hstable : (prefixWord ++ tailWord_96626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96626).length < 2 ^ (prefixWord ++ tailWord_96626).sum := by decide
  have hdescent : baseEnd_96626 < baseStart_96626 := by decide
  rcases family_descends (prefixWord ++ tailWord_96626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96643 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 1, 5]
def baseStart_96643 : Nat := 118140960795 + 96643 * 2 ^ 59
def prefixEnd_96643 : Nat := 4983230072969 + 3 ^ 40 * 96643 * 2
def baseEnd_96643 : Nat := 16541436964190205839351

theorem tailTrace_96643 : CollatzResearch.WordTrace tailWord_96643 prefixEnd_96643 16541436964190205839351 := by
  unfold tailWord_96643
  simp only [CollatzResearch.WordTrace]
  refine ⟨3524859788886391155454583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2349906525924260770303055 3524859788886391155454583)
  ·
    refine ⟨5287289683329586733181875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3524859788886391155454583 5287289683329586733181875)
    ·
      refine ⟨7930934524994380099772813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287289683329586733181875 7930934524994380099772813)
      ·
        refine ⟨2974100446872892537414805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7930934524994380099772813 2974100446872892537414805)
        ·
          refine ⟨139410958447166837691319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2974100446872892537414805 139410958447166837691319)
          ·
            refine ⟨209116437670750256536979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139410958447166837691319 209116437670750256536979)
            ·
              refine ⟨313674656506125384805469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209116437670750256536979 313674656506125384805469)
              ·
                refine ⟨117627996189797019302051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313674656506125384805469 117627996189797019302051)
                ·
                  refine ⟨176441994284695528953077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117627996189797019302051 176441994284695528953077)
                  ·
                    refine ⟨16541436964190205839351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176441994284695528953077 16541436964190205839351)
                    ·
                      rfl

theorem cell23_96643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 5].length) (baseStart_96643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96643 prefixEnd_96643 := by exact prefixLift 96643
  have htrace : WordTrace (prefixWord ++ tailWord_96643) baseStart_96643 baseEnd_96643 := by
    simpa [prefixWord, tailWord_96643, baseEnd_96643] using wordTrace_append hprefix tailTrace_96643
  have hstable : (prefixWord ++ tailWord_96643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96643).length < 2 ^ (prefixWord ++ tailWord_96643).sum := by decide
  have hdescent : baseEnd_96643 < baseStart_96643 := by decide
  rcases family_descends (prefixWord ++ tailWord_96643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96659 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4]
def baseStart_96659 : Nat := 118140960795 + 96659 * 2 ^ 59
def prefixEnd_96659 : Nat := 4983230072969 + 3 ^ 40 * 96659 * 2
def baseEnd_96659 : Nat := 49632526583042554917979

theorem tailTrace_96659 : CollatzResearch.WordTrace tailWord_96659 prefixEnd_96659 49632526583042554917979 := by
  unfold tailWord_96659
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525443356828425888037031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2350295571218950592024687 3525443356828425888037031)
  ·
    refine ⟨5288165035242638832055547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3525443356828425888037031 5288165035242638832055547)
    ·
      refine ⟨7932247552863958248083321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288165035242638832055547 7932247552863958248083321)
      ·
        refine ⟨5949185664647968686062491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7932247552863958248083321 5949185664647968686062491)
        ·
          refine ⟨8923778496971953029093737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949185664647968686062491 8923778496971953029093737)
          ·
            refine ⟨6692833872728964771820303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8923778496971953029093737 6692833872728964771820303)
            ·
              refine ⟨10039250809093447157730455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692833872728964771820303 10039250809093447157730455)
              ·
                refine ⟨15058876213640170736595683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10039250809093447157730455 15058876213640170736595683)
                ·
                  refine ⟨22588314320460256104893525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15058876213640170736595683 22588314320460256104893525)
                  ·
                    refine ⟨264706808442893626229221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22588314320460256104893525 264706808442893626229221)
                    ·
                      refine ⟨49632526583042554917979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 264706808442893626229221 49632526583042554917979)
                      ·
                        rfl

theorem cell23_96659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_96659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96659 prefixEnd_96659 := by exact prefixLift 96659
  have htrace : WordTrace (prefixWord ++ tailWord_96659) baseStart_96659 baseEnd_96659 := by
    simpa [prefixWord, tailWord_96659, baseEnd_96659] using wordTrace_append hprefix tailTrace_96659
  have hstable : (prefixWord ++ tailWord_96659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96659).length < 2 ^ (prefixWord ++ tailWord_96659).sum := by decide
  have hdescent : baseEnd_96659 < baseStart_96659 := by decide
  rcases family_descends (prefixWord ++ tailWord_96659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96666 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_96666 : Nat := 118140960795 + 96666 * 2 ^ 59
def prefixEnd_96666 : Nat := 4983230072969 + 3 ^ 40 * 96666 * 2
def baseEnd_96666 : Nat := 49636120947624027530447

theorem tailTrace_96666 : CollatzResearch.WordTrace tailWord_96666 prefixEnd_96666 49636120947624027530447 := by
  unfold tailWord_96666
  simp only [CollatzResearch.WordTrace]
  refine ⟨881424666950766520885463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2350465778535377389027901 881424666950766520885463)
  ·
    refine ⟨1322137000426149781328195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 881424666950766520885463 1322137000426149781328195)
    ·
      refine ⟨1983205500639224671992293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322137000426149781328195 1983205500639224671992293)
      ·
        refine ⟨371851031369854625998555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1983205500639224671992293 371851031369854625998555)
        ·
          refine ⟨557776547054781938997833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371851031369854625998555 557776547054781938997833)
          ·
            refine ⟨418332410291086454248375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557776547054781938997833 418332410291086454248375)
            ·
              refine ⟨627498615436629681372563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418332410291086454248375 627498615436629681372563)
              ·
                refine ⟨941247923154944522058845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627498615436629681372563 941247923154944522058845)
                ·
                  refine ⟨352967971183104195772067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941247923154944522058845 352967971183104195772067)
                  ·
                    refine ⟨529451956774656293658101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 352967971183104195772067 529451956774656293658101)
                    ·
                      refine ⟨49636120947624027530447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 529451956774656293658101 49636120947624027530447)
                      ·
                        rfl

theorem cell23_96666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_96666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96666 prefixEnd_96666 := by exact prefixLift 96666
  have htrace : WordTrace (prefixWord ++ tailWord_96666) baseStart_96666 baseEnd_96666 := by
    simpa [prefixWord, tailWord_96666, baseEnd_96666] using wordTrace_append hprefix tailTrace_96666
  have hstable : (prefixWord ++ tailWord_96666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96666).length < 2 ^ (prefixWord ++ tailWord_96666).sum := by decide
  have hdescent : baseEnd_96666 < baseStart_96666 := by decide
  rcases family_descends (prefixWord ++ tailWord_96666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96680 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_96680 : Nat := 118140960795 + 96680 * 2 ^ 59
def prefixEnd_96680 : Nat := 4983230072969 + 3 ^ 40 * 96680 * 2
def baseEnd_96680 : Nat := 49643309676786972755383

theorem tailTrace_96680 : CollatzResearch.WordTrace tailWord_96680 prefixEnd_96680 49643309676786972755383 := by
  unfold tailWord_96680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763104644876173237275747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2350806193168230983034329 1763104644876173237275747)
  ·
    refine ⟨2644656967314259855913621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763104644876173237275747 2644656967314259855913621)
    ·
      refine ⟨123968295342855930745951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2644656967314259855913621 123968295342855930745951)
      ·
        refine ⟨185952443014283896118927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123968295342855930745951 185952443014283896118927)
        ·
          refine ⟨278928664521425844178391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185952443014283896118927 278928664521425844178391)
          ·
            refine ⟨418392996782138766267587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278928664521425844178391 418392996782138766267587)
            ·
              refine ⟨627589495173208149401381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418392996782138766267587 627589495173208149401381)
              ·
                refine ⟨117673030344976528012759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627589495173208149401381 117673030344976528012759)
                ·
                  refine ⟨176509545517464792019139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117673030344976528012759 176509545517464792019139)
                  ·
                    refine ⟨264764318276197188028709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176509545517464792019139 264764318276197188028709)
                    ·
                      refine ⟨49643309676786972755383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 264764318276197188028709 49643309676786972755383)
                      ·
                        rfl

theorem cell23_96680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_96680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96680 prefixEnd_96680 := by exact prefixLift 96680
  have htrace : WordTrace (prefixWord ++ tailWord_96680) baseStart_96680 baseEnd_96680 := by
    simpa [prefixWord, tailWord_96680, baseEnd_96680] using wordTrace_append hprefix tailTrace_96680
  have hstable : (prefixWord ++ tailWord_96680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96680).length < 2 ^ (prefixWord ++ tailWord_96680).sum := by decide
  have hdescent : baseEnd_96680 < baseStart_96680 := by decide
  rcases family_descends (prefixWord ++ tailWord_96680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96696 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_96696 : Nat := 118140960795 + 96696 * 2 ^ 59
def prefixEnd_96696 : Nat := 4983230072969 + 3 ^ 40 * 96696 * 2
def baseEnd_96696 : Nat := 49651525367258910155309

theorem tailTrace_96696 : CollatzResearch.WordTrace tailWord_96696 prefixEnd_96696 49651525367258910155309 := by
  unfold tailWord_96696
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763396428847190603566971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2351195238462920804755961 1763396428847190603566971)
  ·
    refine ⟨2645094643270785905350457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763396428847190603566971 2645094643270785905350457)
    ·
      refine ⟨1983820982453089429012843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2645094643270785905350457 1983820982453089429012843)
      ·
        refine ⟨2975731473679634143519265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983820982453089429012843 2975731473679634143519265)
        ·
          refine ⟨2231798605259725607639449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2975731473679634143519265 2231798605259725607639449)
          ·
            refine ⟨1673848953944794205729587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231798605259725607639449 1673848953944794205729587)
            ·
              refine ⟨2510773430917191308594381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673848953944794205729587 2510773430917191308594381)
              ·
                refine ⟨941540036593946740722893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510773430917191308594381 941540036593946740722893)
                ·
                  refine ⟨353077513722730027771085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941540036593946740722893 353077513722730027771085)
                  ·
                    refine ⟨132404067646023760414157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353077513722730027771085 132404067646023760414157)
                    ·
                      refine ⟨49651525367258910155309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132404067646023760414157 49651525367258910155309)
                      ·
                        rfl

theorem cell23_96696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_96696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96696 prefixEnd_96696 := by exact prefixLift 96696
  have htrace : WordTrace (prefixWord ++ tailWord_96696) baseStart_96696 baseEnd_96696 := by
    simpa [prefixWord, tailWord_96696, baseEnd_96696] using wordTrace_append hprefix tailTrace_96696
  have hstable : (prefixWord ++ tailWord_96696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96696).length < 2 ^ (prefixWord ++ tailWord_96696).sum := by decide
  have hdescent : baseEnd_96696 < baseStart_96696 := by decide
  rcases family_descends (prefixWord ++ tailWord_96696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96699 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 6, 7]
def baseStart_96699 : Nat := 118140960795 + 96699 * 2 ^ 59
def prefixEnd_96699 : Nat := 4983230072969 + 3 ^ 40 * 96699 * 2
def baseEnd_96699 : Nat := 16551021936407466139265

theorem tailTrace_96699 : CollatzResearch.WordTrace tailWord_96699 prefixEnd_96699 16551021936407466139265 := by
  unfold tailWord_96699
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526902276683512719493151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2351268184455675146328767 3526902276683512719493151)
  ·
    refine ⟨5290353415025269079239727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3526902276683512719493151 5290353415025269079239727)
    ·
      refine ⟨7935530122537903618859591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5290353415025269079239727 7935530122537903618859591)
      ·
        refine ⟨11903295183806855428289387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935530122537903618859591 11903295183806855428289387)
        ·
          refine ⟨17854942775710283142434081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11903295183806855428289387 17854942775710283142434081)
          ·
            refine ⟨13391207081782712356825561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17854942775710283142434081 13391207081782712356825561)
            ·
              refine ⟨10043405311337034267619171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13391207081782712356825561 10043405311337034267619171)
              ·
                refine ⟨15065107967005551401428757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10043405311337034267619171 15065107967005551401428757)
                ·
                  refine ⟨706176935953385221941973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15065107967005551401428757 706176935953385221941973)
                  ·
                    refine ⟨16551021936407466139265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 706176935953385221941973 16551021936407466139265)
                    ·
                      rfl

theorem cell23_96699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_96699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96699 prefixEnd_96699 := by exact prefixLift 96699
  have htrace : WordTrace (prefixWord ++ tailWord_96699) baseStart_96699 baseEnd_96699 := by
    simpa [prefixWord, tailWord_96699, baseEnd_96699] using wordTrace_append hprefix tailTrace_96699
  have hstable : (prefixWord ++ tailWord_96699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96699).length < 2 ^ (prefixWord ++ tailWord_96699).sum := by decide
  have hdescent : baseEnd_96699 < baseStart_96699 := by decide
  rcases family_descends (prefixWord ++ tailWord_96699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96700 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_96700 : Nat := 118140960795 + 96700 * 2 ^ 59
def prefixEnd_96700 : Nat := 4983230072969 + 3 ^ 40 * 96700 * 2
def baseEnd_96700 : Nat := 49653579289876894505291

theorem tailTrace_96700 : CollatzResearch.WordTrace tailWord_96700 prefixEnd_96700 49653579289876894505291 := by
  unfold tailWord_96700
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763469374839944945139777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2351292499786593260186369 1763469374839944945139777)
  ·
    refine ⟨1322602031129958708854833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1763469374839944945139777 1322602031129958708854833)
    ·
      refine ⟨991951523347469031641125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1322602031129958708854833 991951523347469031641125)
      ·
        refine ⟨185990910627650443432711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 991951523347469031641125 185990910627650443432711)
        ·
          refine ⟨278986365941475665149067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185990910627650443432711 278986365941475665149067)
          ·
            refine ⟨418479548912213497723601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278986365941475665149067 418479548912213497723601)
            ·
              refine ⟨313859661684160123292701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418479548912213497723601 313859661684160123292701)
              ·
                refine ⟨117697373131560046234763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313859661684160123292701 117697373131560046234763)
                ·
                  refine ⟨176546059697340069352145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117697373131560046234763 176546059697340069352145)
                  ·
                    refine ⟨132409544773005052014109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176546059697340069352145 132409544773005052014109)
                    ·
                      refine ⟨49653579289876894505291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132409544773005052014109 49653579289876894505291)
                      ·
                        rfl

theorem cell23_96700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_96700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96700 prefixEnd_96700 := by exact prefixLift 96700
  have htrace : WordTrace (prefixWord ++ tailWord_96700) baseStart_96700 baseEnd_96700 := by
    simpa [prefixWord, tailWord_96700, baseEnd_96700] using wordTrace_append hprefix tailTrace_96700
  have hstable : (prefixWord ++ tailWord_96700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96700).length < 2 ^ (prefixWord ++ tailWord_96700).sum := by decide
  have hdescent : baseEnd_96700 < baseStart_96700 := by decide
  rcases family_descends (prefixWord ++ tailWord_96700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96713 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 3]
def baseStart_96713 : Nat := 118140960795 + 96713 * 2 ^ 59
def prefixEnd_96713 : Nat := 4983230072969 + 3 ^ 40 * 96713 * 2
def baseEnd_96713 : Nat := 49660254538385343642731

theorem tailTrace_96713 : CollatzResearch.WordTrace tailWord_96713 prefixEnd_96713 49660254538385343642731 := by
  unfold tailWord_96713
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527412898632793110502793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2351608599088528740335195 3527412898632793110502793)
  ·
    refine ⟨2645559673974594832877095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3527412898632793110502793 2645559673974594832877095)
    ·
      refine ⟨3968339510961892249315643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2645559673974594832877095 3968339510961892249315643)
      ·
        refine ⟨5952509266442838373973465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968339510961892249315643 5952509266442838373973465)
        ·
          refine ⟨4464381949832128780480099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5952509266442838373973465 4464381949832128780480099)
          ·
            refine ⟨6696572924748193170720149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464381949832128780480099 6696572924748193170720149)
            ·
              refine ⟨313901855847571554877507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6696572924748193170720149 313901855847571554877507)
              ·
                refine ⟨470852783771357332316261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313901855847571554877507 470852783771357332316261)
                ·
                  refine ⟨88284896957129499809299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470852783771357332316261 88284896957129499809299)
                  ·
                    refine ⟨132427345435694249713949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88284896957129499809299 132427345435694249713949)
                    ·
                      refine ⟨49660254538385343642731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132427345435694249713949 49660254538385343642731)
                      ·
                        rfl

theorem cell23_96713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_96713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96713 prefixEnd_96713 := by exact prefixLift 96713
  have htrace : WordTrace (prefixWord ++ tailWord_96713) baseStart_96713 baseEnd_96713 := by
    simpa [prefixWord, tailWord_96713, baseEnd_96713] using wordTrace_append hprefix tailTrace_96713
  have hstable : (prefixWord ++ tailWord_96713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96713).length < 2 ^ (prefixWord ++ tailWord_96713).sum := by decide
  have hdescent : baseEnd_96713 < baseStart_96713 := by decide
  rcases family_descends (prefixWord ++ tailWord_96713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96714 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_96714 : Nat := 118140960795 + 96714 * 2 ^ 59
def prefixEnd_96714 : Nat := 4983230072969 + 3 ^ 40 * 96714 * 2
def baseEnd_96714 : Nat := 49660768019039839730227

theorem tailTrace_96714 : CollatzResearch.WordTrace tailWord_96714 prefixEnd_96714 49660768019039839730227 := by
  unfold tailWord_96714
  simp only [CollatzResearch.WordTrace]
  refine ⟨881862342907292570322299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2351632914419446854192797 881862342907292570322299)
  ·
    refine ⟨1322793514360938855483449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 881862342907292570322299 1322793514360938855483449)
    ·
      refine ⟨992095135770704141612587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1322793514360938855483449 992095135770704141612587)
      ·
        refine ⟨1488142703656056212418881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992095135770704141612587 1488142703656056212418881)
        ·
          refine ⟨1116107027742042159314161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488142703656056212418881 1116107027742042159314161)
          ·
            refine ⟨837080270806531619485621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116107027742042159314161 837080270806531619485621)
            ·
              refine ⟨78476275388112339326777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 837080270806531619485621 78476275388112339326777)
              ·
                refine ⟨58857206541084254495083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78476275388112339326777 58857206541084254495083)
                ·
                  refine ⟨88285809811626381742625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58857206541084254495083 88285809811626381742625)
                  ·
                    refine ⟨66214357358719786306969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88285809811626381742625 66214357358719786306969)
                    ·
                      refine ⟨49660768019039839730227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66214357358719786306969 49660768019039839730227)
                      ·
                        rfl

theorem cell23_96714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_96714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96714 prefixEnd_96714 := by exact prefixLift 96714
  have htrace : WordTrace (prefixWord ++ tailWord_96714) baseStart_96714 baseEnd_96714 := by
    simpa [prefixWord, tailWord_96714, baseEnd_96714] using wordTrace_append hprefix tailTrace_96714
  have hstable : (prefixWord ++ tailWord_96714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96714).length < 2 ^ (prefixWord ++ tailWord_96714).sum := by decide
  have hdescent : baseEnd_96714 < baseStart_96714 := by decide
  rcases family_descends (prefixWord ++ tailWord_96714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96730 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_96730 : Nat := 118140960795 + 96730 * 2 ^ 59
def prefixEnd_96730 : Nat := 4983230072969 + 3 ^ 40 * 96730 * 2
def baseEnd_96730 : Nat := 49668983709511777130153

theorem tailTrace_96730 : CollatzResearch.WordTrace tailWord_96730 prefixEnd_96730 49668983709511777130153 := by
  unfold tailWord_96730
  simp only [CollatzResearch.WordTrace]
  refine ⟨882008234892801253467911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2352021959714136675914429 882008234892801253467911)
  ·
    refine ⟨1323012352339201880201867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882008234892801253467911 1323012352339201880201867)
    ·
      refine ⟨1984518528508802820302801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323012352339201880201867 1984518528508802820302801)
      ·
        refine ⟨1488388896381602115227101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1984518528508802820302801 1488388896381602115227101)
        ·
          refine ⟨558145836143100793210163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1488388896381602115227101 558145836143100793210163)
          ·
            refine ⟨837218754214651189815245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558145836143100793210163 837218754214651189815245)
            ·
              refine ⟨313957032830494196180717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 837218754214651189815245 313957032830494196180717)
              ·
                refine ⟨117733887311435323567769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313957032830494196180717 117733887311435323567769)
                ·
                  refine ⟨88300415483576492675827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117733887311435323567769 88300415483576492675827)
                  ·
                    refine ⟨132450623225364739013741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88300415483576492675827 132450623225364739013741)
                    ·
                      refine ⟨49668983709511777130153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132450623225364739013741 49668983709511777130153)
                      ·
                        rfl

theorem cell23_96730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_96730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96730 prefixEnd_96730 := by exact prefixLift 96730
  have htrace : WordTrace (prefixWord ++ tailWord_96730) baseStart_96730 baseEnd_96730 := by
    simpa [prefixWord, tailWord_96730, baseEnd_96730] using wordTrace_append hprefix tailTrace_96730
  have hstable : (prefixWord ++ tailWord_96730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96730).length < 2 ^ (prefixWord ++ tailWord_96730).sum := by decide
  have hdescent : baseEnd_96730 < baseStart_96730 := by decide
  rcases family_descends (prefixWord ++ tailWord_96730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96776 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 7]
def baseStart_96776 : Nat := 118140960795 + 96776 * 2 ^ 59
def prefixEnd_96776 : Nat := 4983230072969 + 3 ^ 40 * 96776 * 2
def baseEnd_96776 : Nat := 5521400424402066350549

theorem tailTrace_96776 : CollatzResearch.WordTrace tailWord_96776 prefixEnd_96776 5521400424402066350549 := by
  unfold tailWord_96776
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764855348702277435023091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2353140464936369913364121 1764855348702277435023091)
  ·
    refine ⟨2647283023053416152534637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764855348702277435023091 2647283023053416152534637)
    ·
      refine ⟨992731133645031057200489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2647283023053416152534637 992731133645031057200489)
      ·
        refine ⟨744548350233773292900367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992731133645031057200489 744548350233773292900367)
        ·
          refine ⟨1116822525350659939350551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744548350233773292900367 1116822525350659939350551)
          ·
            refine ⟨1675233788025989909025827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116822525350659939350551 1675233788025989909025827)
            ·
              refine ⟨2512850682038984863538741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675233788025989909025827 2512850682038984863538741)
              ·
                refine ⟨235579751441154830956757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2512850682038984863538741 235579751441154830956757)
                ·
                  refine ⟨5521400424402066350549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 235579751441154830956757 5521400424402066350549)
                  ·
                    rfl

theorem cell23_96776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_96776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96776 prefixEnd_96776 := by exact prefixLift 96776
  have htrace : WordTrace (prefixWord ++ tailWord_96776) baseStart_96776 baseEnd_96776 := by
    simpa [prefixWord, tailWord_96776, baseEnd_96776] using wordTrace_append hprefix tailTrace_96776
  have hstable : (prefixWord ++ tailWord_96776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96776).length < 2 ^ (prefixWord ++ tailWord_96776).sum := by decide
  have hdescent : baseEnd_96776 < baseStart_96776 := by decide
  rcases family_descends (prefixWord ++ tailWord_96776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96810 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_96810 : Nat := 118140960795 + 96810 * 2 ^ 59
def prefixEnd_96810 : Nat := 4983230072969 + 3 ^ 40 * 96810 * 2
def baseEnd_96810 : Nat := 5523340240207940458865

theorem tailTrace_96810 : CollatzResearch.WordTrace tailWord_96810 prefixEnd_96810 5523340240207940458865 := by
  unfold tailWord_96810
  simp only [CollatzResearch.WordTrace]
  refine ⟨882737694820344669195971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2353967186187585784522589 882737694820344669195971)
  ·
    refine ⟨1324106542230517003793957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882737694820344669195971 1324106542230517003793957)
    ·
      refine ⟨248269976668221938211367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1324106542230517003793957 248269976668221938211367)
      ·
        refine ⟨372404965002332907317051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248269976668221938211367 372404965002332907317051)
        ·
          refine ⟨558607447503499360975577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372404965002332907317051 558607447503499360975577)
          ·
            refine ⟨418955585627624520731683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558607447503499360975577 418955585627624520731683)
            ·
              refine ⟨628433378441436781097525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418955585627624520731683 628433378441436781097525)
              ·
                refine ⟨58915629228884698227893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 628433378441436781097525 58915629228884698227893)
                ·
                  refine ⟨5523340240207940458865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58915629228884698227893 5523340240207940458865)
                  ·
                    rfl

theorem cell23_96810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_96810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96810 prefixEnd_96810 := by exact prefixLift 96810
  have htrace : WordTrace (prefixWord ++ tailWord_96810) baseStart_96810 baseEnd_96810 := by
    simpa [prefixWord, tailWord_96810, baseEnd_96810] using wordTrace_append hprefix tailTrace_96810
  have hstable : (prefixWord ++ tailWord_96810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96810).length < 2 ^ (prefixWord ++ tailWord_96810).sum := by decide
  have hdescent : baseEnd_96810 < baseStart_96810 := by decide
  rcases family_descends (prefixWord ++ tailWord_96810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96816 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_96816 : Nat := 118140960795 + 96816 * 2 ^ 59
def prefixEnd_96816 : Nat := 4983230072969 + 3 ^ 40 * 96816 * 2
def baseEnd_96816 : Nat := 49713143045798440654757

theorem tailTrace_96816 : CollatzResearch.WordTrace tailWord_96816 prefixEnd_96816 49713143045798440654757 := by
  unfold tailWord_96816
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765584808629820850751151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2354113078173094467668201 1765584808629820850751151)
  ·
    refine ⟨2648377212944731276126727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765584808629820850751151 2648377212944731276126727)
    ·
      refine ⟨3972565819417096914190091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648377212944731276126727 3972565819417096914190091)
      ·
        refine ⟨5958848729125645371285137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972565819417096914190091 5958848729125645371285137)
        ·
          refine ⟨4469136546844234028463853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5958848729125645371285137 4469136546844234028463853)
          ·
            refine ⟨1675926205066587760673945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4469136546844234028463853 1675926205066587760673945)
            ·
              refine ⟨1256944653799940820505459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675926205066587760673945 1256944653799940820505459)
              ·
                refine ⟨1885416980699911230758189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256944653799940820505459 1885416980699911230758189)
                ·
                  refine ⟨707031367762466711534321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1885416980699911230758189 707031367762466711534321)
                  ·
                    refine ⟨530273525821850033650741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 707031367762466711534321 530273525821850033650741)
                    ·
                      refine ⟨49713143045798440654757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 530273525821850033650741 49713143045798440654757)
                      ·
                        rfl

theorem cell23_96816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_96816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96816 prefixEnd_96816 := by exact prefixLift 96816
  have htrace : WordTrace (prefixWord ++ tailWord_96816) baseStart_96816 baseEnd_96816 := by
    simpa [prefixWord, tailWord_96816, baseEnd_96816] using wordTrace_append hprefix tailTrace_96816
  have hstable : (prefixWord ++ tailWord_96816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96816).length < 2 ^ (prefixWord ++ tailWord_96816).sum := by decide
  have hdescent : baseEnd_96816 < baseStart_96816 := by decide
  rcases family_descends (prefixWord ++ tailWord_96816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96838 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_96838 : Nat := 118140960795 + 96838 * 2 ^ 59
def prefixEnd_96838 : Nat := 4983230072969 + 3 ^ 40 * 96838 * 2
def baseEnd_96838 : Nat := 49724439620197354579657

theorem tailTrace_96838 : CollatzResearch.WordTrace tailWord_96838 prefixEnd_96838 49724439620197354579657 := by
  unfold tailWord_96838
  simp only [CollatzResearch.WordTrace]
  refine ⟨110374125724373108087599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2354648015453292972535445 110374125724373108087599)
  ·
    refine ⟨165561188586559662131399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110374125724373108087599 165561188586559662131399)
    ·
      refine ⟨248341782879839493197099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165561188586559662131399 248341782879839493197099)
      ·
        refine ⟨372512674319759239795649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248341782879839493197099 372512674319759239795649)
        ·
          refine ⟨279384505739819429846737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372512674319759239795649 279384505739819429846737)
          ·
            refine ⟨209538379304864572385053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279384505739819429846737 209538379304864572385053)
            ·
              refine ⟨78576892239324214644395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209538379304864572385053 78576892239324214644395)
              ·
                refine ⟨117865338358986321966593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78576892239324214644395 117865338358986321966593)
                ·
                  refine ⟨88399003769239741474945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117865338358986321966593 88399003769239741474945)
                  ·
                    refine ⟨66299252826929806106209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88399003769239741474945 66299252826929806106209)
                    ·
                      refine ⟨49724439620197354579657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66299252826929806106209 49724439620197354579657)
                      ·
                        rfl

theorem cell23_96838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_96838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96838 prefixEnd_96838 := by exact prefixLift 96838
  have htrace : WordTrace (prefixWord ++ tailWord_96838) baseStart_96838 baseEnd_96838 := by
    simpa [prefixWord, tailWord_96838, baseEnd_96838] using wordTrace_append hprefix tailTrace_96838
  have hstable : (prefixWord ++ tailWord_96838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96838).length < 2 ^ (prefixWord ++ tailWord_96838).sum := by decide
  have hdescent : baseEnd_96838 < baseStart_96838 := by decide
  rcases family_descends (prefixWord ++ tailWord_96838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96863 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_96863 : Nat := 118140960795 + 96863 * 2 ^ 59
def prefixEnd_96863 : Nat := 4983230072969 + 3 ^ 40 * 96863 * 2
def baseEnd_96863 : Nat := 49737276636559756767041

theorem tailTrace_96863 : CollatzResearch.WordTrace tailWord_96863 prefixEnd_96863 49737276636559756767041 := by
  unfold tailWord_96863
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532883848089368728463243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2355255898726245818975495 3532883848089368728463243)
  ·
    refine ⟨5299325772134053092694865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3532883848089368728463243 5299325772134053092694865)
    ·
      refine ⟨3974494329100539819521149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5299325772134053092694865 3974494329100539819521149)
      ·
        refine ⟨1490435373412702432320431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3974494329100539819521149 1490435373412702432320431)
        ·
          refine ⟨2235653060119053648480647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490435373412702432320431 2235653060119053648480647)
          ·
            refine ⟨3353479590178580472720971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235653060119053648480647 3353479590178580472720971)
            ·
              refine ⟨5030219385267870709081457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353479590178580472720971 5030219385267870709081457)
              ·
                refine ⟨3772664538950903031811093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030219385267870709081457 3772664538950903031811093)
                ·
                  refine ⟨176843650263323579616145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3772664538950903031811093 176843650263323579616145)
                  ·
                    refine ⟨132632737697492684712109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176843650263323579616145 132632737697492684712109)
                    ·
                      refine ⟨49737276636559756767041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132632737697492684712109 49737276636559756767041)
                      ·
                        rfl

theorem cell23_96863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_96863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96863 prefixEnd_96863 := by exact prefixLift 96863
  have htrace : WordTrace (prefixWord ++ tailWord_96863) baseStart_96863 baseEnd_96863 := by
    simpa [prefixWord, tailWord_96863, baseEnd_96863] using wordTrace_append hprefix tailTrace_96863
  have hstable : (prefixWord ++ tailWord_96863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96863).length < 2 ^ (prefixWord ++ tailWord_96863).sum := by decide
  have hdescent : baseEnd_96863 < baseStart_96863 := by decide
  rcases family_descends (prefixWord ++ tailWord_96863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96900 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 6]
def baseStart_96900 : Nat := 118140960795 + 96900 * 2 ^ 59
def prefixEnd_96900 : Nat := 4983230072969 + 3 ^ 40 * 96900 * 2
def baseEnd_96900 : Nat := 5528475046752901333819

theorem tailTrace_96900 : CollatzResearch.WordTrace tailWord_96900 prefixEnd_96900 5528475046752901333819 := by
  unfold tailWord_96900
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767116674477662023780077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2356155565970216031706769 1767116674477662023780077)
  ·
    refine ⟨662668752929123258917529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1767116674477662023780077 662668752929123258917529)
    ·
      refine ⟨497001564696842444188147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 662668752929123258917529 497001564696842444188147)
      ·
        refine ⟨745502347045263666282221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497001564696842444188147 745502347045263666282221)
        ·
          refine ⟨279563380141973874855833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 745502347045263666282221 279563380141973874855833)
          ·
            refine ⟨209672535106480406141875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279563380141973874855833 209672535106480406141875)
            ·
              refine ⟨314508802659720609212813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209672535106480406141875 314508802659720609212813)
              ·
                refine ⟨117940800997395228454805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314508802659720609212813 117940800997395228454805)
                ·
                  refine ⟨5528475046752901333819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117940800997395228454805 5528475046752901333819)
                  ·
                    rfl

theorem cell23_96900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_96900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96900 prefixEnd_96900 := by exact prefixLift 96900
  have htrace : WordTrace (prefixWord ++ tailWord_96900) baseStart_96900 baseEnd_96900 := by
    simpa [prefixWord, tailWord_96900, baseEnd_96900] using wordTrace_append hprefix tailTrace_96900
  have hstable : (prefixWord ++ tailWord_96900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96900).length < 2 ^ (prefixWord ++ tailWord_96900).sum := by decide
  have hdescent : baseEnd_96900 < baseStart_96900 := by decide
  rcases family_descends (prefixWord ++ tailWord_96900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96953 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_96953 : Nat := 118140960795 + 96953 * 2 ^ 59
def prefixEnd_96953 : Nat := 4983230072969 + 3 ^ 40 * 96953 * 2
def baseEnd_96953 : Nat := 49783489895464404641627

theorem tailTrace_96953 : CollatzResearch.WordTrace tailWord_96953 prefixEnd_96953 49783489895464404641627 := by
  unfold tailWord_96953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536166417763314099239513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2357444278508876066159675 3536166417763314099239513)
  ·
    refine ⟨2652124813322485574429635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3536166417763314099239513 2652124813322485574429635)
    ·
      refine ⟨3978187219983728361644453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652124813322485574429635 3978187219983728361644453)
      ·
        refine ⟨745910103746949067808335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3978187219983728361644453 745910103746949067808335)
        ·
          refine ⟨1118865155620423601712503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745910103746949067808335 1118865155620423601712503)
          ·
            refine ⟨1678297733430635402568755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118865155620423601712503 1678297733430635402568755)
            ·
              refine ⟨2517446600145953103853133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678297733430635402568755 2517446600145953103853133)
              ·
                refine ⟨944042475054732413944925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2517446600145953103853133 944042475054732413944925)
                ·
                  refine ⟨354015928145524655229347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944042475054732413944925 354015928145524655229347)
                  ·
                    refine ⟨531023892218286982844021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 354015928145524655229347 531023892218286982844021)
                    ·
                      refine ⟨49783489895464404641627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 531023892218286982844021 49783489895464404641627)
                      ·
                        rfl

theorem cell23_96953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_96953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96953 prefixEnd_96953 := by exact prefixLift 96953
  have htrace : WordTrace (prefixWord ++ tailWord_96953) baseStart_96953 baseEnd_96953 := by
    simpa [prefixWord, tailWord_96953, baseEnd_96953] using wordTrace_append hprefix tailTrace_96953
  have hstable : (prefixWord ++ tailWord_96953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96953).length < 2 ^ (prefixWord ++ tailWord_96953).sum := by decide
  have hdescent : baseEnd_96953 < baseStart_96953 := by decide
  rcases family_descends (prefixWord ++ tailWord_96953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96960 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 1, 6]
def baseStart_96960 : Nat := 118140960795 + 96960 * 2 ^ 59
def prefixEnd_96960 : Nat := 4983230072969 + 3 ^ 40 * 96960 * 2
def baseEnd_96960 : Nat := 16595694753348625751365

theorem tailTrace_96960 : CollatzResearch.WordTrace tailWord_96960 prefixEnd_96960 16595694753348625751365 := by
  unfold tailWord_96960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768210864368977147372167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2357614485825302863162889 1768210864368977147372167)
  ·
    refine ⟨2652316296553465721058251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768210864368977147372167 2652316296553465721058251)
    ·
      refine ⟨3978474444830198581587377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652316296553465721058251 3978474444830198581587377)
      ·
        refine ⟨2983855833622648936190533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3978474444830198581587377 2983855833622648936190533)
        ·
          refine ⟨559472968804246675535725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2983855833622648936190533 559472968804246675535725)
          ·
            refine ⟨209802363301592503325897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559472968804246675535725 209802363301592503325897)
            ·
              refine ⟨157351772476194377494423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209802363301592503325897 157351772476194377494423)
              ·
                refine ⟨236027658714291566241635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157351772476194377494423 236027658714291566241635)
                ·
                  refine ⟨354041488071437349362453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236027658714291566241635 354041488071437349362453)
                  ·
                    refine ⟨16595694753348625751365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 354041488071437349362453 16595694753348625751365)
                    ·
                      rfl

theorem cell23_96960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_96960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96960 prefixEnd_96960 := by exact prefixLift 96960
  have htrace : WordTrace (prefixWord ++ tailWord_96960) baseStart_96960 baseEnd_96960 := by
    simpa [prefixWord, tailWord_96960, baseEnd_96960] using wordTrace_append hprefix tailTrace_96960
  have hstable : (prefixWord ++ tailWord_96960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96960).length < 2 ^ (prefixWord ++ tailWord_96960).sum := by decide
  have hdescent : baseEnd_96960 < baseStart_96960 := by decide
  rcases family_descends (prefixWord ++ tailWord_96960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96961 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_96961 : Nat := 118140960795 + 96961 * 2 ^ 59
def prefixEnd_96961 : Nat := 4983230072969 + 3 ^ 40 * 96961 * 2
def baseEnd_96961 : Nat := 49787597740700373341591

theorem tailTrace_96961 : CollatzResearch.WordTrace tailWord_96961 prefixEnd_96961 49787597740700373341591 := by
  unfold tailWord_96961
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536458201734331465530737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2357638801156220977020491 3536458201734331465530737)
  ·
    refine ⟨2652343651300748599148053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3536458201734331465530737 2652343651300748599148053)
    ·
      refine ⟨124328608654722590585065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2652343651300748599148053 124328608654722590585065)
      ·
        refine ⟨93246456491041942938799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124328608654722590585065 93246456491041942938799)
        ·
          refine ⟨139869684736562914408199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93246456491041942938799 139869684736562914408199)
          ·
            refine ⟨209804527104844371612299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139869684736562914408199 209804527104844371612299)
            ·
              refine ⟨314706790657266557418449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209804527104844371612299 314706790657266557418449)
              ·
                refine ⟨236030092992949918063837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314706790657266557418449 236030092992949918063837)
                ·
                  refine ⟨88511284872356219273939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236030092992949918063837 88511284872356219273939)
                  ·
                    refine ⟨132766927308534328910909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88511284872356219273939 132766927308534328910909)
                    ·
                      refine ⟨49787597740700373341591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132766927308534328910909 49787597740700373341591)
                      ·
                        rfl

theorem cell23_96961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_96961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96961 prefixEnd_96961 := by exact prefixLift 96961
  have htrace : WordTrace (prefixWord ++ tailWord_96961) baseStart_96961 baseEnd_96961 := by
    simpa [prefixWord, tailWord_96961, baseEnd_96961] using wordTrace_append hprefix tailTrace_96961
  have hstable : (prefixWord ++ tailWord_96961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96961).length < 2 ^ (prefixWord ++ tailWord_96961).sum := by decide
  have hdescent : baseEnd_96961 < baseStart_96961 := by decide
  rcases family_descends (prefixWord ++ tailWord_96961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96981 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_96981 : Nat := 118140960795 + 96981 * 2 ^ 59
def prefixEnd_96981 : Nat := 4983230072969 + 3 ^ 40 * 96981 * 2
def baseEnd_96981 : Nat := 16599289117930098363833

theorem tailTrace_96981 : CollatzResearch.WordTrace tailWord_96981 prefixEnd_96981 16599289117930098363833 := by
  unfold tailWord_96981
  simp only [CollatzResearch.WordTrace]
  refine ⟨3537187661661874881258797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2358125107774583254172531 3537187661661874881258797)
  ·
    refine ⟨1326445373123203080472049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3537187661661874881258797 1326445373123203080472049)
    ·
      refine ⟨994834029842402310354037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1326445373123203080472049 994834029842402310354037)
      ·
        refine ⟨93265690297725216595691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 994834029842402310354037 93265690297725216595691)
        ·
          refine ⟨139898535446587824893537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93265690297725216595691 139898535446587824893537)
          ·
            refine ⟨104923901584940868670153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139898535446587824893537 104923901584940868670153)
            ·
              refine ⟨78692926188705651502615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104923901584940868670153 78692926188705651502615)
              ·
                refine ⟨118039389283058477253923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78692926188705651502615 118039389283058477253923)
                ·
                  refine ⟨177059083924587715880885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118039389283058477253923 177059083924587715880885)
                  ·
                    refine ⟨16599289117930098363833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177059083924587715880885 16599289117930098363833)
                    ·
                      rfl

theorem cell23_96981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_96981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96981 prefixEnd_96981 := by exact prefixLift 96981
  have htrace : WordTrace (prefixWord ++ tailWord_96981) baseStart_96981 baseEnd_96981 := by
    simpa [prefixWord, tailWord_96981, baseEnd_96981] using wordTrace_append hprefix tailTrace_96981
  have hstable : (prefixWord ++ tailWord_96981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96981).length < 2 ^ (prefixWord ++ tailWord_96981).sum := by decide
  have hdescent : baseEnd_96981 < baseStart_96981 := by decide
  rcases family_descends (prefixWord ++ tailWord_96981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_96984 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 1, 1, 4]
def baseStart_96984 : Nat := 118140960795 + 96984 * 2 ^ 59
def prefixEnd_96984 : Nat := 4983230072969 + 3 ^ 40 * 96984 * 2
def baseEnd_96984 : Nat := 49799407795753783353985

theorem tailTrace_96984 : CollatzResearch.WordTrace tailWord_96984 prefixEnd_96984 49799407795753783353985 := by
  unfold tailWord_96984
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768648540325503196809003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2358198053767337595745337 1768648540325503196809003)
  ·
    refine ⟨2652972810488254795213505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768648540325503196809003 2652972810488254795213505)
    ·
      refine ⟨1989729607866191096410129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2652972810488254795213505 1989729607866191096410129)
      ·
        refine ⟨1492297205899643322307597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1989729607866191096410129 1492297205899643322307597)
        ·
          refine ⟨559611452212366245865349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1492297205899643322307597 559611452212366245865349)
          ·
            refine ⟨104927147289818671099753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 559611452212366245865349 104927147289818671099753)
            ·
              refine ⟨78695360467364003324815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104927147289818671099753 78695360467364003324815)
              ·
                refine ⟨118043040701046004987223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78695360467364003324815 118043040701046004987223)
                ·
                  refine ⟨177064561051569007480835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118043040701046004987223 177064561051569007480835)
                  ·
                    refine ⟨265596841577353511221253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177064561051569007480835 265596841577353511221253)
                    ·
                      refine ⟨49799407795753783353985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 265596841577353511221253 49799407795753783353985)
                      ·
                        rfl

theorem cell23_96984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_96984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_96984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_96984 prefixEnd_96984 := by exact prefixLift 96984
  have htrace : WordTrace (prefixWord ++ tailWord_96984) baseStart_96984 baseEnd_96984 := by
    simpa [prefixWord, tailWord_96984, baseEnd_96984] using wordTrace_append hprefix tailTrace_96984
  have hstable : (prefixWord ++ tailWord_96984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_96984).length < 2 ^ (prefixWord ++ tailWord_96984).sum := by decide
  have hdescent : baseEnd_96984 < baseStart_96984 := by decide
  rcases family_descends (prefixWord ++ tailWord_96984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97017 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 3]
def baseStart_97017 : Nat := 118140960795 + 97017 * 2 ^ 59
def prefixEnd_97017 : Nat := 4983230072969 + 3 ^ 40 * 97017 * 2
def baseEnd_97017 : Nat := 49816352657352154241333

theorem tailTrace_97017 : CollatzResearch.WordTrace tailWord_97017 prefixEnd_97017 49816352657352154241333 := by
  unfold tailWord_97017
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538500689531453029569305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2359000459687635353046203 3538500689531453029569305)
  ·
    refine ⟨2653875517148589772176979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3538500689531453029569305 2653875517148589772176979)
    ·
      refine ⟨3980813275722884658265469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653875517148589772176979 3980813275722884658265469)
      ·
        refine ⟨1492804978396081746849551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3980813275722884658265469 1492804978396081746849551)
        ·
          refine ⟨2239207467594122620274327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492804978396081746849551 2239207467594122620274327)
          ·
            refine ⟨3358811201391183930411491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239207467594122620274327 3358811201391183930411491)
            ·
              refine ⟨5038216802086775895617237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358811201391183930411491 5038216802086775895617237)
              ·
                refine ⟨118083206298908810053529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5038216802086775895617237 118083206298908810053529)
                ·
                  refine ⟨88562404724181607540147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118083206298908810053529 88562404724181607540147)
                  ·
                    refine ⟨132843607086272411310221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88562404724181607540147 132843607086272411310221)
                    ·
                      refine ⟨49816352657352154241333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 132843607086272411310221 49816352657352154241333)
                      ·
                        rfl

theorem cell23_97017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_97017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97017 prefixEnd_97017 := by exact prefixLift 97017
  have htrace : WordTrace (prefixWord ++ tailWord_97017) baseStart_97017 baseEnd_97017 := by
    simpa [prefixWord, tailWord_97017, baseEnd_97017] using wordTrace_append hprefix tailTrace_97017
  have hstable : (prefixWord ++ tailWord_97017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97017).length < 2 ^ (prefixWord ++ tailWord_97017).sum := by decide
  have hdescent : baseEnd_97017 < baseStart_97017 := by decide
  rcases family_descends (prefixWord ++ tailWord_97017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97033 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_97033 : Nat := 118140960795 + 97033 * 2 ^ 59
def prefixEnd_97033 : Nat := 4983230072969 + 3 ^ 40 * 97033 * 2
def baseEnd_97033 : Nat := 16608189449274697213753

theorem tailTrace_97033 : CollatzResearch.WordTrace tailWord_97033 prefixEnd_97033 16608189449274697213753 := by
  unfold tailWord_97033
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539084257473487762151753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2359389504982325174767835 3539084257473487762151753)
  ·
    refine ⟨2654313193105115821613815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3539084257473487762151753 2654313193105115821613815)
    ·
      refine ⟨3981469789657673732420723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2654313193105115821613815 3981469789657673732420723)
      ·
        refine ⟨5972204684486510598631085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981469789657673732420723 5972204684486510598631085)
        ·
          refine ⟨2239576756682441474486657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5972204684486510598631085 2239576756682441474486657)
          ·
            refine ⟨1679682567511831105864993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239576756682441474486657 1679682567511831105864993)
            ·
              refine ⟨1259761925633873329398745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679682567511831105864993 1259761925633873329398745)
              ·
                refine ⟨944821444225404997049059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259761925633873329398745 944821444225404997049059)
                ·
                  refine ⟨1417232166338107495573589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944821444225404997049059 1417232166338107495573589)
                  ·
                    refine ⟨16608189449274697213753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1417232166338107495573589 16608189449274697213753)
                    ·
                      rfl

theorem cell23_97033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_97033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97033 prefixEnd_97033 := by exact prefixLift 97033
  have htrace : WordTrace (prefixWord ++ tailWord_97033) baseStart_97033 baseEnd_97033 := by
    simpa [prefixWord, tailWord_97033, baseEnd_97033] using wordTrace_append hprefix tailTrace_97033
  have hstable : (prefixWord ++ tailWord_97033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97033).length < 2 ^ (prefixWord ++ tailWord_97033).sum := by decide
  have hdescent : baseEnd_97033 < baseStart_97033 := by decide
  rcases family_descends (prefixWord ++ tailWord_97033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97108 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_97108 : Nat := 118140960795 + 97108 * 2 ^ 59
def prefixEnd_97108 : Nat := 4983230072969 + 3 ^ 40 * 97108 * 2
def baseEnd_97108 : Nat := 49863079396911298203415

theorem tailTrace_97108 : CollatzResearch.WordTrace tailWord_97108 prefixEnd_97108 49863079396911298203415 := by
  unfold tailWord_97108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770909866100887785565989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2361213154801183714087985 1770909866100887785565989)
  ·
    refine ⟨332045599893916459793623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1770909866100887785565989 332045599893916459793623)
    ·
      refine ⟨498068399840874689690435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332045599893916459793623 498068399840874689690435)
      ·
        refine ⟨747102599761312034535653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498068399840874689690435 747102599761312034535653)
        ·
          refine ⟨140081737455246006475435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 747102599761312034535653 140081737455246006475435)
          ·
            refine ⟨210122606182869009713153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140081737455246006475435 210122606182869009713153)
            ·
              refine ⟨157591954637151757284865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210122606182869009713153 157591954637151757284865)
              ·
                refine ⟨118193965977863817963649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157591954637151757284865 118193965977863817963649)
                ·
                  refine ⟨88645474483397863472737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118193965977863817963649 88645474483397863472737)
                  ·
                    refine ⟨66484105862548397604553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88645474483397863472737 66484105862548397604553)
                    ·
                      refine ⟨49863079396911298203415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66484105862548397604553 49863079396911298203415)
                      ·
                        rfl

theorem cell23_97108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_97108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97108 prefixEnd_97108 := by exact prefixLift 97108
  have htrace : WordTrace (prefixWord ++ tailWord_97108) baseStart_97108 baseEnd_97108 := by
    simpa [prefixWord, tailWord_97108, baseEnd_97108] using wordTrace_append hprefix tailTrace_97108
  have hstable : (prefixWord ++ tailWord_97108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97108).length < 2 ^ (prefixWord ++ tailWord_97108).sum := by decide
  have hdescent : baseEnd_97108 < baseStart_97108 := by decide
  rcases family_descends (prefixWord ++ tailWord_97108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97114 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_97114 : Nat := 118140960795 + 97114 * 2 ^ 59
def prefixEnd_97114 : Nat := 4983230072969 + 3 ^ 40 * 97114 * 2
def baseEnd_97114 : Nat := 5540684475648697192043

theorem tailTrace_97114 : CollatzResearch.WordTrace tailWord_97114 prefixEnd_97114 5540684475648697192043 := by
  unfold tailWord_97114
  simp only [CollatzResearch.WordTrace]
  refine ⟨885509642545009648962599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2361359046786692397233597 885509642545009648962599)
  ·
    refine ⟨1328264463817514473443899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 885509642545009648962599 1328264463817514473443899)
    ·
      refine ⟨1992396695726271710165849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328264463817514473443899 1992396695726271710165849)
      ·
        refine ⟨1494297521794703782624387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1992396695726271710165849 1494297521794703782624387)
        ·
          refine ⟨2241446282692055673936581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494297521794703782624387 2241446282692055673936581)
          ·
            refine ⟨420271178004760438863109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2241446282692055673936581 420271178004760438863109)
            ·
              refine ⟨78800845875892582286833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 420271178004760438863109 78800845875892582286833)
              ·
                refine ⟨59100634406919436715125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78800845875892582286833 59100634406919436715125)
                ·
                  refine ⟨5540684475648697192043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59100634406919436715125 5540684475648697192043)
                  ·
                    rfl

theorem cell23_97114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_97114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97114 prefixEnd_97114 := by exact prefixLift 97114
  have htrace : WordTrace (prefixWord ++ tailWord_97114) baseStart_97114 baseEnd_97114 := by
    simpa [prefixWord, tailWord_97114, baseEnd_97114] using wordTrace_append hprefix tailTrace_97114
  have hstable : (prefixWord ++ tailWord_97114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97114).length < 2 ^ (prefixWord ++ tailWord_97114).sum := by decide
  have hdescent : baseEnd_97114 < baseStart_97114 := by decide
  rcases family_descends (prefixWord ++ tailWord_97114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97120 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_97120 : Nat := 118140960795 + 97120 * 2 ^ 59
def prefixEnd_97120 : Nat := 4983230072969 + 3 ^ 40 * 97120 * 2
def baseEnd_97120 : Nat := 49869241164765251253359

theorem tailTrace_97120 : CollatzResearch.WordTrace tailWord_97120 prefixEnd_97120 49869241164765251253359 := by
  unfold tailWord_97120
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771128704079150810284407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2361504938772201080379209 1771128704079150810284407)
  ·
    refine ⟨2656693056118726215426611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771128704079150810284407 2656693056118726215426611)
    ·
      refine ⟨3985039584178089323139917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656693056118726215426611 3985039584178089323139917)
      ·
        refine ⟨1494389844066783496177469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3985039584178089323139917 1494389844066783496177469)
        ·
          refine ⟨560396191525043811066551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1494389844066783496177469 560396191525043811066551)
          ·
            refine ⟨840594287287565716599827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560396191525043811066551 840594287287565716599827)
            ·
              refine ⟨1260891430931348574899741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840594287287565716599827 1260891430931348574899741)
              ·
                refine ⟨472834286599255715587403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1260891430931348574899741 472834286599255715587403)
                ·
                  refine ⟨709251429898883573381105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472834286599255715587403 709251429898883573381105)
                  ·
                    refine ⟨531938572424162680035829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 709251429898883573381105 531938572424162680035829)
                    ·
                      refine ⟨49869241164765251253359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 531938572424162680035829 49869241164765251253359)
                      ·
                        rfl

theorem cell23_97120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_97120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97120 prefixEnd_97120 := by exact prefixLift 97120
  have htrace : WordTrace (prefixWord ++ tailWord_97120) baseStart_97120 baseEnd_97120 := by
    simpa [prefixWord, tailWord_97120, baseEnd_97120] using wordTrace_append hprefix tailTrace_97120
  have hstable : (prefixWord ++ tailWord_97120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97120).length < 2 ^ (prefixWord ++ tailWord_97120).sum := by decide
  have hdescent : baseEnd_97120 < baseStart_97120 := by decide
  rcases family_descends (prefixWord ++ tailWord_97120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97147 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 4]
def baseStart_97147 : Nat := 118140960795 + 97147 * 2 ^ 59
def prefixEnd_97147 : Nat := 4983230072969 + 3 ^ 40 * 97147 * 2
def baseEnd_97147 : Nat := 49883105142436645615735

theorem tailTrace_97147 : CollatzResearch.WordTrace tailWord_97147 prefixEnd_97147 49883105142436645615735 := by
  unfold tailWord_97147
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543242179060485231801695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2362161452706990154534463 3543242179060485231801695)
  ·
    refine ⟨5314863268590727847702543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543242179060485231801695 5314863268590727847702543)
    ·
      refine ⟨7972294902886091771553815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314863268590727847702543 7972294902886091771553815)
      ·
        refine ⟨11958442354329137657330723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7972294902886091771553815 11958442354329137657330723)
        ·
          refine ⟨17937663531493706485996085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11958442354329137657330723 17937663531493706485996085)
          ·
            refine ⟨1681655956077534983062133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17937663531493706485996085 1681655956077534983062133)
            ·
              refine ⟨157655245882268904662075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1681655956077534983062133 157655245882268904662075)
              ·
                refine ⟨236482868823403356993113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157655245882268904662075 236482868823403356993113)
                ·
                  refine ⟨177362151617552517744835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236482868823403356993113 177362151617552517744835)
                  ·
                    refine ⟨266043227426328776617253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177362151617552517744835 266043227426328776617253)
                    ·
                      refine ⟨49883105142436645615735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 266043227426328776617253 49883105142436645615735)
                      ·
                        rfl

theorem cell23_97147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 4].length) (baseStart_97147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97147 prefixEnd_97147 := by exact prefixLift 97147
  have htrace : WordTrace (prefixWord ++ tailWord_97147) baseStart_97147 baseEnd_97147 := by
    simpa [prefixWord, tailWord_97147, baseEnd_97147] using wordTrace_append hprefix tailTrace_97147
  have hstable : (prefixWord ++ tailWord_97147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97147).length < 2 ^ (prefixWord ++ tailWord_97147).sum := by decide
  have hdescent : baseEnd_97147 < baseStart_97147 := by decide
  rcases family_descends (prefixWord ++ tailWord_97147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97204 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 8]
def baseStart_97204 : Nat := 118140960795 + 97204 * 2 ^ 59
def prefixEnd_97204 : Nat := 4983230072969 + 3 ^ 40 * 97204 * 2
def baseEnd_97204 : Nat := 5545819282193658066997

theorem tailTrace_97204 : CollatzResearch.WordTrace tailWord_97204 prefixEnd_97204 5545819282193658066997 := by
  unfold tailWord_97204
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772660569926991983313333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2363547426569322644417777 1772660569926991983313333)
  ·
    refine ⟨166186928430655498435625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1772660569926991983313333 166186928430655498435625)
    ·
      refine ⟨124640196322991623826719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166186928430655498435625 124640196322991623826719)
      ·
        refine ⟨186960294484487435740079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124640196322991623826719 186960294484487435740079)
        ·
          refine ⟨280440441726731153610119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186960294484487435740079 280440441726731153610119)
          ·
            refine ⟨420660662590096730415179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280440441726731153610119 420660662590096730415179)
            ·
              refine ⟨630990993885145095622769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420660662590096730415179 630990993885145095622769)
              ·
                refine ⟨473243245413858821717077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630990993885145095622769 473243245413858821717077)
                ·
                  refine ⟨5545819282193658066997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 473243245413858821717077 5545819282193658066997)
                  ·
                    rfl

theorem cell23_97204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_97204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97204 prefixEnd_97204 := by exact prefixLift 97204
  have htrace : WordTrace (prefixWord ++ tailWord_97204) baseStart_97204 baseEnd_97204 := by
    simpa [prefixWord, tailWord_97204, baseEnd_97204] using wordTrace_append hprefix tailTrace_97204
  have hstable : (prefixWord ++ tailWord_97204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97204).length < 2 ^ (prefixWord ++ tailWord_97204).sum := by decide
  have hdescent : baseEnd_97204 < baseStart_97204 := by decide
  rcases family_descends (prefixWord ++ tailWord_97204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97231 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 3]
def baseStart_97231 : Nat := 118140960795 + 97231 * 2 ^ 59
def prefixEnd_97231 : Nat := 4983230072969 + 3 ^ 40 * 97231 * 2
def baseEnd_97231 : Nat := 49926237517414316965349

theorem tailTrace_97231 : CollatzResearch.WordTrace tailWord_97231 prefixEnd_97231 49926237517414316965349 := by
  unfold tailWord_97231
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546305910756167577859547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2364203940504111718573031 3546305910756167577859547)
  ·
    refine ⟨5319458866134251366789321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3546305910756167577859547 5319458866134251366789321)
    ·
      refine ⟨3989594149600688525091991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5319458866134251366789321 3989594149600688525091991)
      ·
        refine ⟨5984391224401032787637987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3989594149600688525091991 5984391224401032787637987)
        ·
          refine ⟨8976586836601549181456981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984391224401032787637987 8976586836601549181456981)
          ·
            refine ⟨105194376991424404470199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 8976586836601549181456981 105194376991424404470199)
            ·
              refine ⟨157791565487136606705299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105194376991424404470199 157791565487136606705299)
              ·
                refine ⟨236687348230704910057949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157791565487136606705299 236687348230704910057949)
                ·
                  refine ⟨88757755586514341271731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236687348230704910057949 88757755586514341271731)
                  ·
                    refine ⟨133136633379771511907597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88757755586514341271731 133136633379771511907597)
                    ·
                      refine ⟨49926237517414316965349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133136633379771511907597 49926237517414316965349)
                      ·
                        rfl

theorem cell23_97231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_97231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97231 prefixEnd_97231 := by exact prefixLift 97231
  have htrace : WordTrace (prefixWord ++ tailWord_97231) baseStart_97231 baseEnd_97231 := by
    simpa [prefixWord, tailWord_97231, baseEnd_97231] using wordTrace_append hprefix tailTrace_97231
  have hstable : (prefixWord ++ tailWord_97231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97231).length < 2 ^ (prefixWord ++ tailWord_97231).sum := by decide
  have hdescent : baseEnd_97231 < baseStart_97231 := by decide
  rcases family_descends (prefixWord ++ tailWord_97231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97238 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_97238 : Nat := 118140960795 + 97238 * 2 ^ 59
def prefixEnd_97238 : Nat := 4983230072969 + 3 ^ 40 * 97238 * 2
def baseEnd_97238 : Nat := 5547759097999532175313

theorem tailTrace_97238 : CollatzResearch.WordTrace tailWord_97238 prefixEnd_97238 5547759097999532175313 := by
  unfold tailWord_97238
  simp only [CollatzResearch.WordTrace]
  refine ⟨221660076358175485835273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2364374147820538515576245 221660076358175485835273)
  ·
    refine ⟨166245057268631614376455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221660076358175485835273 166245057268631614376455)
    ·
      refine ⟨249367585902947421564683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166245057268631614376455 249367585902947421564683)
      ·
        refine ⟨374051378854421132347025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249367585902947421564683 374051378854421132347025)
        ·
          refine ⟨280538534140815849260269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374051378854421132347025 280538534140815849260269)
          ·
            refine ⟨105201950302805943472601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280538534140815849260269 105201950302805943472601)
            ·
              refine ⟨78901462727104457604451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105201950302805943472601 78901462727104457604451)
              ·
                refine ⟨118352194090656686406677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78901462727104457604451 118352194090656686406677)
                ·
                  refine ⟨5547759097999532175313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118352194090656686406677 5547759097999532175313)
                  ·
                    rfl

theorem cell23_97238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_97238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97238 prefixEnd_97238 := by exact prefixLift 97238
  have htrace : WordTrace (prefixWord ++ tailWord_97238) baseStart_97238 baseEnd_97238 := by
    simpa [prefixWord, tailWord_97238, baseEnd_97238] using wordTrace_append hprefix tailTrace_97238
  have hstable : (prefixWord ++ tailWord_97238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97238).length < 2 ^ (prefixWord ++ tailWord_97238).sum := by decide
  have hdescent : baseEnd_97238 < baseStart_97238 := by decide
  rcases family_descends (prefixWord ++ tailWord_97238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97274 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_97274 : Nat := 118140960795 + 97274 * 2 ^ 59
def prefixEnd_97274 : Nat := 4983230072969 + 3 ^ 40 * 97274 * 2
def baseEnd_97274 : Nat := 49948317185557648727651

theorem tailTrace_97274 : CollatzResearch.WordTrace tailWord_97274 prefixEnd_97274 49948317185557648727651 := by
  unfold tailWord_97274
  simp only [CollatzResearch.WordTrace]
  refine ⟨886968562400096480418719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2365249499733590614449917 886968562400096480418719)
  ·
    refine ⟨1330452843600144720628079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886968562400096480418719 1330452843600144720628079)
    ·
      refine ⟨1995679265400217080942119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330452843600144720628079 1995679265400217080942119)
      ·
        refine ⟨2993518898100325621413179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995679265400217080942119 2993518898100325621413179)
        ·
          refine ⟨4490278347150488432119769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993518898100325621413179 4490278347150488432119769)
          ·
            refine ⟨3367708760362866324089827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490278347150488432119769 3367708760362866324089827)
            ·
              refine ⟨5051563140544299486134741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367708760362866324089827 5051563140544299486134741)
              ·
                refine ⟨118396011106507019206283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5051563140544299486134741 118396011106507019206283)
                ·
                  refine ⟨177594016659760528809425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118396011106507019206283 177594016659760528809425)
                  ·
                    refine ⟨133195512494820396607069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177594016659760528809425 133195512494820396607069)
                    ·
                      refine ⟨49948317185557648727651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133195512494820396607069 49948317185557648727651)
                      ·
                        rfl

theorem cell23_97274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_97274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97274 prefixEnd_97274 := by exact prefixLift 97274
  have htrace : WordTrace (prefixWord ++ tailWord_97274) baseStart_97274 baseEnd_97274 := by
    simpa [prefixWord, tailWord_97274, baseEnd_97274] using wordTrace_append hprefix tailTrace_97274
  have hstable : (prefixWord ++ tailWord_97274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97274).length < 2 ^ (prefixWord ++ tailWord_97274).sum := by decide
  have hdescent : baseEnd_97274 < baseStart_97274 := by decide
  rcases family_descends (prefixWord ++ tailWord_97274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97281 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 2, 4]
def baseStart_97281 : Nat := 118140960795 + 97281 * 2 ^ 59
def prefixEnd_97281 : Nat := 4983230072969 + 3 ^ 40 * 97281 * 2
def baseEnd_97281 : Nat := 16650637183379707113373

theorem tailTrace_97281 : CollatzResearch.WordTrace tailWord_97281 prefixEnd_97281 16650637183379707113373 := by
  unfold tailWord_97281
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548129560575026117179697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2365419707050017411453131 3548129560575026117179697)
  ·
    refine ⟨2661097170431269587884773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3548129560575026117179697 2661097170431269587884773)
    ·
      refine ⟨498955719455863047728395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2661097170431269587884773 498955719455863047728395)
      ·
        refine ⟨748433579183794571592593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498955719455863047728395 748433579183794571592593)
        ·
          refine ⟨561325184387845928694445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748433579183794571592593 561325184387845928694445)
          ·
            refine ⟨210496944145442223260417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561325184387845928694445 210496944145442223260417)
            ·
              refine ⟨157872708109081667445313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210496944145442223260417 157872708109081667445313)
              ·
                refine ⟨118404531081811250583985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157872708109081667445313 118404531081811250583985)
                ·
                  refine ⟨88803398311358437937989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118404531081811250583985 88803398311358437937989)
                  ·
                    refine ⟨16650637183379707113373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88803398311358437937989 16650637183379707113373)
                    ·
                      rfl

theorem cell23_97281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_97281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97281 prefixEnd_97281 := by exact prefixLift 97281
  have htrace : WordTrace (prefixWord ++ tailWord_97281) baseStart_97281 baseEnd_97281 := by
    simpa [prefixWord, tailWord_97281, baseEnd_97281] using wordTrace_append hprefix tailTrace_97281
  have hstable : (prefixWord ++ tailWord_97281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97281).length < 2 ^ (prefixWord ++ tailWord_97281).sum := by decide
  have hdescent : baseEnd_97281 < baseStart_97281 := by decide
  rcases family_descends (prefixWord ++ tailWord_97281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97282 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_97282 : Nat := 118140960795 + 97282 * 2 ^ 59
def prefixEnd_97282 : Nat := 4983230072969 + 3 ^ 40 * 97282 * 2
def baseEnd_97282 : Nat := 49952425030793617427615

theorem tailTrace_97282 : CollatzResearch.WordTrace tailWord_97282 prefixEnd_97282 49952425030793617427615 := by
  unfold tailWord_97282
  simp only [CollatzResearch.WordTrace]
  refine ⟨887041508392850821991525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2365444022380935525310733 887041508392850821991525)
  ·
    refine ⟨166320282823659529123411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 887041508392850821991525 166320282823659529123411)
    ·
      refine ⟨249480424235489293685117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166320282823659529123411 249480424235489293685117)
      ·
        refine ⟨93555159088308485131919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249480424235489293685117 93555159088308485131919)
        ·
          refine ⟨140332738632462727697879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93555159088308485131919 140332738632462727697879)
          ·
            refine ⟨210499107948694091546819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140332738632462727697879 210499107948694091546819)
            ·
              refine ⟨315748661923041137320229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210499107948694091546819 315748661923041137320229)
              ·
                refine ⟨59202874110570213247543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315748661923041137320229 59202874110570213247543)
                ·
                  refine ⟨88804311165855319871315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59202874110570213247543 88804311165855319871315)
                  ·
                    refine ⟨133206466748782979806973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88804311165855319871315 133206466748782979806973)
                    ·
                      refine ⟨49952425030793617427615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133206466748782979806973 49952425030793617427615)
                      ·
                        rfl

theorem cell23_97282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_97282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97282 prefixEnd_97282 := by exact prefixLift 97282
  have htrace : WordTrace (prefixWord ++ tailWord_97282) baseStart_97282 baseEnd_97282 := by
    simpa [prefixWord, tailWord_97282, baseEnd_97282] using wordTrace_append hprefix tailTrace_97282
  have hstable : (prefixWord ++ tailWord_97282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97282).length < 2 ^ (prefixWord ++ tailWord_97282).sum := by decide
  have hdescent : baseEnd_97282 < baseStart_97282 := by decide
  rcases family_descends (prefixWord ++ tailWord_97282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97294 : List Nat := [4, 1, 1, 2, 2, 4, 1, 8]
def baseStart_97294 : Nat := 118140960795 + 97294 * 2 ^ 59
def prefixEnd_97294 : Nat := 4983230072969 + 3 ^ 40 * 97294 * 2
def baseEnd_97294 : Nat := 1850318029579539647317

theorem tailTrace_97294 : CollatzResearch.WordTrace tailWord_97294 prefixEnd_97294 1850318029579539647317 := by
  unfold tailWord_97294
  simp only [CollatzResearch.WordTrace]
  refine ⟨443575463690991167175367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2365735806351952891601957 443575463690991167175367)
  ·
    refine ⟨665363195536486750763051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 443575463690991167175367 665363195536486750763051)
    ·
      refine ⟨998044793304730126144577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665363195536486750763051 998044793304730126144577)
      ·
        refine ⟨748533594978547594608433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 998044793304730126144577 748533594978547594608433)
        ·
          refine ⟨561400196233910695956325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748533594978547594608433 561400196233910695956325)
          ·
            refine ⟨105262536793858255491811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 561400196233910695956325 105262536793858255491811)
            ·
              refine ⟨157893805190787383237717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105262536793858255491811 157893805190787383237717)
              ·
                refine ⟨1850318029579539647317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 157893805190787383237717 1850318029579539647317)
                ·
                  rfl

theorem cell23_97294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_97294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97294 prefixEnd_97294 := by exact prefixLift 97294
  have htrace : WordTrace (prefixWord ++ tailWord_97294) baseStart_97294 baseEnd_97294 := by
    simpa [prefixWord, tailWord_97294, baseEnd_97294] using wordTrace_append hprefix tailTrace_97294
  have hstable : (prefixWord ++ tailWord_97294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97294).length < 2 ^ (prefixWord ++ tailWord_97294).sum := by decide
  have hdescent : baseEnd_97294 < baseStart_97294 := by decide
  rcases family_descends (prefixWord ++ tailWord_97294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97304 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_97304 : Nat := 118140960795 + 97304 * 2 ^ 59
def prefixEnd_97304 : Nat := 4983230072969 + 3 ^ 40 * 97304 * 2
def baseEnd_97304 : Nat := 49963721605192531352513

theorem tailTrace_97304 : CollatzResearch.WordTrace tailWord_97304 prefixEnd_97304 49963721605192531352513 := by
  unfold tailWord_97304
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774484219745850522633483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2365978959661134030177977 1774484219745850522633483)
  ·
    refine ⟨2661726329618775783950225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1774484219745850522633483 2661726329618775783950225)
    ·
      refine ⟨1996294747214081837962669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2661726329618775783950225 1996294747214081837962669)
      ·
        refine ⟨748610530205280689236001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1996294747214081837962669 748610530205280689236001)
        ·
          refine ⟨561457897653960516927001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748610530205280689236001 561457897653960516927001)
          ·
            refine ⟨421093423240470387695251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561457897653960516927001 421093423240470387695251)
            ·
              refine ⟨631640134860705581542877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421093423240470387695251 631640134860705581542877)
              ·
                refine ⟨236865050572764593078579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631640134860705581542877 236865050572764593078579)
                ·
                  refine ⟨355297575859146889617869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236865050572764593078579 355297575859146889617869)
                  ·
                    refine ⟨133236590947180083606701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355297575859146889617869 133236590947180083606701)
                    ·
                      refine ⟨49963721605192531352513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133236590947180083606701 49963721605192531352513)
                      ·
                        rfl

theorem cell23_97304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_97304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97304 prefixEnd_97304 := by exact prefixLift 97304
  have htrace : WordTrace (prefixWord ++ tailWord_97304) baseStart_97304 baseEnd_97304 := by
    simpa [prefixWord, tailWord_97304, baseEnd_97304] using wordTrace_append hprefix tailTrace_97304
  have hstable : (prefixWord ++ tailWord_97304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97304).length < 2 ^ (prefixWord ++ tailWord_97304).sum := by decide
  have hdescent : baseEnd_97304 < baseStart_97304 := by decide
  rcases family_descends (prefixWord ++ tailWord_97304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97317 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_97317 : Nat := 118140960795 + 97317 * 2 ^ 59
def prefixEnd_97317 : Nat := 4983230072969 + 3 ^ 40 * 97317 * 2
def baseEnd_97317 : Nat := 49970396853700980489953

theorem tailTrace_97317 : CollatzResearch.WordTrace tailWord_97317 prefixEnd_97317 49970396853700980489953 := by
  unfold tailWord_97317
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549442588444604265490205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2366295058963069510326803 3549442588444604265490205)
  ·
    refine ⟨1331040970666726599558827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3549442588444604265490205 1331040970666726599558827)
    ·
      refine ⟨1996561456000089899338241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331040970666726599558827 1996561456000089899338241)
      ·
        refine ⟨1497421092000067424503681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1996561456000089899338241 1497421092000067424503681)
        ·
          refine ⟨1123065819000050568377761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1497421092000067424503681 1123065819000050568377761)
          ·
            refine ⟨842299364250037926283321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123065819000050568377761 842299364250037926283321)
            ·
              refine ⟨631724523187528444712491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842299364250037926283321 631724523187528444712491)
              ·
                refine ⟨947586784781292667068737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631724523187528444712491 947586784781292667068737)
                ·
                  refine ⟨710690088585969500301553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 947586784781292667068737 710690088585969500301553)
                  ·
                    refine ⟨533017566439477125226165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 710690088585969500301553 533017566439477125226165)
                    ·
                      refine ⟨49970396853700980489953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 533017566439477125226165 49970396853700980489953)
                      ·
                        rfl

theorem cell23_97317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_97317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97317 prefixEnd_97317 := by exact prefixLift 97317
  have htrace : WordTrace (prefixWord ++ tailWord_97317) baseStart_97317 baseEnd_97317 := by
    simpa [prefixWord, tailWord_97317, baseEnd_97317] using wordTrace_append hprefix tailTrace_97317
  have hstable : (prefixWord ++ tailWord_97317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97317).length < 2 ^ (prefixWord ++ tailWord_97317).sum := by decide
  have hdescent : baseEnd_97317 < baseStart_97317 := by decide
  rcases family_descends (prefixWord ++ tailWord_97317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97322 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_97322 : Nat := 118140960795 + 97322 * 2 ^ 59
def prefixEnd_97322 : Nat := 4983230072969 + 3 ^ 40 * 97322 * 2
def baseEnd_97322 : Nat := 49972964256973460927431

theorem tailTrace_97322 : CollatzResearch.WordTrace tailWord_97322 prefixEnd_97322 49972964256973460927431 := by
  unfold tailWord_97322
  simp only [CollatzResearch.WordTrace]
  refine ⟨887406238356622529855555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2366416635617660079614813 887406238356622529855555)
  ·
    refine ⟨1331109357534933794783333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887406238356622529855555 1331109357534933794783333)
    ·
      refine ⟨249583004537800086521875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1331109357534933794783333 249583004537800086521875)
      ·
        refine ⟨374374506806700129782813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249583004537800086521875 374374506806700129782813)
        ·
          refine ⟨140390440052512548668555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374374506806700129782813 140390440052512548668555)
          ·
            refine ⟨210585660078768823002833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140390440052512548668555 210585660078768823002833)
            ·
              refine ⟨157939245059076617252125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210585660078768823002833 157939245059076617252125)
              ·
                refine ⟨59227216897153731469547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157939245059076617252125 59227216897153731469547)
                ·
                  refine ⟨88840825345730597204321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59227216897153731469547 88840825345730597204321)
                  ·
                    refine ⟨66630619009297947903241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88840825345730597204321 66630619009297947903241)
                    ·
                      refine ⟨49972964256973460927431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66630619009297947903241 49972964256973460927431)
                      ·
                        rfl

theorem cell23_97322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_97322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97322 prefixEnd_97322 := by exact prefixLift 97322
  have htrace : WordTrace (prefixWord ++ tailWord_97322) baseStart_97322 baseEnd_97322 := by
    simpa [prefixWord, tailWord_97322, baseEnd_97322] using wordTrace_append hprefix tailTrace_97322
  have hstable : (prefixWord ++ tailWord_97322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97322).length < 2 ^ (prefixWord ++ tailWord_97322).sum := by decide
  have hdescent : baseEnd_97322 < baseStart_97322 := by decide
  rcases family_descends (prefixWord ++ tailWord_97322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97361 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 1, 4, 2]
def baseStart_97361 : Nat := 118140960795 + 97361 * 2 ^ 59
def prefixEnd_97361 : Nat := 4983230072969 + 3 ^ 40 * 97361 * 2
def baseEnd_97361 : Nat := 49992990002498808339751

theorem tailTrace_97361 : CollatzResearch.WordTrace tailWord_97361 prefixEnd_97361 49992990002498808339751 := by
  unfold tailWord_97361
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551047400285199780091937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2367364933523466520061291 3551047400285199780091937)
  ·
    refine ⟨2663285550213899835068953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3551047400285199780091937 2663285550213899835068953)
    ·
      refine ⟨1997464162660424876301715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2663285550213899835068953 1997464162660424876301715)
      ·
        refine ⟨2996196243990637314452573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997464162660424876301715 2996196243990637314452573)
        ·
          refine ⟨1123573591496488992919715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2996196243990637314452573 1123573591496488992919715)
          ·
            refine ⟨1685360387244733489379573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123573591496488992919715 1685360387244733489379573)
            ·
              refine ⟨158002536304193764629335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1685360387244733489379573 158002536304193764629335)
              ·
                refine ⟨237003804456290646944003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158002536304193764629335 237003804456290646944003)
                ·
                  refine ⟨355505706684435970416005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237003804456290646944003 355505706684435970416005)
                  ·
                    refine ⟨66657320003331744453001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355505706684435970416005 66657320003331744453001)
                    ·
                      refine ⟨49992990002498808339751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66657320003331744453001 49992990002498808339751)
                      ·
                        rfl

theorem cell23_97361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_97361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97361 prefixEnd_97361 := by exact prefixLift 97361
  have htrace : WordTrace (prefixWord ++ tailWord_97361) baseStart_97361 baseEnd_97361 := by
    simpa [prefixWord, tailWord_97361, baseEnd_97361] using wordTrace_append hprefix tailTrace_97361
  have hstable : (prefixWord ++ tailWord_97361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97361).length < 2 ^ (prefixWord ++ tailWord_97361).sum := by decide
  have hdescent : baseEnd_97361 < baseStart_97361 := by decide
  rcases family_descends (prefixWord ++ tailWord_97361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97364 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_97364 : Nat := 118140960795 + 97364 * 2 ^ 59
def prefixEnd_97364 : Nat := 4983230072969 + 3 ^ 40 * 97364 * 2
def baseEnd_97364 : Nat := 49994530444462296602237

theorem tailTrace_97364 : CollatzResearch.WordTrace tailWord_97364 prefixEnd_97364 49994530444462296602237 := by
  unfold tailWord_97364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775578409637165646225573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2367437879516220861634097 1775578409637165646225573)
  ·
    refine ⟨332920951806968558667295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1775578409637165646225573 332920951806968558667295)
    ·
      refine ⟨499381427710452838000943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332920951806968558667295 499381427710452838000943)
      ·
        refine ⟨749072141565679257001415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499381427710452838000943 749072141565679257001415)
        ·
          refine ⟨1123608212348518885502123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749072141565679257001415 1123608212348518885502123)
          ·
            refine ⟨1685412318522778328253185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123608212348518885502123 1685412318522778328253185)
            ·
              refine ⟨1264059238892083746189889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685412318522778328253185 1264059238892083746189889)
              ·
                refine ⟨948044429169062809642417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264059238892083746189889 948044429169062809642417)
                ·
                  refine ⟨711033321876797107231813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 948044429169062809642417 711033321876797107231813)
                  ·
                    refine ⟨133318747851899457605965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 711033321876797107231813 133318747851899457605965)
                    ·
                      refine ⟨49994530444462296602237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133318747851899457605965 49994530444462296602237)
                      ·
                        rfl

theorem cell23_97364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_97364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97364 prefixEnd_97364 := by exact prefixLift 97364
  have htrace : WordTrace (prefixWord ++ tailWord_97364) baseStart_97364 baseEnd_97364 := by
    simpa [prefixWord, tailWord_97364, baseEnd_97364] using wordTrace_append hprefix tailTrace_97364
  have hstable : (prefixWord ++ tailWord_97364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97364).length < 2 ^ (prefixWord ++ tailWord_97364).sum := by decide
  have hdescent : baseEnd_97364 < baseStart_97364 := by decide
  rcases family_descends (prefixWord ++ tailWord_97364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97401 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 7]
def baseStart_97401 : Nat := 118140960795 + 97401 * 2 ^ 59
def prefixEnd_97401 : Nat := 4983230072969 + 3 ^ 40 * 97401 * 2
def baseEnd_97401 : Nat := 5557058803186516871063

theorem tailTrace_97401 : CollatzResearch.WordTrace tailWord_97401 prefixEnd_97401 5557058803186516871063 := by
  unfold tailWord_97401
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552506320140286611548057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2368337546760191074365371 3552506320140286611548057)
  ·
    refine ⟨2664379740105214958661043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3552506320140286611548057 2664379740105214958661043)
    ·
      refine ⟨3996569610157822437991565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664379740105214958661043 3996569610157822437991565)
      ·
        refine ⟨1498713603809183414246837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3996569610157822437991565 1498713603809183414246837)
        ·
          refine ⟨140504400357110945085641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1498713603809183414246837 140504400357110945085641)
          ·
            refine ⟨105378300267833208814231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140504400357110945085641 105378300267833208814231)
            ·
              refine ⟨158067450401749813221347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105378300267833208814231 158067450401749813221347)
              ·
                refine ⟨237101175602624719832021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158067450401749813221347 237101175602624719832021)
                ·
                  refine ⟨5557058803186516871063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 237101175602624719832021 5557058803186516871063)
                  ·
                    rfl

theorem cell23_97401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_97401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97401 prefixEnd_97401 := by exact prefixLift 97401
  have htrace : WordTrace (prefixWord ++ tailWord_97401) baseStart_97401 baseEnd_97401 := by
    simpa [prefixWord, tailWord_97401, baseEnd_97401] using wordTrace_append hprefix tailTrace_97401
  have hstable : (prefixWord ++ tailWord_97401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97401).length < 2 ^ (prefixWord ++ tailWord_97401).sum := by decide
  have hdescent : baseEnd_97401 < baseStart_97401 := by decide
  rcases family_descends (prefixWord ++ tailWord_97401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97406 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_97406 : Nat := 118140960795 + 97406 * 2 ^ 59
def prefixEnd_97406 : Nat := 4983230072969 + 3 ^ 40 * 97406 * 2
def baseEnd_97406 : Nat := 50016096631951132277045

theorem tailTrace_97406 : CollatzResearch.WordTrace tailWord_97406 prefixEnd_97406 50016096631951132277045 := by
  unfold tailWord_97406
  simp only [CollatzResearch.WordTrace]
  refine ⟨444086085640271558185009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2368459123414781643653381 444086085640271558185009)
  ·
    refine ⟨333064564230203668638757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 444086085640271558185009 333064564230203668638757)
    ·
      refine ⟨62449605793163187869767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333064564230203668638757 62449605793163187869767)
      ·
        refine ⟨93674408689744781804651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62449605793163187869767 93674408689744781804651)
        ·
          refine ⟨140511613034617172706977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93674408689744781804651 140511613034617172706977)
          ·
            refine ⟨105383709775962879530233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140511613034617172706977 105383709775962879530233)
            ·
              refine ⟨79037782331972159647675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105383709775962879530233 79037782331972159647675)
              ·
                refine ⟨118556673497958239471513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79037782331972159647675 118556673497958239471513)
                ·
                  refine ⟨88917505123468679603635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118556673497958239471513 88917505123468679603635)
                  ·
                    refine ⟨133376257685203019405453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88917505123468679603635 133376257685203019405453)
                    ·
                      refine ⟨50016096631951132277045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133376257685203019405453 50016096631951132277045)
                      ·
                        rfl

theorem cell23_97406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_97406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97406 prefixEnd_97406 := by exact prefixLift 97406
  have htrace : WordTrace (prefixWord ++ tailWord_97406) baseStart_97406 baseEnd_97406 := by
    simpa [prefixWord, tailWord_97406, baseEnd_97406] using wordTrace_append hprefix tailTrace_97406
  have hstable : (prefixWord ++ tailWord_97406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97406).length < 2 ^ (prefixWord ++ tailWord_97406).sum := by decide
  have hdescent : baseEnd_97406 < baseStart_97406 := by decide
  rcases family_descends (prefixWord ++ tailWord_97406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97412 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_97412 : Nat := 118140960795 + 97412 * 2 ^ 59
def prefixEnd_97412 : Nat := 4983230072969 + 3 ^ 40 * 97412 * 2
def baseEnd_97412 : Nat := 50019177515878108802017

theorem tailTrace_97412 : CollatzResearch.WordTrace tailWord_97412 prefixEnd_97412 50019177515878108802017 := by
  unfold tailWord_97412
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776453761550217745099245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2368605015400290326798993 1776453761550217745099245)
  ·
    refine ⟨666170160581331654412217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1776453761550217745099245 666170160581331654412217)
    ·
      refine ⟨499627620435998740809163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666170160581331654412217 499627620435998740809163)
      ·
        refine ⟨749441430653998111213745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499627620435998740809163 749441430653998111213745)
        ·
          refine ⟨562081072990498583410309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749441430653998111213745 562081072990498583410309)
          ·
            refine ⟨105390201185718484389433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 562081072990498583410309 105390201185718484389433)
            ·
              refine ⟨79042650889288863292075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105390201185718484389433 79042650889288863292075)
              ·
                refine ⟨118563976333933294938113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79042650889288863292075 118563976333933294938113)
                ·
                  refine ⟨88922982250449971203585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118563976333933294938113 88922982250449971203585)
                  ·
                    refine ⟨66692236687837478402689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88922982250449971203585 66692236687837478402689)
                    ·
                      refine ⟨50019177515878108802017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66692236687837478402689 50019177515878108802017)
                      ·
                        rfl

theorem cell23_97412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_97412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97412 prefixEnd_97412 := by exact prefixLift 97412
  have htrace : WordTrace (prefixWord ++ tailWord_97412) baseStart_97412 baseEnd_97412 := by
    simpa [prefixWord, tailWord_97412, baseEnd_97412] using wordTrace_append hprefix tailTrace_97412
  have hstable : (prefixWord ++ tailWord_97412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97412).length < 2 ^ (prefixWord ++ tailWord_97412).sum := by decide
  have hdescent : baseEnd_97412 < baseStart_97412 := by decide
  rcases family_descends (prefixWord ++ tailWord_97412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97427 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 8]
def baseStart_97427 : Nat := 118140960795 + 97427 * 2 ^ 59
def prefixEnd_97427 : Nat := 4983230072969 + 3 ^ 40 * 97427 * 2
def baseEnd_97427 : Nat := 16675626575231850038149

theorem tailTrace_97427 : CollatzResearch.WordTrace tailWord_97427 prefixEnd_97427 16675626575231850038149 := by
  unfold tailWord_97427
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553454618046093051994535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2368969745364062034663023 3553454618046093051994535)
  ·
    refine ⟨5330181927069139577991803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553454618046093051994535 5330181927069139577991803)
    ·
      refine ⟨7995272890603709366987705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330181927069139577991803 7995272890603709366987705)
      ·
        refine ⟨5996454667952782025240779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7995272890603709366987705 5996454667952782025240779)
        ·
          refine ⟨8994682001929173037861169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996454667952782025240779 8994682001929173037861169)
          ·
            refine ⟨6746011501446879778395877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8994682001929173037861169 6746011501446879778395877)
            ·
              refine ⟨1264877156521289958449227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6746011501446879778395877 1264877156521289958449227)
              ·
                refine ⟨1897315734781934937673841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264877156521289958449227 1897315734781934937673841)
                ·
                  refine ⟨1422986801086451203255381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897315734781934937673841 1422986801086451203255381)
                  ·
                    refine ⟨16675626575231850038149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1422986801086451203255381 16675626575231850038149)
                    ·
                      rfl

theorem cell23_97427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_97427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97427 prefixEnd_97427 := by exact prefixLift 97427
  have htrace : WordTrace (prefixWord ++ tailWord_97427) baseStart_97427 baseEnd_97427 := by
    simpa [prefixWord, tailWord_97427, baseEnd_97427] using wordTrace_append hprefix tailTrace_97427
  have hstable : (prefixWord ++ tailWord_97427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97427).length < 2 ^ (prefixWord ++ tailWord_97427).sum := by decide
  have hdescent : baseEnd_97427 < baseStart_97427 := by decide
  rcases family_descends (prefixWord ++ tailWord_97427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97431 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 2, 5]
def baseStart_97431 : Nat := 118140960795 + 97431 * 2 ^ 59
def prefixEnd_97431 : Nat := 4983230072969 + 3 ^ 40 * 97431 * 2
def baseEnd_97431 : Nat := 16676311216104511488143

theorem tailTrace_97431 : CollatzResearch.WordTrace tailWord_97431 prefixEnd_97431 16676311216104511488143 := by
  unfold tailWord_97431
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553600510031601735140147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2369067006687734490093431 3553600510031601735140147)
  ·
    refine ⟨5330400765047402602710221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553600510031601735140147 5330400765047402602710221)
    ·
      refine ⟨1998900286892775976016333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5330400765047402602710221 1998900286892775976016333)
      ·
        refine ⟨749587607584790991006125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1998900286892775976016333 749587607584790991006125)
        ·
          refine ⟨281095352844296621627297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 749587607584790991006125 281095352844296621627297)
          ·
            refine ⟨210821514633222466220473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281095352844296621627297 210821514633222466220473)
            ·
              refine ⟨158116135974916849665355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210821514633222466220473 158116135974916849665355)
              ·
                refine ⟨237174203962375274498033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158116135974916849665355 237174203962375274498033)
                ·
                  refine ⟨177880652971781455873525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237174203962375274498033 177880652971781455873525)
                  ·
                    refine ⟨16676311216104511488143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177880652971781455873525 16676311216104511488143)
                    ·
                      rfl

theorem cell23_97431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_97431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97431 prefixEnd_97431 := by exact prefixLift 97431
  have htrace : WordTrace (prefixWord ++ tailWord_97431) baseStart_97431 baseEnd_97431 := by
    simpa [prefixWord, tailWord_97431, baseEnd_97431] using wordTrace_append hprefix tailTrace_97431
  have hstable : (prefixWord ++ tailWord_97431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97431).length < 2 ^ (prefixWord ++ tailWord_97431).sum := by decide
  have hdescent : baseEnd_97431 < baseStart_97431 := by decide
  rcases family_descends (prefixWord ++ tailWord_97431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97468 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_97468 : Nat := 118140960795 + 97468 * 2 ^ 59
def prefixEnd_97468 : Nat := 4983230072969 + 3 ^ 40 * 97468 * 2
def baseEnd_97468 : Nat := 50047932432529889701759

theorem tailTrace_97468 : CollatzResearch.WordTrace tailWord_97468 prefixEnd_97468 50047932432529889701759 := by
  unfold tailWord_97468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777475005448778527118529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2369966673931704702824705 1777475005448778527118529)
  ·
    refine ⟨1333106254086583895338897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1777475005448778527118529 1333106254086583895338897)
    ·
      refine ⟨999829690564937921504173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1333106254086583895338897 999829690564937921504173)
      ·
        refine ⟨374936133961851720564065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 999829690564937921504173 374936133961851720564065)
        ·
          refine ⟨281202100471388790423049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374936133961851720564065 281202100471388790423049)
          ·
            refine ⟨210901575353541592817287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281202100471388790423049 210901575353541592817287)
            ·
              refine ⟨316352363030312389225931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210901575353541592817287 316352363030312389225931)
              ·
                refine ⟨474528544545468583838897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316352363030312389225931 474528544545468583838897)
                ·
                  refine ⟨355896408409101437879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474528544545468583838897 355896408409101437879173)
                  ·
                    refine ⟨66730576576706519602345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 355896408409101437879173 66730576576706519602345)
                    ·
                      refine ⟨50047932432529889701759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66730576576706519602345 50047932432529889701759)
                      ·
                        rfl

theorem cell23_97468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_97468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97468 prefixEnd_97468 := by exact prefixLift 97468
  have htrace : WordTrace (prefixWord ++ tailWord_97468) baseStart_97468 baseEnd_97468 := by
    simpa [prefixWord, tailWord_97468, baseEnd_97468] using wordTrace_append hprefix tailTrace_97468
  have hstable : (prefixWord ++ tailWord_97468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97468).length < 2 ^ (prefixWord ++ tailWord_97468).sum := by decide
  have hdescent : baseEnd_97468 < baseStart_97468 := by decide
  rcases family_descends (prefixWord ++ tailWord_97468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97485 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_97485 : Nat := 118140960795 + 97485 * 2 ^ 59
def prefixEnd_97485 : Nat := 4983230072969 + 3 ^ 40 * 97485 * 2
def baseEnd_97485 : Nat := 50056661603656323189181

theorem tailTrace_97485 : CollatzResearch.WordTrace tailWord_97485 prefixEnd_97485 50056661603656323189181 := by
  unfold tailWord_97485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555570051835968957605909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2370380034557312638403939 3555570051835968957605909)
  ·
    refine ⟨166667346179811044887777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3555570051835968957605909 166667346179811044887777)
    ·
      refine ⟨125000509634858283665833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166667346179811044887777 125000509634858283665833)
      ·
        refine ⟨93750382226143712749375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125000509634858283665833 93750382226143712749375)
        ·
          refine ⟨140625573339215569124063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93750382226143712749375 140625573339215569124063)
          ·
            refine ⟨210938360008823353686095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140625573339215569124063 210938360008823353686095)
            ·
              refine ⟨316407540013235030529143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210938360008823353686095 316407540013235030529143)
              ·
                refine ⟨474611310019852545793715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316407540013235030529143 474611310019852545793715)
                ·
                  refine ⟨711916965029778818690573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474611310019852545793715 711916965029778818690573)
                  ·
                    refine ⟨266968861886167057008965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711916965029778818690573 266968861886167057008965)
                    ·
                      refine ⟨50056661603656323189181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 266968861886167057008965 50056661603656323189181)
                      ·
                        rfl

theorem cell23_97485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_97485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97485 prefixEnd_97485 := by exact prefixLift 97485
  have htrace : WordTrace (prefixWord ++ tailWord_97485) baseStart_97485 baseEnd_97485 := by
    simpa [prefixWord, tailWord_97485, baseEnd_97485] using wordTrace_append hprefix tailTrace_97485
  have hstable : (prefixWord ++ tailWord_97485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97485).length < 2 ^ (prefixWord ++ tailWord_97485).sum := by decide
  have hdescent : baseEnd_97485 < baseStart_97485 := by decide
  rcases family_descends (prefixWord ++ tailWord_97485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97518 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_97518 : Nat := 118140960795 + 97518 * 2 ^ 59
def prefixEnd_97518 : Nat := 4983230072969 + 3 ^ 40 * 97518 * 2
def baseEnd_97518 : Nat := 50073606465254694076529

theorem tailTrace_97518 : CollatzResearch.WordTrace tailWord_97518 prefixEnd_97518 50073606465254694076529 := by
  unfold tailWord_97518
  simp only [CollatzResearch.WordTrace]
  refine ⟨444596707589551949194651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2371182440477610395704805 444596707589551949194651)
  ·
    refine ⟨666895061384327923791977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444596707589551949194651 666895061384327923791977)
    ·
      refine ⟨500171296038245942843983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666895061384327923791977 500171296038245942843983)
      ·
        refine ⟨750256944057368914265975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500171296038245942843983 750256944057368914265975)
        ·
          refine ⟨1125385416086053371398963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750256944057368914265975 1125385416086053371398963)
          ·
            refine ⟨1688078124129080057098445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125385416086053371398963 1688078124129080057098445)
            ·
              refine ⟨633029296548405021411917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1688078124129080057098445 633029296548405021411917)
              ·
                refine ⟨237385986205651883029469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633029296548405021411917 237385986205651883029469)
                ·
                  refine ⟨89019744827119456136051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237385986205651883029469 89019744827119456136051)
                  ·
                    refine ⟨133529617240679184204077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89019744827119456136051 133529617240679184204077)
                    ·
                      refine ⟨50073606465254694076529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133529617240679184204077 50073606465254694076529)
                      ·
                        rfl

theorem cell23_97518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_97518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97518 prefixEnd_97518 := by exact prefixLift 97518
  have htrace : WordTrace (prefixWord ++ tailWord_97518) baseStart_97518 baseEnd_97518 := by
    simpa [prefixWord, tailWord_97518, baseEnd_97518] using wordTrace_append hprefix tailTrace_97518
  have hstable : (prefixWord ++ tailWord_97518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97518).length < 2 ^ (prefixWord ++ tailWord_97518).sum := by decide
  have hdescent : baseEnd_97518 < baseStart_97518 := by decide
  rcases family_descends (prefixWord ++ tailWord_97518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97541 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 6, 2]
def baseStart_97541 : Nat := 118140960795 + 97541 * 2 ^ 59
def prefixEnd_97541 : Nat := 4983230072969 + 3 ^ 40 * 97541 * 2
def baseEnd_97541 : Nat := 50085416520308104088923

theorem tailTrace_97541 : CollatzResearch.WordTrace tailWord_97541 prefixEnd_97541 50085416520308104088923 := by
  unfold tailWord_97541
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557612539633090521644477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2371741693088727014429651 3557612539633090521644477)
  ·
    refine ⟨1334104702362408945616679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3557612539633090521644477 1334104702362408945616679)
    ·
      refine ⟨2001157053543613418425019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334104702362408945616679 2001157053543613418425019)
      ·
        refine ⟨3001735580315420127637529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001157053543613418425019 3001735580315420127637529)
        ·
          refine ⟨2251301685236565095728147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3001735580315420127637529 2251301685236565095728147)
          ·
            refine ⟨3376952527854847643592221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251301685236565095728147 3376952527854847643592221)
            ·
              refine ⟨1266357197945567866347083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3376952527854847643592221 1266357197945567866347083)
              ·
                refine ⟨1899535796918351799520625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266357197945567866347083 1899535796918351799520625)
                ·
                  refine ⟨1424651847688763849640469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1899535796918351799520625 1424651847688763849640469)
                  ·
                    refine ⟨66780555360410805451897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1424651847688763849640469 66780555360410805451897)
                    ·
                      refine ⟨50085416520308104088923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66780555360410805451897 50085416520308104088923)
                      ·
                        rfl

theorem cell23_97541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_97541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97541 prefixEnd_97541 := by exact prefixLift 97541
  have htrace : WordTrace (prefixWord ++ tailWord_97541) baseStart_97541 baseEnd_97541 := by
    simpa [prefixWord, tailWord_97541, baseEnd_97541] using wordTrace_append hprefix tailTrace_97541
  have hstable : (prefixWord ++ tailWord_97541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97541).length < 2 ^ (prefixWord ++ tailWord_97541).sum := by decide
  have hdescent : baseEnd_97541 < baseStart_97541 := by decide
  rcases family_descends (prefixWord ++ tailWord_97541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97564 : List Nat := [2, 2, 3, 1, 1, 1, 13]
def baseStart_97564 : Nat := 118140960795 + 97564 * 2 ^ 59
def prefixEnd_97564 : Nat := 4983230072969 + 3 ^ 40 * 97564 * 2
def baseEnd_97564 : Nat := 618484278708166840757

theorem tailTrace_97564 : CollatzResearch.WordTrace tailWord_97564 prefixEnd_97564 618484278708166840757 := by
  unfold tailWord_97564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779225709274882724865873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2372300945699843633154497 1779225709274882724865873)
  ·
    refine ⟨1334419281956162043649405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1779225709274882724865873 1334419281956162043649405)
    ·
      refine ⟨500407230733560766368527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1334419281956162043649405 500407230733560766368527)
      ·
        refine ⟨750610846100341149552791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500407230733560766368527 750610846100341149552791)
        ·
          refine ⟨1125916269150511724329187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750610846100341149552791 1125916269150511724329187)
          ·
            refine ⟨1688874403725767586493781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125916269150511724329187 1688874403725767586493781)
            ·
              refine ⟨618484278708166840757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 1688874403725767586493781 618484278708166840757)
              ·
                rfl

theorem cell23_97564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 13].length) (baseStart_97564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97564 prefixEnd_97564 := by exact prefixLift 97564
  have htrace : WordTrace (prefixWord ++ tailWord_97564) baseStart_97564 baseEnd_97564 := by
    simpa [prefixWord, tailWord_97564, baseEnd_97564] using wordTrace_append hprefix tailTrace_97564
  have hstable : (prefixWord ++ tailWord_97564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97564).length < 2 ^ (prefixWord ++ tailWord_97564).sum := by decide
  have hdescent : baseEnd_97564 < baseStart_97564 := by decide
  rcases family_descends (prefixWord ++ tailWord_97564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97578 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_97578 : Nat := 118140960795 + 97578 * 2 ^ 59
def prefixEnd_97578 : Nat := 4983230072969 + 3 ^ 40 * 97578 * 2
def baseEnd_97578 : Nat := 50104415304524459326253

theorem tailTrace_97578 : CollatzResearch.WordTrace tailWord_97578 prefixEnd_97578 50104415304524459326253 := by
  unfold tailWord_97578
  simp only [CollatzResearch.WordTrace]
  refine ⟨889740510124761460185347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2372641360332697227160925 889740510124761460185347)
  ·
    refine ⟨1334610765187142190278021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889740510124761460185347 1334610765187142190278021)
    ·
      refine ⟨250239518472589160677129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1334610765187142190278021 250239518472589160677129)
      ·
        refine ⟨187679638854441870507847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250239518472589160677129 187679638854441870507847)
        ·
          refine ⟨281519458281662805761771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187679638854441870507847 281519458281662805761771)
          ·
            refine ⟨422279187422494208642657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281519458281662805761771 422279187422494208642657)
            ·
              refine ⟨316709390566870656481993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422279187422494208642657 316709390566870656481993)
              ·
                refine ⟨237532042925152992361495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316709390566870656481993 237532042925152992361495)
                ·
                  refine ⟨356298064387729488542243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237532042925152992361495 356298064387729488542243)
                  ·
                    refine ⟨534447096581594232813365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 356298064387729488542243 534447096581594232813365)
                    ·
                      refine ⟨50104415304524459326253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 534447096581594232813365 50104415304524459326253)
                      ·
                        rfl

theorem cell23_97578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_97578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97578 prefixEnd_97578 := by exact prefixLift 97578
  have htrace : WordTrace (prefixWord ++ tailWord_97578) baseStart_97578 baseEnd_97578 := by
    simpa [prefixWord, tailWord_97578, baseEnd_97578] using wordTrace_append hprefix tailTrace_97578
  have hstable : (prefixWord ++ tailWord_97578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97578).length < 2 ^ (prefixWord ++ tailWord_97578).sum := by decide
  have hdescent : baseEnd_97578 < baseStart_97578 := by decide
  rcases family_descends (prefixWord ++ tailWord_97578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97584 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_97584 : Nat := 118140960795 + 97584 * 2 ^ 59
def prefixEnd_97584 : Nat := 4983230072969 + 3 ^ 40 * 97584 * 2
def baseEnd_97584 : Nat := 50107496188451435851225

theorem tailTrace_97584 : CollatzResearch.WordTrace tailWord_97584 prefixEnd_97584 50107496188451435851225 := by
  unfold tailWord_97584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779590439238654432729903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2372787252318205910306537 1779590439238654432729903)
  ·
    refine ⟨2669385658857981649094855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779590439238654432729903 2669385658857981649094855)
    ·
      refine ⟨4004078488286972473642283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669385658857981649094855 4004078488286972473642283)
      ·
        refine ⟨6006117732430458710463425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004078488286972473642283 6006117732430458710463425)
        ·
          refine ⟨4504588299322844032847569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6006117732430458710463425 4504588299322844032847569)
          ·
            refine ⟨3378441224492133024635677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4504588299322844032847569 3378441224492133024635677)
            ·
              refine ⟨1266915459184549884238379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378441224492133024635677 1266915459184549884238379)
              ·
                refine ⟨1900373188776824826357569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266915459184549884238379 1900373188776824826357569)
                ·
                  refine ⟨1425279891582618619768177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900373188776824826357569 1425279891582618619768177)
                  ·
                    refine ⟨1068959918686963964826133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425279891582618619768177 1068959918686963964826133)
                    ·
                      refine ⟨50107496188451435851225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1068959918686963964826133 50107496188451435851225)
                      ·
                        rfl

theorem cell23_97584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_97584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97584 prefixEnd_97584 := by exact prefixLift 97584
  have htrace : WordTrace (prefixWord ++ tailWord_97584) baseStart_97584 baseEnd_97584 := by
    simpa [prefixWord, tailWord_97584, baseEnd_97584] using wordTrace_append hprefix tailTrace_97584
  have hstable : (prefixWord ++ tailWord_97584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97584).length < 2 ^ (prefixWord ++ tailWord_97584).sum := by decide
  have hdescent : baseEnd_97584 < baseStart_97584 := by decide
  rcases family_descends (prefixWord ++ tailWord_97584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97585 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 2, 4]
def baseStart_97585 : Nat := 118140960795 + 97585 * 2 ^ 59
def prefixEnd_97585 : Nat := 4983230072969 + 3 ^ 40 * 97585 * 2
def baseEnd_97585 : Nat := 16702669889701977312907

theorem tailTrace_97585 : CollatzResearch.WordTrace tailWord_97585 prefixEnd_97585 16702669889701977312907 := by
  unfold tailWord_97585
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559217351473686036246209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2372811567649124024164139 3559217351473686036246209)
  ·
    refine ⟨2669413013605264527184657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3559217351473686036246209 2669413013605264527184657)
    ·
      refine ⟨2002059760203948395388493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2669413013605264527184657 2002059760203948395388493)
      ·
        refine ⟨750772410076480648270685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2002059760203948395388493 750772410076480648270685)
        ·
          refine ⟨281539653778680243101507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750772410076480648270685 281539653778680243101507)
          ·
            refine ⟨422309480668020364652261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281539653778680243101507 422309480668020364652261)
            ·
              refine ⟨79183027625253818372299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 422309480668020364652261 79183027625253818372299)
              ·
                refine ⟨118774541437880727558449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79183027625253818372299 118774541437880727558449)
                ·
                  refine ⟨89080906078410545668837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118774541437880727558449 89080906078410545668837)
                  ·
                    refine ⟨16702669889701977312907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89080906078410545668837 16702669889701977312907)
                    ·
                      rfl

theorem cell23_97585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_97585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97585 prefixEnd_97585 := by exact prefixLift 97585
  have htrace : WordTrace (prefixWord ++ tailWord_97585) baseStart_97585 baseEnd_97585 := by
    simpa [prefixWord, tailWord_97585, baseEnd_97585] using wordTrace_append hprefix tailTrace_97585
  have hstable : (prefixWord ++ tailWord_97585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97585).length < 2 ^ (prefixWord ++ tailWord_97585).sum := by decide
  have hdescent : baseEnd_97585 < baseStart_97585 := by decide
  rcases family_descends (prefixWord ++ tailWord_97585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97588 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_97588 : Nat := 118140960795 + 97588 * 2 ^ 59
def prefixEnd_97588 : Nat := 4983230072969 + 3 ^ 40 * 97588 * 2
def baseEnd_97588 : Nat := 50109550111069420201207

theorem tailTrace_97588 : CollatzResearch.WordTrace tailWord_97588 prefixEnd_97588 50109550111069420201207 := by
  unfold tailWord_97588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779663385231408774302709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2372884513641878365736945 1779663385231408774302709)
  ·
    refine ⟨166843442365444572590879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1779663385231408774302709 166843442365444572590879)
    ·
      refine ⟨250265163548166858886319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166843442365444572590879 250265163548166858886319)
      ·
        refine ⟨375397745322250288329479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250265163548166858886319 375397745322250288329479)
        ·
          refine ⟨563096617983375432494219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375397745322250288329479 563096617983375432494219)
          ·
            refine ⟨844644926975063148741329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563096617983375432494219 844644926975063148741329)
            ·
              refine ⟨633483695231297361555997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844644926975063148741329 633483695231297361555997)
              ·
                refine ⟨237556385711736510583499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633483695231297361555997 237556385711736510583499)
                ·
                  refine ⟨356334578567604765875249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237556385711736510583499 356334578567604765875249)
                  ·
                    refine ⟨267250933925703574406437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 356334578567604765875249 267250933925703574406437)
                    ·
                      refine ⟨50109550111069420201207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 267250933925703574406437 50109550111069420201207)
                      ·
                        rfl

theorem cell23_97588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_97588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97588 prefixEnd_97588 := by exact prefixLift 97588
  have htrace : WordTrace (prefixWord ++ tailWord_97588) baseStart_97588 baseEnd_97588 := by
    simpa [prefixWord, tailWord_97588, baseEnd_97588] using wordTrace_append hprefix tailTrace_97588
  have hstable : (prefixWord ++ tailWord_97588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97588).length < 2 ^ (prefixWord ++ tailWord_97588).sum := by decide
  have hdescent : baseEnd_97588 < baseStart_97588 := by decide
  rcases family_descends (prefixWord ++ tailWord_97588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97661 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_97661 : Nat := 118140960795 + 97661 * 2 ^ 59
def prefixEnd_97661 : Nat := 4983230072969 + 3 ^ 40 * 97661 * 2
def baseEnd_97661 : Nat := 50147034198847634588371

theorem tailTrace_97661 : CollatzResearch.WordTrace tailWord_97661 prefixEnd_97661 50147034198847634588371 := by
  unfold tailWord_97661
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561989299198351016012837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2374659532798900677341891 3561989299198351016012837)
  ·
    refine ⟨667872993599690815502407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3561989299198351016012837 667872993599690815502407)
    ·
      refine ⟨1001809490399536223253611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667872993599690815502407 1001809490399536223253611)
      ·
        refine ⟨1502714235599304334880417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001809490399536223253611 1502714235599304334880417)
        ·
          refine ⟨1127035676699478251160313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502714235599304334880417 1127035676699478251160313)
          ·
            refine ⟨845276757524608688370235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127035676699478251160313 845276757524608688370235)
            ·
              refine ⟨1267915136286913032555353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845276757524608688370235 1267915136286913032555353)
              ·
                refine ⟨950936352215184774416515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267915136286913032555353 950936352215184774416515)
                ·
                  refine ⟨1426404528322777161624773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950936352215184774416515 1426404528322777161624773)
                  ·
                    refine ⟨267450849060520717804645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426404528322777161624773 267450849060520717804645)
                    ·
                      refine ⟨50147034198847634588371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 267450849060520717804645 50147034198847634588371)
                      ·
                        rfl

theorem cell23_97661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_97661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97661 prefixEnd_97661 := by exact prefixLift 97661
  have htrace : WordTrace (prefixWord ++ tailWord_97661) baseStart_97661 baseEnd_97661 := by
    simpa [prefixWord, tailWord_97661, baseEnd_97661] using wordTrace_append hprefix tailTrace_97661
  have hstable : (prefixWord ++ tailWord_97661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97661).length < 2 ^ (prefixWord ++ tailWord_97661).sum := by decide
  have hdescent : baseEnd_97661 < baseStart_97661 := by decide
  rcases family_descends (prefixWord ++ tailWord_97661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97681 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_97681 : Nat := 118140960795 + 97681 * 2 ^ 59
def prefixEnd_97681 : Nat := 4983230072969 + 3 ^ 40 * 97681 * 2
def baseEnd_97681 : Nat := 50157303811937556338279

theorem tailTrace_97681 : CollatzResearch.WordTrace tailWord_97681 prefixEnd_97681 50157303811937556338279 := by
  unfold tailWord_97681
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562718759125894431740897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2375145839417262954493931 3562718759125894431740897)
  ·
    refine ⟨2672039069344420823805673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3562718759125894431740897 2672039069344420823805673)
    ·
      refine ⟨2004029302008315617854255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2672039069344420823805673 2004029302008315617854255)
      ·
        refine ⟨3006043953012473426781383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004029302008315617854255 3006043953012473426781383)
        ·
          refine ⟨4509065929518710140172075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006043953012473426781383 4509065929518710140172075)
          ·
            refine ⟨6763598894278065210258113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509065929518710140172075 6763598894278065210258113)
            ·
              refine ⟨5072699170708548907693585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763598894278065210258113 5072699170708548907693585)
              ·
                refine ⟨3804524378031411680770189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072699170708548907693585 3804524378031411680770189)
                ·
                  refine ⟨1426696641761779380288821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3804524378031411680770189 1426696641761779380288821)
                  ·
                    refine ⟨133752810165166816902077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1426696641761779380288821 133752810165166816902077)
                    ·
                      refine ⟨50157303811937556338279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 133752810165166816902077 50157303811937556338279)
                      ·
                        rfl

theorem cell23_97681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_97681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97681 prefixEnd_97681 := by exact prefixLift 97681
  have htrace : WordTrace (prefixWord ++ tailWord_97681) baseStart_97681 baseEnd_97681 := by
    simpa [prefixWord, tailWord_97681, baseEnd_97681] using wordTrace_append hprefix tailTrace_97681
  have hstable : (prefixWord ++ tailWord_97681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97681).length < 2 ^ (prefixWord ++ tailWord_97681).sum := by decide
  have hdescent : baseEnd_97681 < baseStart_97681 := by decide
  rcases family_descends (prefixWord ++ tailWord_97681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97701 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_97701 : Nat := 118140960795 + 97701 * 2 ^ 59
def prefixEnd_97701 : Nat := 4983230072969 + 3 ^ 40 * 97701 * 2
def baseEnd_97701 : Nat := 16722524475009159362729

theorem tailTrace_97701 : CollatzResearch.WordTrace tailWord_97701 prefixEnd_97701 16722524475009159362729 := by
  unfold tailWord_97701
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563448219053437847468957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2375632146035625231645971 3563448219053437847468957)
  ·
    refine ⟨1336293082145039192800859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3563448219053437847468957 1336293082145039192800859)
    ·
      refine ⟨2004439623217558789201289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336293082145039192800859 2004439623217558789201289)
      ·
        refine ⟨1503329717413169091900967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004439623217558789201289 1503329717413169091900967)
        ·
          refine ⟨2254994576119753637851451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503329717413169091900967 2254994576119753637851451)
          ·
            refine ⟨3382491864179630456777177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254994576119753637851451 3382491864179630456777177)
            ·
              refine ⟨2536868898134722842582883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3382491864179630456777177 2536868898134722842582883)
              ·
                refine ⟨3805303347202084263874325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536868898134722842582883 3805303347202084263874325)
                ·
                  refine ⟨178373594400097699869109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3805303347202084263874325 178373594400097699869109)
                  ·
                    refine ⟨16722524475009159362729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 178373594400097699869109 16722524475009159362729)
                    ·
                      rfl

theorem cell23_97701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_97701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97701 prefixEnd_97701 := by exact prefixLift 97701
  have htrace : WordTrace (prefixWord ++ tailWord_97701) baseStart_97701 baseEnd_97701 := by
    simpa [prefixWord, tailWord_97701, baseEnd_97701] using wordTrace_append hprefix tailTrace_97701
  have hstable : (prefixWord ++ tailWord_97701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97701).length < 2 ^ (prefixWord ++ tailWord_97701).sum := by decide
  have hdescent : baseEnd_97701 < baseStart_97701 := by decide
  rcases family_descends (prefixWord ++ tailWord_97701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97708 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 2, 5, 2]
def baseStart_97708 : Nat := 118140960795 + 97708 * 2 ^ 59
def prefixEnd_97708 : Nat := 4983230072969 + 3 ^ 40 * 97708 * 2
def baseEnd_97708 : Nat := 50171167789608950700655

theorem tailTrace_97708 : CollatzResearch.WordTrace tailWord_97708 prefixEnd_97708 50171167789608950700655 := by
  unfold tailWord_97708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1781851765014039021486889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2375802353352052028649185 1781851765014039021486889)
  ·
    refine ⟨1336388823760529266115167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1781851765014039021486889 1336388823760529266115167)
    ·
      refine ⟨2004583235640793899172751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336388823760529266115167 2004583235640793899172751)
      ·
        refine ⟨3006874853461190848759127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004583235640793899172751 3006874853461190848759127)
        ·
          refine ⟨4510312280191786273138691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006874853461190848759127 4510312280191786273138691)
          ·
            refine ⟨6765468420287679409708037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510312280191786273138691 6765468420287679409708037)
            ·
              refine ⟨1268525328803939889320257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6765468420287679409708037 1268525328803939889320257)
              ·
                refine ⟨951393996602954916990193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268525328803939889320257 951393996602954916990193)
                ·
                  refine ⟨713545497452216187742645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 951393996602954916990193 713545497452216187742645)
                  ·
                    refine ⟨66894890386145267600873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 713545497452216187742645 66894890386145267600873)
                    ·
                      refine ⟨50171167789608950700655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 66894890386145267600873 50171167789608950700655)
                      ·
                        rfl

theorem cell23_97708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_97708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97708 prefixEnd_97708 := by exact prefixLift 97708
  have htrace : WordTrace (prefixWord ++ tailWord_97708) baseStart_97708 baseEnd_97708 := by
    simpa [prefixWord, tailWord_97708, baseEnd_97708] using wordTrace_append hprefix tailTrace_97708
  have hstable : (prefixWord ++ tailWord_97708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97708).length < 2 ^ (prefixWord ++ tailWord_97708).sum := by decide
  have hdescent : baseEnd_97708 < baseStart_97708 := by decide
  rcases family_descends (prefixWord ++ tailWord_97708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97738 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_97738 : Nat := 118140960795 + 97738 * 2 ^ 59
def prefixEnd_97738 : Nat := 4983230072969 + 3 ^ 40 * 97738 * 2
def baseEnd_97738 : Nat := 50186572209243833325517

theorem tailTrace_97738 : CollatzResearch.WordTrace tailWord_97738 prefixEnd_97738 50186572209243833325517 := by
  unfold tailWord_97738
  simp only [CollatzResearch.WordTrace]
  refine ⟨891199429979848291641467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2376531813279595444377245 891199429979848291641467)
  ·
    refine ⟨1336799144969772437462201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891199429979848291641467 1336799144969772437462201)
    ·
      refine ⟨1002599358727329328096651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1336799144969772437462201 1002599358727329328096651)
      ·
        refine ⟨1503899038090993992144977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002599358727329328096651 1503899038090993992144977)
        ·
          refine ⟨1127924278568245494108733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503899038090993992144977 1127924278568245494108733)
          ·
            refine ⟨422971604463092060290775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1127924278568245494108733 422971604463092060290775)
            ·
              refine ⟨634457406694638090436163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422971604463092060290775 634457406694638090436163)
              ·
                refine ⟨951686110041957135654245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634457406694638090436163 951686110041957135654245)
                ·
                  refine ⟨178441145632866962935171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951686110041957135654245 178441145632866962935171)
                  ·
                    refine ⟨267661718449300444402757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178441145632866962935171 267661718449300444402757)
                    ·
                      refine ⟨50186572209243833325517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 267661718449300444402757 50186572209243833325517)
                      ·
                        rfl

theorem cell23_97738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_97738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97738 prefixEnd_97738 := by exact prefixLift 97738
  have htrace : WordTrace (prefixWord ++ tailWord_97738) baseStart_97738 baseEnd_97738 := by
    simpa [prefixWord, tailWord_97738, baseEnd_97738] using wordTrace_append hprefix tailTrace_97738
  have hstable : (prefixWord ++ tailWord_97738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97738).length < 2 ^ (prefixWord ++ tailWord_97738).sum := by decide
  have hdescent : baseEnd_97738 < baseStart_97738 := by decide
  rcases family_descends (prefixWord ++ tailWord_97738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97751 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_97751 : Nat := 118140960795 + 97751 * 2 ^ 59
def prefixEnd_97751 : Nat := 4983230072969 + 3 ^ 40 * 97751 * 2
def baseEnd_97751 : Nat := 50193247457752282462957

theorem tailTrace_97751 : CollatzResearch.WordTrace tailWord_97751 prefixEnd_97751 50193247457752282462957 := by
  unfold tailWord_97751
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565271868872296386789107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2376847912581530924526071 3565271868872296386789107)
  ·
    refine ⟨5347907803308444580183661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3565271868872296386789107 5347907803308444580183661)
    ·
      refine ⟨2005465426240666717568873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5347907803308444580183661 2005465426240666717568873)
      ·
        refine ⟨1504099069680500038176655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2005465426240666717568873 1504099069680500038176655)
        ·
          refine ⟨2256148604520750057264983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504099069680500038176655 2256148604520750057264983)
          ·
            refine ⟨3384222906781125085897475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256148604520750057264983 3384222906781125085897475)
            ·
              refine ⟨5076334360171687628846213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384222906781125085897475 5076334360171687628846213)
              ·
                refine ⟨951812692532191430408665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5076334360171687628846213 951812692532191430408665)
                ·
                  refine ⟨713859519399143572806499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 951812692532191430408665 713859519399143572806499)
                  ·
                    refine ⟨1070789279098715359209749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 713859519399143572806499 1070789279098715359209749)
                    ·
                      refine ⟨50193247457752282462957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1070789279098715359209749 50193247457752282462957)
                      ·
                        rfl

theorem cell23_97751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_97751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97751 prefixEnd_97751 := by exact prefixLift 97751
  have htrace : WordTrace (prefixWord ++ tailWord_97751) baseStart_97751 baseEnd_97751 := by
    simpa [prefixWord, tailWord_97751, baseEnd_97751] using wordTrace_append hprefix tailTrace_97751
  have hstable : (prefixWord ++ tailWord_97751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97751).length < 2 ^ (prefixWord ++ tailWord_97751).sum := by decide
  have hdescent : baseEnd_97751 < baseStart_97751 := by decide
  rcases family_descends (prefixWord ++ tailWord_97751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97799 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 1, 4]
def baseStart_97799 : Nat := 118140960795 + 97799 * 2 ^ 59
def prefixEnd_97799 : Nat := 4983230072969 + 3 ^ 40 * 97799 * 2
def baseEnd_97799 : Nat := 16739298176389364887579

theorem tailTrace_97799 : CollatzResearch.WordTrace tailWord_97799 prefixEnd_97799 16739298176389364887579 := by
  unfold tailWord_97799
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567022572698400584536451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2378015048465600389690967 3567022572698400584536451)
  ·
    refine ⟨5350533859047600876804677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3567022572698400584536451 5350533859047600876804677)
    ·
      refine ⟨1003225098571425164400877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5350533859047600876804677 1003225098571425164400877)
      ·
        refine ⟨376209411964284436650329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1003225098571425164400877 376209411964284436650329)
        ·
          refine ⟨282157058973213327487747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376209411964284436650329 282157058973213327487747)
          ·
            refine ⟨423235588459819991231621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282157058973213327487747 423235588459819991231621)
            ·
              refine ⟨79356672836216248355929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 423235588459819991231621 79356672836216248355929)
              ·
                refine ⟨59517504627162186266947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79356672836216248355929 59517504627162186266947)
                ·
                  refine ⟨89276256940743279400421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59517504627162186266947 89276256940743279400421)
                  ·
                    refine ⟨16739298176389364887579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89276256940743279400421 16739298176389364887579)
                    ·
                      rfl

theorem cell23_97799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_97799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97799 prefixEnd_97799 := by exact prefixLift 97799
  have htrace : WordTrace (prefixWord ++ tailWord_97799) baseStart_97799 baseEnd_97799 := by
    simpa [prefixWord, tailWord_97799, baseEnd_97799] using wordTrace_append hprefix tailTrace_97799
  have hstable : (prefixWord ++ tailWord_97799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97799).length < 2 ^ (prefixWord ++ tailWord_97799).sum := by decide
  have hdescent : baseEnd_97799 < baseStart_97799 := by decide
  rcases family_descends (prefixWord ++ tailWord_97799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97855 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 4, 4]
def baseStart_97855 : Nat := 118140960795 + 97855 * 2 ^ 59
def prefixEnd_97855 : Nat := 4983230072969 + 3 ^ 40 * 97855 * 2
def baseEnd_97855 : Nat := 16748883148606625187493

theorem tailTrace_97855 : CollatzResearch.WordTrace tailWord_97855 prefixEnd_97855 16748883148606625187493 := by
  unfold tailWord_97855
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569065060495522148575019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2379376706997014765716679 3569065060495522148575019)
  ·
    refine ⟨5353597590743283222862529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3569065060495522148575019 5353597590743283222862529)
    ·
      refine ⟨4015198193057462417146897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5353597590743283222862529 4015198193057462417146897)
      ·
        refine ⟨3011398644793096812860173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015198193057462417146897 3011398644793096812860173)
        ·
          refine ⟨1129274491797411304822565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3011398644793096812860173 1129274491797411304822565)
          ·
            refine ⟨211738967212014619654231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1129274491797411304822565 211738967212014619654231)
            ·
              refine ⟨317608450818021929481347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211738967212014619654231 317608450818021929481347)
              ·
                refine ⟨476412676227032894222021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317608450818021929481347 476412676227032894222021)
                ·
                  refine ⟨89327376792568667666629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476412676227032894222021 89327376792568667666629)
                  ·
                    refine ⟨16748883148606625187493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89327376792568667666629 16748883148606625187493)
                    ·
                      rfl

theorem cell23_97855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_97855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97855 prefixEnd_97855 := by exact prefixLift 97855
  have htrace : WordTrace (prefixWord ++ tailWord_97855) baseStart_97855 baseEnd_97855 := by
    simpa [prefixWord, tailWord_97855, baseEnd_97855] using wordTrace_append hprefix tailTrace_97855
  have hstable : (prefixWord ++ tailWord_97855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97855).length < 2 ^ (prefixWord ++ tailWord_97855).sum := by decide
  have hdescent : baseEnd_97855 < baseStart_97855 := by decide
  rcases family_descends (prefixWord ++ tailWord_97855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97872 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 2, 4]
def baseStart_97872 : Nat := 118140960795 + 97872 * 2 ^ 59
def prefixEnd_97872 : Nat := 4983230072969 + 3 ^ 40 * 97872 * 2
def baseEnd_97872 : Nat := 16751792872315436349967

theorem tailTrace_97872 : CollatzResearch.WordTrace tailWord_97872 prefixEnd_97872 16751792872315436349967 := by
  unfold tailWord_97872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784842550716967025971935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2379790067622622701295913 1784842550716967025971935)
  ·
    refine ⟨2677263826075450538957903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784842550716967025971935 2677263826075450538957903)
    ·
      refine ⟨4015895739113175808436855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677263826075450538957903 4015895739113175808436855)
      ·
        refine ⟨6023843608669763712655283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015895739113175808436855 6023843608669763712655283)
        ·
          refine ⟨9035765413004645568982925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6023843608669763712655283 9035765413004645568982925)
          ·
            refine ⟨3388412029876742088368597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9035765413004645568982925 3388412029876742088368597)
            ·
              refine ⟨79415906950236142696139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3388412029876742088368597 79415906950236142696139)
              ·
                refine ⟨119123860425354214044209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79415906950236142696139 119123860425354214044209)
                ·
                  refine ⟨89342895319015660533157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119123860425354214044209 89342895319015660533157)
                  ·
                    refine ⟨16751792872315436349967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89342895319015660533157 16751792872315436349967)
                    ·
                      rfl

theorem cell23_97872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 2, 4].length) (baseStart_97872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97872 prefixEnd_97872 := by exact prefixLift 97872
  have htrace : WordTrace (prefixWord ++ tailWord_97872) baseStart_97872 baseEnd_97872 := by
    simpa [prefixWord, tailWord_97872, baseEnd_97872] using wordTrace_append hprefix tailTrace_97872
  have hstable : (prefixWord ++ tailWord_97872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97872).length < 2 ^ (prefixWord ++ tailWord_97872).sum := by decide
  have hdescent : baseEnd_97872 < baseStart_97872 := by decide
  rcases family_descends (prefixWord ++ tailWord_97872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97895 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_97895 : Nat := 118140960795 + 97895 * 2 ^ 59
def prefixEnd_97895 : Nat := 4983230072969 + 3 ^ 40 * 97895 * 2
def baseEnd_97895 : Nat := 50267188671999719062295

theorem tailTrace_97895 : CollatzResearch.WordTrace tailWord_97895 prefixEnd_97895 50267188671999719062295 := by
  unfold tailWord_97895
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570523980350608980031139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2380349320233739320020759 3570523980350608980031139)
  ·
    refine ⟨5355785970525913470046709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3570523980350608980031139 5355785970525913470046709)
    ·
      refine ⟨502104934736804387816879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5355785970525913470046709 502104934736804387816879)
      ·
        refine ⟨753157402105206581725319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502104934736804387816879 753157402105206581725319)
        ·
          refine ⟨1129736103157809872587979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753157402105206581725319 1129736103157809872587979)
          ·
            refine ⟨1694604154736714808881969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129736103157809872587979 1694604154736714808881969)
            ·
              refine ⟨1270953116052536106661477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694604154736714808881969 1270953116052536106661477)
              ·
                refine ⟨238303709259850519999027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1270953116052536106661477 238303709259850519999027)
                ·
                  refine ⟨357455563889775779998541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238303709259850519999027 357455563889775779998541)
                  ·
                    refine ⟨134045836458665917499453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357455563889775779998541 134045836458665917499453)
                    ·
                      refine ⟨50267188671999719062295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134045836458665917499453 50267188671999719062295)
                      ·
                        rfl

theorem cell23_97895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_97895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97895 prefixEnd_97895 := by exact prefixLift 97895
  have htrace : WordTrace (prefixWord ++ tailWord_97895) baseStart_97895 baseEnd_97895 := by
    simpa [prefixWord, tailWord_97895, baseEnd_97895] using wordTrace_append hprefix tailTrace_97895
  have hstable : (prefixWord ++ tailWord_97895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97895).length < 2 ^ (prefixWord ++ tailWord_97895).sum := by decide
  have hdescent : baseEnd_97895 < baseStart_97895 := by decide
  rcases family_descends (prefixWord ++ tailWord_97895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97902 : List Nat := [4, 1, 2, 2, 4, 1, 9]
def baseStart_97902 : Nat := 118140960795 + 97902 * 2 ^ 59
def prefixEnd_97902 : Nat := 4983230072969 + 3 ^ 40 * 97902 * 2
def baseEnd_97902 : Nat := 620626951068903600923

theorem tailTrace_97902 : CollatzResearch.WordTrace tailWord_97902 prefixEnd_97902 620626951068903600923 := by
  unfold tailWord_97902
  simp only [CollatzResearch.WordTrace]
  refine ⟨446347411415656146941995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2380519527550166117023973 446347411415656146941995)
  ·
    refine ⟨669521117123484220412993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 446347411415656146941995 669521117123484220412993)
    ·
      refine ⟨502140837842613165309745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 669521117123484220412993 502140837842613165309745)
      ·
        refine ⟨376605628381959873982309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502140837842613165309745 376605628381959873982309)
        ·
          refine ⟨70613555321617476371683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 376605628381959873982309 70613555321617476371683)
          ·
            refine ⟨105920332982426214557525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70613555321617476371683 105920332982426214557525)
            ·
              refine ⟨620626951068903600923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 105920332982426214557525 620626951068903600923)
              ·
                rfl

theorem cell23_97902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 9].length) (baseStart_97902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97902 prefixEnd_97902 := by exact prefixLift 97902
  have htrace : WordTrace (prefixWord ++ tailWord_97902) baseStart_97902 baseEnd_97902 := by
    simpa [prefixWord, tailWord_97902, baseEnd_97902] using wordTrace_append hprefix tailTrace_97902
  have hstable : (prefixWord ++ tailWord_97902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97902).length < 2 ^ (prefixWord ++ tailWord_97902).sum := by decide
  have hdescent : baseEnd_97902 < baseStart_97902 := by decide
  rcases family_descends (prefixWord ++ tailWord_97902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97929 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 2, 1, 3]
def baseStart_97929 : Nat := 118140960795 + 97929 * 2 ^ 59
def prefixEnd_97929 : Nat := 4983230072969 + 3 ^ 40 * 97929 * 2
def baseEnd_97929 : Nat := 50284647014252586037139

theorem tailTrace_97929 : CollatzResearch.WordTrace tailWord_97929 prefixEnd_97929 50284647014252586037139 := by
  unfold tailWord_97929
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571764062227432786768841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2381176041484955191179227 3571764062227432786768841)
  ·
    refine ⟨2678823046670574590076631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3571764062227432786768841 2678823046670574590076631)
    ·
      refine ⟨4018234570005861885114947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2678823046670574590076631 4018234570005861885114947)
      ·
        refine ⟨6027351855008792827672421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018234570005861885114947 6027351855008792827672421)
        ·
          refine ⟨1130128472814148655188579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6027351855008792827672421 1130128472814148655188579)
          ·
            refine ⟨1695192709221222982782869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130128472814148655188579 1695192709221222982782869)
            ·
              refine ⟨79462158244744827317947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1695192709221222982782869 79462158244744827317947)
              ·
                refine ⟨119193237367117240976921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79462158244744827317947 119193237367117240976921)
                ·
                  refine ⟨89394928025337930732691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119193237367117240976921 89394928025337930732691)
                  ·
                    refine ⟨134092392038006896099037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89394928025337930732691 134092392038006896099037)
                    ·
                      refine ⟨50284647014252586037139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134092392038006896099037 50284647014252586037139)
                      ·
                        rfl

theorem cell23_97929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 1, 3].length) (baseStart_97929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97929 prefixEnd_97929 := by exact prefixLift 97929
  have htrace : WordTrace (prefixWord ++ tailWord_97929) baseStart_97929 baseEnd_97929 := by
    simpa [prefixWord, tailWord_97929, baseEnd_97929] using wordTrace_append hprefix tailTrace_97929
  have hstable : (prefixWord ++ tailWord_97929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97929).length < 2 ^ (prefixWord ++ tailWord_97929).sum := by decide
  have hdescent : baseEnd_97929 < baseStart_97929 := by decide
  rcases family_descends (prefixWord ++ tailWord_97929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97952 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 3, 4, 2]
def baseStart_97952 : Nat := 118140960795 + 97952 * 2 ^ 59
def prefixEnd_97952 : Nat := 4983230072969 + 3 ^ 40 * 97952 * 2
def baseEnd_97952 : Nat := 50296457069305996049533

theorem tailTrace_97952 : CollatzResearch.WordTrace tailWord_97952 prefixEnd_97952 50296457069305996049533 := by
  unfold tailWord_97952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786301470572053857428055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2381735294096071809904073 1786301470572053857428055)
  ·
    refine ⟨2679452205858080786142083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786301470572053857428055 2679452205858080786142083)
    ·
      refine ⟨4019178308787121179213125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2679452205858080786142083 4019178308787121179213125)
      ·
        refine ⟨753595932897585221102461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4019178308787121179213125 753595932897585221102461)
        ·
          refine ⟨282598474836594457913423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 753595932897585221102461 282598474836594457913423)
          ·
            refine ⟨423897712254891686870135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282598474836594457913423 423897712254891686870135)
            ·
              refine ⟨635846568382337530305203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423897712254891686870135 635846568382337530305203)
              ·
                refine ⟨953769852573506295457805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635846568382337530305203 953769852573506295457805)
                ·
                  refine ⟨357663694715064860796677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 953769852573506295457805 357663694715064860796677)
                  ·
                    refine ⟨67061942759074661399377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 357663694715064860796677 67061942759074661399377)
                    ·
                      refine ⟨50296457069305996049533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67061942759074661399377 50296457069305996049533)
                      ·
                        rfl

theorem cell23_97952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_97952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97952 prefixEnd_97952 := by exact prefixLift 97952
  have htrace : WordTrace (prefixWord ++ tailWord_97952) baseStart_97952 baseEnd_97952 := by
    simpa [prefixWord, tailWord_97952, baseEnd_97952] using wordTrace_append hprefix tailTrace_97952
  have hstable : (prefixWord ++ tailWord_97952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97952).length < 2 ^ (prefixWord ++ tailWord_97952).sum := by decide
  have hdescent : baseEnd_97952 < baseStart_97952 := by decide
  rcases family_descends (prefixWord ++ tailWord_97952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97956 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_97956 : Nat := 118140960795 + 97956 * 2 ^ 59
def prefixEnd_97956 : Nat := 4983230072969 + 3 ^ 40 * 97956 * 2
def baseEnd_97956 : Nat := 50298510991923980399515

theorem tailTrace_97956 : CollatzResearch.WordTrace tailWord_97956 prefixEnd_97956 50298510991923980399515 := by
  unfold tailWord_97956
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786374416564808199000861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2381832555419744265334481 1786374416564808199000861)
  ·
    refine ⟨669890406211803074625323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1786374416564808199000861 669890406211803074625323)
    ·
      refine ⟨1004835609317704611937985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669890406211803074625323 1004835609317704611937985)
      ·
        refine ⟨753626706988278458953489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004835609317704611937985 753626706988278458953489)
        ·
          refine ⟨565220030241208844215117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753626706988278458953489 565220030241208844215117)
          ·
            refine ⟨211957511340453316580669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565220030241208844215117 211957511340453316580669)
            ·
              refine ⟨79484066752669993717751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211957511340453316580669 79484066752669993717751)
              ·
                refine ⟨119226100129004990576627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79484066752669993717751 119226100129004990576627)
                ·
                  refine ⟨178839150193507485864941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119226100129004990576627 178839150193507485864941)
                  ·
                    refine ⟨67064681322565307199353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178839150193507485864941 67064681322565307199353)
                    ·
                      refine ⟨50298510991923980399515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67064681322565307199353 50298510991923980399515)
                      ·
                        rfl

theorem cell23_97956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_97956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97956 prefixEnd_97956 := by exact prefixLift 97956
  have htrace : WordTrace (prefixWord ++ tailWord_97956) baseStart_97956 baseEnd_97956 := by
    simpa [prefixWord, tailWord_97956, baseEnd_97956] using wordTrace_append hprefix tailTrace_97956
  have hstable : (prefixWord ++ tailWord_97956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97956).length < 2 ^ (prefixWord ++ tailWord_97956).sum := by decide
  have hdescent : baseEnd_97956 < baseStart_97956 := by decide
  rcases family_descends (prefixWord ++ tailWord_97956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97968 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_97968 : Nat := 118140960795 + 97968 * 2 ^ 59
def prefixEnd_97968 : Nat := 4983230072969 + 3 ^ 40 * 97968 * 2
def baseEnd_97968 : Nat := 50304672759777933449459

theorem tailTrace_97968 : CollatzResearch.WordTrace tailWord_97968 prefixEnd_97968 50304672759777933449459 := by
  unfold tailWord_97968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786593254543071223719279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2382124339390761631625705 1786593254543071223719279)
  ·
    refine ⟨2679889881814606835578919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786593254543071223719279 2679889881814606835578919)
    ·
      refine ⟨4019834822721910253368379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2679889881814606835578919 4019834822721910253368379)
      ·
        refine ⟨6029752234082865380052569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019834822721910253368379 6029752234082865380052569)
        ·
          refine ⟨4522314175562149035039427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6029752234082865380052569 4522314175562149035039427)
          ·
            refine ⟨6783471263343223552559141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522314175562149035039427 6783471263343223552559141)
            ·
              refine ⟨1271900861876854416104839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6783471263343223552559141 1271900861876854416104839)
              ·
                refine ⟨1907851292815281624157259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271900861876854416104839 1907851292815281624157259)
                ·
                  refine ⟨2861776939222922436235889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907851292815281624157259 2861776939222922436235889)
                  ·
                    refine ⟨2146332704417191827176917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861776939222922436235889 2146332704417191827176917)
                    ·
                      refine ⟨50304672759777933449459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2146332704417191827176917 50304672759777933449459)
                      ·
                        rfl

theorem cell23_97968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_97968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97968 prefixEnd_97968 := by exact prefixLift 97968
  have htrace : WordTrace (prefixWord ++ tailWord_97968) baseStart_97968 baseEnd_97968 := by
    simpa [prefixWord, tailWord_97968, baseEnd_97968] using wordTrace_append hprefix tailTrace_97968
  have hstable : (prefixWord ++ tailWord_97968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97968).length < 2 ^ (prefixWord ++ tailWord_97968).sum := by decide
  have hdescent : baseEnd_97968 < baseStart_97968 := by decide
  rcases family_descends (prefixWord ++ tailWord_97968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97982 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_97982 : Nat := 118140960795 + 97982 * 2 ^ 59
def prefixEnd_97982 : Nat := 4983230072969 + 3 ^ 40 * 97982 * 2
def baseEnd_97982 : Nat := 50311861488940878674395

theorem tailTrace_97982 : CollatzResearch.WordTrace tailWord_97982 prefixEnd_97982 50311861488940878674395 := by
  unfold tailWord_97982
  simp only [CollatzResearch.WordTrace]
  refine ⟨446712141379427854806025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2382464754023615225632133 446712141379427854806025)
  ·
    refine ⟨335034106034570891104519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 446712141379427854806025 335034106034570891104519)
    ·
      refine ⟨502551159051856336656779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335034106034570891104519 502551159051856336656779)
      ·
        refine ⟨753826738577784504985169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502551159051856336656779 753826738577784504985169)
        ·
          refine ⟨565370053933338378738877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753826738577784504985169 565370053933338378738877)
          ·
            refine ⟨212013770225001892027079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565370053933338378738877 212013770225001892027079)
            ·
              refine ⟨318020655337502838040619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212013770225001892027079 318020655337502838040619)
              ·
                refine ⟨477030983006254257060929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318020655337502838040619 477030983006254257060929)
                ·
                  refine ⟨357773237254690692795697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477030983006254257060929 357773237254690692795697)
                  ·
                    refine ⟨268329927941018019596773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357773237254690692795697 268329927941018019596773)
                    ·
                      refine ⟨50311861488940878674395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 268329927941018019596773 50311861488940878674395)
                      ·
                        rfl

theorem cell23_97982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_97982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_97982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_97982 prefixEnd_97982 := by exact prefixLift 97982
  have htrace : WordTrace (prefixWord ++ tailWord_97982) baseStart_97982 baseEnd_97982 := by
    simpa [prefixWord, tailWord_97982, baseEnd_97982] using wordTrace_append hprefix tailTrace_97982
  have hstable : (prefixWord ++ tailWord_97982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97982).length < 2 ^ (prefixWord ++ tailWord_97982).sum := by decide
  have hdescent : baseEnd_97982 < baseStart_97982 := by decide
  rcases family_descends (prefixWord ++ tailWord_97982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98025 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_98025 : Nat := 118140960795 + 98025 * 2 ^ 59
def prefixEnd_98025 : Nat := 4983230072969 + 3 ^ 40 * 98025 * 2
def baseEnd_98025 : Nat := 50333941157084210436697

theorem tailTrace_98025 : CollatzResearch.WordTrace tailWord_98025 prefixEnd_98025 50333941157084210436697 := by
  unfold tailWord_98025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575265469879641182263529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2383510313253094121509019 3575265469879641182263529)
  ·
    refine ⟨2681449102409730886697647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3575265469879641182263529 2681449102409730886697647)
    ·
      refine ⟨4022173653614596330046471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2681449102409730886697647 4022173653614596330046471)
      ·
        refine ⟨6033260480421894495069707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4022173653614596330046471 6033260480421894495069707)
        ·
          refine ⟨9049890720632841742604561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033260480421894495069707 9049890720632841742604561)
          ·
            refine ⟨6787418040474631306953421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9049890720632841742604561 6787418040474631306953421)
            ·
              refine ⟨2545281765177986740107533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6787418040474631306953421 2545281765177986740107533)
              ·
                refine ⟨954480661941745027540325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2545281765177986740107533 954480661941745027540325)
                ·
                  refine ⟨178965124114077192663811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 954480661941745027540325 178965124114077192663811)
                  ·
                    refine ⟨268447686171115788995717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178965124114077192663811 268447686171115788995717)
                    ·
                      refine ⟨50333941157084210436697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 268447686171115788995717 50333941157084210436697)
                      ·
                        rfl

theorem cell23_98025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_98025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98025 prefixEnd_98025 := by exact prefixLift 98025
  have htrace : WordTrace (prefixWord ++ tailWord_98025) baseStart_98025 baseEnd_98025 := by
    simpa [prefixWord, tailWord_98025, baseEnd_98025] using wordTrace_append hprefix tailTrace_98025
  have hstable : (prefixWord ++ tailWord_98025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98025).length < 2 ^ (prefixWord ++ tailWord_98025).sum := by decide
  have hdescent : baseEnd_98025 < baseStart_98025 := by decide
  rcases family_descends (prefixWord ++ tailWord_98025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98036 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_98036 : Nat := 118140960795 + 98036 * 2 ^ 59
def prefixEnd_98036 : Nat := 4983230072969 + 3 ^ 40 * 98036 * 2
def baseEnd_98036 : Nat := 50339589444283667399147

theorem tailTrace_98036 : CollatzResearch.WordTrace tailWord_98036 prefixEnd_98036 50339589444283667399147 := by
  unfold tailWord_98036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787833336419895030456981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2383777781893193373942641 1787833336419895030456981)
  ·
    refine ⟨83804687644682579552671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1787833336419895030456981 83804687644682579552671)
    ·
      refine ⟨125707031467023869329007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83804687644682579552671 125707031467023869329007)
      ·
        refine ⟨188560547200535803993511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125707031467023869329007 188560547200535803993511)
        ·
          refine ⟨282840820800803705990267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188560547200535803993511 282840820800803705990267)
          ·
            refine ⟨424261231201205558985401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282840820800803705990267 424261231201205558985401)
            ·
              refine ⟨318195923400904169239051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424261231201205558985401 318195923400904169239051)
              ·
                refine ⟨477293885101356253858577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318195923400904169239051 477293885101356253858577)
                ·
                  refine ⟨357970413826017190393933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477293885101356253858577 357970413826017190393933)
                  ·
                    refine ⟨134238905184756446397725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357970413826017190393933 134238905184756446397725)
                    ·
                      refine ⟨50339589444283667399147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134238905184756446397725 50339589444283667399147)
                      ·
                        rfl

theorem cell23_98036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_98036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98036 prefixEnd_98036 := by exact prefixLift 98036
  have htrace : WordTrace (prefixWord ++ tailWord_98036) baseStart_98036 baseEnd_98036 := by
    simpa [prefixWord, tailWord_98036, baseEnd_98036] using wordTrace_append hprefix tailTrace_98036
  have hstable : (prefixWord ++ tailWord_98036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98036).length < 2 ^ (prefixWord ++ tailWord_98036).sum := by decide
  have hdescent : baseEnd_98036 < baseStart_98036 := by decide
  rcases family_descends (prefixWord ++ tailWord_98036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98062 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_98062 : Nat := 118140960795 + 98062 * 2 ^ 59
def prefixEnd_98062 : Nat := 4983230072969 + 3 ^ 40 * 98062 * 2
def baseEnd_98062 : Nat := 50352939941300565674027

theorem tailTrace_98062 : CollatzResearch.WordTrace tailWord_98062 prefixEnd_98062 50352939941300565674027 := by
  unfold tailWord_98062
  simp only [CollatzResearch.WordTrace]
  refine ⟨447076871343199562670055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2384409980497064334240293 447076871343199562670055)
  ·
    refine ⟨670615307014799344005083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 447076871343199562670055 670615307014799344005083)
    ·
      refine ⟨1005922960522199016007625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670615307014799344005083 1005922960522199016007625)
      ·
        refine ⟨754442220391649262005719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1005922960522199016007625 754442220391649262005719)
        ·
          refine ⟨1131663330587473893008579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754442220391649262005719 1131663330587473893008579)
          ·
            refine ⟨1697494995881210839512869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131663330587473893008579 1697494995881210839512869)
            ·
              refine ⟨318280311727727032408663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1697494995881210839512869 318280311727727032408663)
              ·
                refine ⟨477420467591590548612995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318280311727727032408663 477420467591590548612995)
                ·
                  refine ⟨716130701387385822919493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477420467591590548612995 716130701387385822919493)
                  ·
                    refine ⟨134274506510134841797405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 716130701387385822919493 134274506510134841797405)
                    ·
                      refine ⟨50352939941300565674027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134274506510134841797405 50352939941300565674027)
                      ·
                        rfl

theorem cell23_98062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_98062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98062 prefixEnd_98062 := by exact prefixLift 98062
  have htrace : WordTrace (prefixWord ++ tailWord_98062) baseStart_98062 baseEnd_98062 := by
    simpa [prefixWord, tailWord_98062, baseEnd_98062] using wordTrace_append hprefix tailTrace_98062
  have hstable : (prefixWord ++ tailWord_98062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98062).length < 2 ^ (prefixWord ++ tailWord_98062).sum := by decide
  have hdescent : baseEnd_98062 < baseStart_98062 := by decide
  rcases family_descends (prefixWord ++ tailWord_98062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98075 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 3]
def baseStart_98075 : Nat := 118140960795 + 98075 * 2 ^ 59
def prefixEnd_98075 : Nat := 4983230072969 + 3 ^ 40 * 98075 * 2
def baseEnd_98075 : Nat := 50359615189809014811467

theorem tailTrace_98075 : CollatzResearch.WordTrace tailWord_98075 prefixEnd_98075 50359615189809014811467 := by
  unfold tailWord_98075
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577089119698499721583679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2384726079798999814389119 3577089119698499721583679)
  ·
    refine ⟨5365633679547749582375519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3577089119698499721583679 5365633679547749582375519)
    ·
      refine ⟨8048450519321624373563279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5365633679547749582375519 8048450519321624373563279)
      ·
        refine ⟨12072675778982436560344919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8048450519321624373563279 12072675778982436560344919)
        ·
          refine ⟨18109013668473654840517379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12072675778982436560344919 18109013668473654840517379)
          ·
            refine ⟨27163520502710482260776069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18109013668473654840517379 27163520502710482260776069)
            ·
              refine ⟨5093160094258215423895513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27163520502710482260776069 5093160094258215423895513)
              ·
                refine ⟨3819870070693661567921635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093160094258215423895513 3819870070693661567921635)
                ·
                  refine ⟨5729805106040492351882453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819870070693661567921635 5729805106040492351882453)
                  ·
                    refine ⟨134292307172824039497245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5729805106040492351882453 134292307172824039497245)
                    ·
                      refine ⟨50359615189809014811467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134292307172824039497245 50359615189809014811467)
                      ·
                        rfl

theorem cell23_98075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 3].length) (baseStart_98075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98075 prefixEnd_98075 := by exact prefixLift 98075
  have htrace : WordTrace (prefixWord ++ tailWord_98075) baseStart_98075 baseEnd_98075 := by
    simpa [prefixWord, tailWord_98075, baseEnd_98075] using wordTrace_append hprefix tailTrace_98075
  have hstable : (prefixWord ++ tailWord_98075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98075).length < 2 ^ (prefixWord ++ tailWord_98075).sum := by decide
  have hdescent : baseEnd_98075 < baseStart_98075 := by decide
  rcases family_descends (prefixWord ++ tailWord_98075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98082 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_98082 : Nat := 118140960795 + 98082 * 2 ^ 59
def prefixEnd_98082 : Nat := 4983230072969 + 3 ^ 40 * 98082 * 2
def baseEnd_98082 : Nat := 5595912172710054158215

theorem tailTrace_98082 : CollatzResearch.WordTrace tailWord_98082 prefixEnd_98082 5595912172710054158215 := by
  unfold tailWord_98082
  simp only [CollatzResearch.WordTrace]
  refine ⟨894336107668284979272125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2384896287115426611392333 894336107668284979272125)
  ·
    refine ⟨335376040375606867227047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 894336107668284979272125 335376040375606867227047)
    ·
      refine ⟨503064060563410300840571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335376040375606867227047 503064060563410300840571)
      ·
        refine ⟨754596090845115451260857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503064060563410300840571 754596090845115451260857)
        ·
          refine ⟨565947068133836588445643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 754596090845115451260857 565947068133836588445643)
          ·
            refine ⟨848920602200754882668465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565947068133836588445643 848920602200754882668465)
            ·
              refine ⟨636690451650566162001349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848920602200754882668465 636690451650566162001349)
              ·
                refine ⟨119379459684481155375253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 636690451650566162001349 119379459684481155375253)
                ·
                  refine ⟨5595912172710054158215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119379459684481155375253 5595912172710054158215)
                  ·
                    rfl

theorem cell23_98082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_98082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98082 prefixEnd_98082 := by exact prefixLift 98082
  have htrace : WordTrace (prefixWord ++ tailWord_98082) baseStart_98082 baseEnd_98082 := by
    simpa [prefixWord, tailWord_98082, baseEnd_98082] using wordTrace_append hprefix tailTrace_98082
  have hstable : (prefixWord ++ tailWord_98082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98082).length < 2 ^ (prefixWord ++ tailWord_98082).sum := by decide
  have hdescent : baseEnd_98082 < baseStart_98082 := by decide
  rcases family_descends (prefixWord ++ tailWord_98082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98095 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 5, 5]
def baseStart_98095 : Nat := 118140960795 + 98095 * 2 ^ 59
def prefixEnd_98095 : Nat := 4983230072969 + 3 ^ 40 * 98095 * 2
def baseEnd_98095 : Nat := 16789961600966312187125

theorem tailTrace_98095 : CollatzResearch.WordTrace tailWord_98095 prefixEnd_98095 16789961600966312187125 := by
  unfold tailWord_98095
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577818579626043137311739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2385212386417362091541159 3577818579626043137311739)
  ·
    refine ⟨5366727869439064705967609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3577818579626043137311739 5366727869439064705967609)
    ·
      refine ⟨4025045902079298529475707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5366727869439064705967609 4025045902079298529475707)
      ·
        refine ⟨6037568853118947794213561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025045902079298529475707 6037568853118947794213561)
        ·
          refine ⟨4528176639839210845660171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6037568853118947794213561 4528176639839210845660171)
          ·
            refine ⟨6792264959758816268490257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528176639839210845660171 6792264959758816268490257)
            ·
              refine ⟨5094198719819112201367693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6792264959758816268490257 5094198719819112201367693)
              ·
                refine ⟨1910324519932167075512885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5094198719819112201367693 1910324519932167075512885)
                ·
                  refine ⟨179092923743640663329333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910324519932167075512885 179092923743640663329333)
                  ·
                    refine ⟨16789961600966312187125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179092923743640663329333 16789961600966312187125)
                    ·
                      rfl

theorem cell23_98095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_98095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98095 prefixEnd_98095 := by exact prefixLift 98095
  have htrace : WordTrace (prefixWord ++ tailWord_98095) baseStart_98095 baseEnd_98095 := by
    simpa [prefixWord, tailWord_98095, baseEnd_98095] using wordTrace_append hprefix tailTrace_98095
  have hstable : (prefixWord ++ tailWord_98095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98095).length < 2 ^ (prefixWord ++ tailWord_98095).sum := by decide
  have hdescent : baseEnd_98095 < baseStart_98095 := by decide
  rcases family_descends (prefixWord ++ tailWord_98095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98119 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_98119 : Nat := 118140960795 + 98119 * 2 ^ 59
def prefixEnd_98119 : Nat := 4983230072969 + 3 ^ 40 * 98119 * 2
def baseEnd_98119 : Nat := 50382208338606842661265

theorem tailTrace_98119 : CollatzResearch.WordTrace tailWord_98119 prefixEnd_98119 50382208338606842661265 := by
  unfold tailWord_98119
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578693931539095236185411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2385795954359396824123607 3578693931539095236185411)
  ·
    refine ⟨5368040897308642854278117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578693931539095236185411 5368040897308642854278117)
    ·
      refine ⟨1006507668245370535177147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5368040897308642854278117 1006507668245370535177147)
      ·
        refine ⟨1509761502368055802765721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006507668245370535177147 1509761502368055802765721)
        ·
          refine ⟨1132321126776041852074291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1509761502368055802765721 1132321126776041852074291)
          ·
            refine ⟨1698481690164062778111437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132321126776041852074291 1698481690164062778111437)
            ·
              refine ⟨636930633811523541791789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1698481690164062778111437 636930633811523541791789)
              ·
                refine ⟨238848987679321328171921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 636930633811523541791789 238848987679321328171921)
                ·
                  refine ⟨179136740759490996128941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238848987679321328171921 179136740759490996128941)
                  ·
                    refine ⟨67176277784809123548353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179136740759490996128941 67176277784809123548353)
                    ·
                      refine ⟨50382208338606842661265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67176277784809123548353 50382208338606842661265)
                      ·
                        rfl

theorem cell23_98119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_98119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98119 prefixEnd_98119 := by exact prefixLift 98119
  have htrace : WordTrace (prefixWord ++ tailWord_98119) baseStart_98119 baseEnd_98119 := by
    simpa [prefixWord, tailWord_98119, baseEnd_98119] using wordTrace_append hprefix tailTrace_98119
  have hstable : (prefixWord ++ tailWord_98119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98119).length < 2 ^ (prefixWord ++ tailWord_98119).sum := by decide
  have hdescent : baseEnd_98119 < baseStart_98119 := by decide
  rcases family_descends (prefixWord ++ tailWord_98119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98143 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 1, 1, 3]
def baseStart_98143 : Nat := 118140960795 + 98143 * 2 ^ 59
def prefixEnd_98143 : Nat := 4983230072969 + 3 ^ 40 * 98143 * 2
def baseEnd_98143 : Nat := 50394531874314748761155

theorem tailTrace_98143 : CollatzResearch.WordTrace tailWord_98143 prefixEnd_98143 50394531874314748761155 := by
  unfold tailWord_98143
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579569283452147335059083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2386379522301431556706055 3579569283452147335059083)
  ·
    refine ⟨5369353925178221002588625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3579569283452147335059083 5369353925178221002588625)
    ·
      refine ⟨4027015443883665751941469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5369353925178221002588625 4027015443883665751941469)
      ·
        refine ⟨1510130791456374656978051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4027015443883665751941469 1510130791456374656978051)
        ·
          refine ⟨2265196187184561985467077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510130791456374656978051 2265196187184561985467077)
          ·
            refine ⟨424724285097105372275077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2265196187184561985467077 424724285097105372275077)
            ·
              refine ⟨79635803455707257301577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 424724285097105372275077 79635803455707257301577)
              ·
                refine ⟨59726852591780442976183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79635803455707257301577 59726852591780442976183)
                ·
                  refine ⟨89590278887670664464275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59726852591780442976183 89590278887670664464275)
                  ·
                    refine ⟨134385418331505996696413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89590278887670664464275 134385418331505996696413)
                    ·
                      refine ⟨50394531874314748761155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134385418331505996696413 50394531874314748761155)
                      ·
                        rfl

theorem cell23_98143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_98143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98143 prefixEnd_98143 := by exact prefixLift 98143
  have htrace : WordTrace (prefixWord ++ tailWord_98143) baseStart_98143 baseEnd_98143 := by
    simpa [prefixWord, tailWord_98143, baseEnd_98143] using wordTrace_append hprefix tailTrace_98143
  have hstable : (prefixWord ++ tailWord_98143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98143).length < 2 ^ (prefixWord ++ tailWord_98143).sum := by decide
  have hdescent : baseEnd_98143 < baseStart_98143 := by decide
  rcases family_descends (prefixWord ++ tailWord_98143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98152 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_98152 : Nat := 118140960795 + 98152 * 2 ^ 59
def prefixEnd_98152 : Nat := 4983230072969 + 3 ^ 40 * 98152 * 2
def baseEnd_98152 : Nat := 50399153200205213548613

theorem tailTrace_98152 : CollatzResearch.WordTrace tailWord_98152 prefixEnd_98152 50399153200205213548613 := by
  unfold tailWord_98152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789948770209770936068355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2386598360279694581424473 1789948770209770936068355)
  ·
    refine ⟨2684923155314656404102533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1789948770209770936068355 2684923155314656404102533)
    ·
      refine ⟨503423091621498075769225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2684923155314656404102533 503423091621498075769225)
      ·
        refine ⟨377567318716123556826919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503423091621498075769225 377567318716123556826919)
        ·
          refine ⟨566350978074185335240379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377567318716123556826919 566350978074185335240379)
          ·
            refine ⟨849526467111278002860569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566350978074185335240379 849526467111278002860569)
            ·
              refine ⟨637144850333458502145427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849526467111278002860569 637144850333458502145427)
              ·
                refine ⟨955717275500187753218141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637144850333458502145427 955717275500187753218141)
                ·
                  refine ⟨358393978312570407456803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 955717275500187753218141 358393978312570407456803)
                  ·
                    refine ⟨537590967468855611185205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358393978312570407456803 537590967468855611185205)
                    ·
                      refine ⟨50399153200205213548613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 537590967468855611185205 50399153200205213548613)
                      ·
                        rfl

theorem cell23_98152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_98152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98152 prefixEnd_98152 := by exact prefixLift 98152
  have htrace : WordTrace (prefixWord ++ tailWord_98152) baseStart_98152 baseEnd_98152 := by
    simpa [prefixWord, tailWord_98152, baseEnd_98152] using wordTrace_append hprefix tailTrace_98152
  have hstable : (prefixWord ++ tailWord_98152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98152).length < 2 ^ (prefixWord ++ tailWord_98152).sum := by decide
  have hdescent : baseEnd_98152 < baseStart_98152 := by decide
  rcases family_descends (prefixWord ++ tailWord_98152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98169 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 3]
def baseStart_98169 : Nat := 118140960795 + 98169 * 2 ^ 59
def prefixEnd_98169 : Nat := 4983230072969 + 3 ^ 40 * 98169 * 2
def baseEnd_98169 : Nat := 50407882371331647036035

theorem tailTrace_98169 : CollatzResearch.WordTrace tailWord_98169 prefixEnd_98169 50407882371331647036035 := by
  unfold tailWord_98169
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580517581357953775505561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2387011720905302517003707 3580517581357953775505561)
  ·
    refine ⟨2685388186018465331629171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3580517581357953775505561 2685388186018465331629171)
    ·
      refine ⟨4028082279027697997443757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685388186018465331629171 4028082279027697997443757)
      ·
        refine ⟨1510530854635386749041409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4028082279027697997443757 1510530854635386749041409)
        ·
          refine ⟨1132898140976540061781057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510530854635386749041409 1132898140976540061781057)
          ·
            refine ⟨849673605732405046335793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132898140976540061781057 849673605732405046335793)
            ·
              refine ⟨637255204299303784751845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849673605732405046335793 637255204299303784751845)
              ·
                refine ⟨119485350806119459640971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637255204299303784751845 119485350806119459640971)
                ·
                  refine ⟨179228026209179189461457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119485350806119459640971 179228026209179189461457)
                  ·
                    refine ⟨134421019656884392096093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 179228026209179189461457 134421019656884392096093)
                    ·
                      refine ⟨50407882371331647036035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134421019656884392096093 50407882371331647036035)
                      ·
                        rfl

theorem cell23_98169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_98169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98169 prefixEnd_98169 := by exact prefixLift 98169
  have htrace : WordTrace (prefixWord ++ tailWord_98169) baseStart_98169 baseEnd_98169 := by
    simpa [prefixWord, tailWord_98169, baseEnd_98169] using wordTrace_append hprefix tailTrace_98169
  have hstable : (prefixWord ++ tailWord_98169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98169).length < 2 ^ (prefixWord ++ tailWord_98169).sum := by decide
  have hdescent : baseEnd_98169 < baseStart_98169 := by decide
  rcases family_descends (prefixWord ++ tailWord_98169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98183 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_98183 : Nat := 118140960795 + 98183 * 2 ^ 59
def prefixEnd_98183 : Nat := 4983230072969 + 3 ^ 40 * 98183 * 2
def baseEnd_98183 : Nat := 50415071100494592260971

theorem tailTrace_98183 : CollatzResearch.WordTrace tailWord_98183 prefixEnd_98183 50415071100494592260971 := by
  unfold tailWord_98183
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581028203307234166515203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2387352135538156111010135 3581028203307234166515203)
  ·
    refine ⟨5371542304960851249772805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3581028203307234166515203 5371542304960851249772805)
    ·
      refine ⟨1007164182180159609332401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5371542304960851249772805 1007164182180159609332401)
      ·
        refine ⟨755373136635119706999301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1007164182180159609332401 755373136635119706999301)
        ·
          refine ⟨141632463119084945062369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 755373136635119706999301 141632463119084945062369)
          ·
            refine ⟨106224347339313708796777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141632463119084945062369 106224347339313708796777)
            ·
              refine ⟨79668260504485281597583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106224347339313708796777 79668260504485281597583)
              ·
                refine ⟨119502390756727922396375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79668260504485281597583 119502390756727922396375)
                ·
                  refine ⟨179253586135091883594563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119502390756727922396375 179253586135091883594563)
                  ·
                    refine ⟨268880379202637825391845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179253586135091883594563 268880379202637825391845)
                    ·
                      refine ⟨50415071100494592260971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 268880379202637825391845 50415071100494592260971)
                      ·
                        rfl

theorem cell23_98183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_98183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98183 prefixEnd_98183 := by exact prefixLift 98183
  have htrace : WordTrace (prefixWord ++ tailWord_98183) baseStart_98183 baseEnd_98183 := by
    simpa [prefixWord, tailWord_98183, baseEnd_98183] using wordTrace_append hprefix tailTrace_98183
  have hstable : (prefixWord ++ tailWord_98183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98183).length < 2 ^ (prefixWord ++ tailWord_98183).sum := by decide
  have hdescent : baseEnd_98183 < baseStart_98183 := by decide
  rcases family_descends (prefixWord ++ tailWord_98183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98200 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 3, 2, 2]
def baseStart_98200 : Nat := 118140960795 + 98200 * 2 ^ 59
def prefixEnd_98200 : Nat := 4983230072969 + 3 ^ 40 * 98200 * 2
def baseEnd_98200 : Nat := 50423800271621025748393

theorem tailTrace_98200 : CollatzResearch.WordTrace tailWord_98200 prefixEnd_98200 50423800271621025748393 := by
  unfold tailWord_98200
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790824122122823034942027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2387765496163764046589369 1790824122122823034942027)
  ·
    refine ⟨2686236183184234552413041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790824122122823034942027 2686236183184234552413041)
    ·
      refine ⟨2014677137388175914309781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2686236183184234552413041 2014677137388175914309781)
      ·
        refine ⟨94437990815070745983271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2014677137388175914309781 94437990815070745983271)
        ·
          refine ⟨141656986222606118974907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94437990815070745983271 141656986222606118974907)
          ·
            refine ⟨212485479333909178462361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141656986222606118974907 212485479333909178462361)
            ·
              refine ⟨159364109500431883846771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212485479333909178462361 159364109500431883846771)
              ·
                refine ⟨239046164250647825770157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159364109500431883846771 239046164250647825770157)
                ·
                  refine ⟨89642311593992934663809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239046164250647825770157 89642311593992934663809)
                  ·
                    refine ⟨67231733695494700997857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89642311593992934663809 67231733695494700997857)
                    ·
                      refine ⟨50423800271621025748393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67231733695494700997857 50423800271621025748393)
                      ·
                        rfl

theorem cell23_98200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_98200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98200 prefixEnd_98200 := by exact prefixLift 98200
  have htrace : WordTrace (prefixWord ++ tailWord_98200) baseStart_98200 baseEnd_98200 := by
    simpa [prefixWord, tailWord_98200, baseEnd_98200] using wordTrace_append hprefix tailTrace_98200
  have hstable : (prefixWord ++ tailWord_98200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98200).length < 2 ^ (prefixWord ++ tailWord_98200).sum := by decide
  have hdescent : baseEnd_98200 < baseStart_98200 := by decide
  rcases family_descends (prefixWord ++ tailWord_98200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98239 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 3, 4, 2]
def baseStart_98239 : Nat := 118140960795 + 98239 * 2 ^ 59
def prefixEnd_98239 : Nat := 4983230072969 + 3 ^ 40 * 98239 * 2
def baseEnd_98239 : Nat := 50443826017146373160713

theorem tailTrace_98239 : CollatzResearch.WordTrace tailWord_98239 prefixEnd_98239 50443826017146373160713 := by
  unfold tailWord_98239
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583070691104355730553771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2388713794069570487035847 3583070691104355730553771)
  ·
    refine ⟨5374606036656533595830657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583070691104355730553771 5374606036656533595830657)
    ·
      refine ⟨4030954527492400196872993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5374606036656533595830657 4030954527492400196872993)
      ·
        refine ⟨3023215895619300147654745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4030954527492400196872993 3023215895619300147654745)
        ·
          refine ⟨2267411921714475110741059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023215895619300147654745 2267411921714475110741059)
          ·
            refine ⟨3401117882571712666111589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267411921714475110741059 3401117882571712666111589)
            ·
              refine ⟨637709602982196124895923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3401117882571712666111589 637709602982196124895923)
              ·
                refine ⟨956564404473294187343885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637709602982196124895923 956564404473294187343885)
                ·
                  refine ⟨358711651677485320253957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956564404473294187343885 358711651677485320253957)
                  ·
                    refine ⟨67258434689528497547617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358711651677485320253957 67258434689528497547617)
                    ·
                      refine ⟨50443826017146373160713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67258434689528497547617 50443826017146373160713)
                      ·
                        rfl

theorem cell23_98239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_98239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98239 prefixEnd_98239 := by exact prefixLift 98239
  have htrace : WordTrace (prefixWord ++ tailWord_98239) baseStart_98239 baseEnd_98239 := by
    simpa [prefixWord, tailWord_98239, baseEnd_98239] using wordTrace_append hprefix tailTrace_98239
  have hstable : (prefixWord ++ tailWord_98239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98239).length < 2 ^ (prefixWord ++ tailWord_98239).sum := by decide
  have hdescent : baseEnd_98239 < baseStart_98239 := by decide
  rcases family_descends (prefixWord ++ tailWord_98239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98256 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 4, 2, 2]
def baseStart_98256 : Nat := 118140960795 + 98256 * 2 ^ 59
def prefixEnd_98256 : Nat := 4983230072969 + 3 ^ 40 * 98256 * 2
def baseEnd_98256 : Nat := 50452555188272806648135

theorem tailTrace_98256 : CollatzResearch.WordTrace tailWord_98256 prefixEnd_98256 50452555188272806648135 := by
  unfold tailWord_98256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791845366021383816961311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2389127154695178422615081 1791845366021383816961311)
  ·
    refine ⟨2687768049032075725441967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791845366021383816961311 2687768049032075725441967)
    ·
      refine ⟨4031652073548113588162951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2687768049032075725441967 4031652073548113588162951)
      ·
        refine ⟨6047478110322170382244427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031652073548113588162951 6047478110322170382244427)
        ·
          refine ⟨9071217165483255573366641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047478110322170382244427 9071217165483255573366641)
          ·
            refine ⟨6803412874112441680024981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9071217165483255573366641 6803412874112441680024981)
            ·
              refine ⟨318909978474020703751171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6803412874112441680024981 318909978474020703751171)
              ·
                refine ⟨478364967711031055626757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318909978474020703751171 478364967711031055626757)
                ·
                  refine ⟨89693431445818322930017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478364967711031055626757 89693431445818322930017)
                  ·
                    refine ⟨67270073584363742197513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89693431445818322930017 67270073584363742197513)
                    ·
                      refine ⟨50452555188272806648135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67270073584363742197513 50452555188272806648135)
                      ·
                        rfl

theorem cell23_98256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 2, 2].length) (baseStart_98256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98256 prefixEnd_98256 := by exact prefixLift 98256
  have htrace : WordTrace (prefixWord ++ tailWord_98256) baseStart_98256 baseEnd_98256 := by
    simpa [prefixWord, tailWord_98256, baseEnd_98256] using wordTrace_append hprefix tailTrace_98256
  have hstable : (prefixWord ++ tailWord_98256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98256).length < 2 ^ (prefixWord ++ tailWord_98256).sum := by decide
  have hdescent : baseEnd_98256 < baseStart_98256 := by decide
  rcases family_descends (prefixWord ++ tailWord_98256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98309 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_98309 : Nat := 118140960795 + 98309 * 2 ^ 59
def prefixEnd_98309 : Nat := 4983230072969 + 3 ^ 40 * 98309 * 2
def baseEnd_98309 : Nat := 16826589887653699761797

theorem tailTrace_98309 : CollatzResearch.WordTrace tailWord_98309 prefixEnd_98309 16826589887653699761797 := by
  unfold tailWord_98309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585623800850757685601981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2390415867233838457067987 3585623800850757685601981)
  ·
    refine ⟨1344608925319034132100743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3585623800850757685601981 1344608925319034132100743)
    ·
      refine ⟨2016913387978551198151115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344608925319034132100743 2016913387978551198151115)
      ·
        refine ⟨3025370081967826797226673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016913387978551198151115 3025370081967826797226673)
        ·
          refine ⟨2269027561475870097920005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3025370081967826797226673 2269027561475870097920005)
          ·
            refine ⟨425442667776725643360001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2269027561475870097920005 425442667776725643360001)
            ·
              refine ⟨319082000832544232520001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425442667776725643360001 319082000832544232520001)
              ·
                refine ⟨239311500624408174390001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319082000832544232520001 239311500624408174390001)
                ·
                  refine ⟨179483625468306130792501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239311500624408174390001 179483625468306130792501)
                  ·
                    refine ⟨16826589887653699761797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179483625468306130792501 16826589887653699761797)
                    ·
                      rfl

theorem cell23_98309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_98309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98309 prefixEnd_98309 := by exact prefixLift 98309
  have htrace : WordTrace (prefixWord ++ tailWord_98309) baseStart_98309 baseEnd_98309 := by
    simpa [prefixWord, tailWord_98309, baseEnd_98309] using wordTrace_append hprefix tailTrace_98309
  have hstable : (prefixWord ++ tailWord_98309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98309).length < 2 ^ (prefixWord ++ tailWord_98309).sum := by decide
  have hdescent : baseEnd_98309 < baseStart_98309 := by decide
  rcases family_descends (prefixWord ++ tailWord_98309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98346 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_98346 : Nat := 118140960795 + 98346 * 2 ^ 59
def prefixEnd_98346 : Nat := 4983230072969 + 3 ^ 40 * 98346 * 2
def baseEnd_98346 : Nat := 50498768447177454522721

theorem tailTrace_98346 : CollatzResearch.WordTrace tailWord_98346 prefixEnd_98346 50498768447177454522721 := by
  unfold tailWord_98346
  simp only [CollatzResearch.WordTrace]
  refine ⟨896743325429178251174723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2391315534477808669799261 896743325429178251174723)
  ·
    refine ⟨1345114988143767376762085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 896743325429178251174723 1345114988143767376762085)
    ·
      refine ⟨252209060276956383142891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1345114988143767376762085 252209060276956383142891)
      ·
        refine ⟨378313590415434574714337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252209060276956383142891 378313590415434574714337)
        ·
          refine ⟨283735192811575931035753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378313590415434574714337 283735192811575931035753)
          ·
            refine ⟨212801394608681948276815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283735192811575931035753 212801394608681948276815)
            ·
              refine ⟨319202091913022922415223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212801394608681948276815 319202091913022922415223)
              ·
                refine ⟨478803137869534383622835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319202091913022922415223 478803137869534383622835)
                ·
                  refine ⟨718204706804301575434253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478803137869534383622835 718204706804301575434253)
                  ·
                    refine ⟨269326765051613090787845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 718204706804301575434253 269326765051613090787845)
                    ·
                      refine ⟨50498768447177454522721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 269326765051613090787845 50498768447177454522721)
                      ·
                        rfl

theorem cell23_98346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_98346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98346 prefixEnd_98346 := by exact prefixLift 98346
  have htrace : WordTrace (prefixWord ++ tailWord_98346) baseStart_98346 baseEnd_98346 := by
    simpa [prefixWord, tailWord_98346, baseEnd_98346] using wordTrace_append hprefix tailTrace_98346
  have hstable : (prefixWord ++ tailWord_98346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98346).length < 2 ^ (prefixWord ++ tailWord_98346).sum := by decide
  have hdescent : baseEnd_98346 < baseStart_98346 := by decide
  rcases family_descends (prefixWord ++ tailWord_98346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98390 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_98390 : Nat := 118140960795 + 98390 * 2 ^ 59
def prefixEnd_98390 : Nat := 4983230072969 + 3 ^ 40 * 98390 * 2
def baseEnd_98390 : Nat := 16840453865325094124173

theorem tailTrace_98390 : CollatzResearch.WordTrace tailWord_98390 prefixEnd_98390 16840453865325094124173 := by
  unfold tailWord_98390
  simp only [CollatzResearch.WordTrace]
  refine ⟨224286132097331782456289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2392385409038205679533749 224286132097331782456289)
  ·
    refine ⟨168214599072998836842217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224286132097331782456289 168214599072998836842217)
    ·
      refine ⟨126160949304749127631663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168214599072998836842217 126160949304749127631663)
      ·
        refine ⟨189241423957123691447495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126160949304749127631663 189241423957123691447495)
        ·
          refine ⟨283862135935685537171243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189241423957123691447495 283862135935685537171243)
          ·
            refine ⟨425793203903528305756865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283862135935685537171243 425793203903528305756865)
            ·
              refine ⟨319344902927646229317649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425793203903528305756865 319344902927646229317649)
              ·
                refine ⟨239508677195734671988237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319344902927646229317649 239508677195734671988237)
                ·
                  refine ⟨89815753948400501995589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239508677195734671988237 89815753948400501995589)
                  ·
                    refine ⟨16840453865325094124173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89815753948400501995589 16840453865325094124173)
                    ·
                      rfl

theorem cell23_98390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_98390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98390 prefixEnd_98390 := by exact prefixLift 98390
  have htrace : WordTrace (prefixWord ++ tailWord_98390) baseStart_98390 baseEnd_98390 := by
    simpa [prefixWord, tailWord_98390, baseEnd_98390] using wordTrace_append hprefix tailTrace_98390
  have hstable : (prefixWord ++ tailWord_98390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98390).length < 2 ^ (prefixWord ++ tailWord_98390).sum := by decide
  have hdescent : baseEnd_98390 < baseStart_98390 := by decide
  rcases family_descends (prefixWord ++ tailWord_98390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98416 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 1, 5]
def baseStart_98416 : Nat := 118140960795 + 98416 * 2 ^ 59
def prefixEnd_98416 : Nat := 4983230072969 + 3 ^ 40 * 98416 * 2
def baseEnd_98416 : Nat := 16844904030997393549133

theorem tailTrace_98416 : CollatzResearch.WordTrace tailWord_98416 prefixEnd_98416 16844904030997393549133 := by
  unfold tailWord_98416
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794763205731557479873551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2393017607642076639831401 1794763205731557479873551)
  ·
    refine ⟨2692144808597336219810327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1794763205731557479873551 2692144808597336219810327)
    ·
      refine ⟨4038217212896004329715491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692144808597336219810327 4038217212896004329715491)
      ·
        refine ⟨6057325819344006494573237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038217212896004329715491 6057325819344006494573237)
        ·
          refine ⟨567874295563500608866241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6057325819344006494573237 567874295563500608866241)
          ·
            refine ⟨425905721672625456649681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567874295563500608866241 425905721672625456649681)
            ·
              refine ⟨319429291254469092487261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425905721672625456649681 319429291254469092487261)
              ·
                refine ⟨119785984220425909682723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319429291254469092487261 119785984220425909682723)
                ·
                  refine ⟨179678976330638864524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119785984220425909682723 179678976330638864524085)
                  ·
                    refine ⟨16844904030997393549133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179678976330638864524085 16844904030997393549133)
                    ·
                      rfl

theorem cell23_98416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_98416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98416 prefixEnd_98416 := by exact prefixLift 98416
  have htrace : WordTrace (prefixWord ++ tailWord_98416) baseStart_98416 baseEnd_98416 := by
    simpa [prefixWord, tailWord_98416, baseEnd_98416] using wordTrace_append hprefix tailTrace_98416
  have hstable : (prefixWord ++ tailWord_98416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98416).length < 2 ^ (prefixWord ++ tailWord_98416).sum := by decide
  have hdescent : baseEnd_98416 < baseStart_98416 := by decide
  rcases family_descends (prefixWord ++ tailWord_98416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98423 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 2, 3, 2]
def baseStart_98423 : Nat := 118140960795 + 98423 * 2 ^ 59
def prefixEnd_98423 : Nat := 4983230072969 + 3 ^ 40 * 98423 * 2
def baseEnd_98423 : Nat := 50538306457573653259867

theorem tailTrace_98423 : CollatzResearch.WordTrace tailWord_98423 prefixEnd_98423 50538306457573653259867 := by
  unfold tailWord_98423
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589781722437755155251923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2393187814958503436834615 3589781722437755155251923)
  ·
    refine ⟨5384672583656632732877885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3589781722437755155251923 5384672583656632732877885)
    ·
      refine ⟨2019252218871237274829207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5384672583656632732877885 2019252218871237274829207)
      ·
        refine ⟨3028878328306855912243811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019252218871237274829207 3028878328306855912243811)
        ·
          refine ⟨4543317492460283868365717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028878328306855912243811 4543317492460283868365717)
          ·
            refine ⟨212968007459075806329643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4543317492460283868365717 212968007459075806329643)
            ·
              refine ⟨319452011188613709494465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212968007459075806329643 319452011188613709494465)
              ·
                refine ⟨239589008391460282120849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319452011188613709494465 239589008391460282120849)
                ·
                  refine ⟨179691756293595211590637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239589008391460282120849 179691756293595211590637)
                  ·
                    refine ⟨67384408610098204346489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179691756293595211590637 67384408610098204346489)
                    ·
                      refine ⟨50538306457573653259867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67384408610098204346489 50538306457573653259867)
                      ·
                        rfl

theorem cell23_98423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_98423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98423 prefixEnd_98423 := by exact prefixLift 98423
  have htrace : WordTrace (prefixWord ++ tailWord_98423) baseStart_98423 baseEnd_98423 := by
    simpa [prefixWord, tailWord_98423, baseEnd_98423] using wordTrace_append hprefix tailTrace_98423
  have hstable : (prefixWord ++ tailWord_98423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98423).length < 2 ^ (prefixWord ++ tailWord_98423).sum := by decide
  have hdescent : baseEnd_98423 < baseStart_98423 := by decide
  rcases family_descends (prefixWord ++ tailWord_98423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98436 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_98436 : Nat := 118140960795 + 98436 * 2 ^ 59
def prefixEnd_98436 : Nat := 4983230072969 + 3 ^ 40 * 98436 * 2
def baseEnd_98436 : Nat := 50544981706082102397307

theorem tailTrace_98436 : CollatzResearch.WordTrace tailWord_98436 prefixEnd_98436 50544981706082102397307 := by
  unfold tailWord_98436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1795127935695329187737581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2393503914260438916983441 1795127935695329187737581)
  ·
    refine ⟨673172975885748445401593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1795127935695329187737581 673172975885748445401593)
    ·
      refine ⟨504879731914311334051195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 673172975885748445401593 504879731914311334051195)
      ·
        refine ⟨757319597871467001076793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504879731914311334051195 757319597871467001076793)
        ·
          refine ⟨567989698403600250807595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757319597871467001076793 567989698403600250807595)
          ·
            refine ⟨851984547605400376211393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567989698403600250807595 851984547605400376211393)
            ·
              refine ⟨638988410704050282158545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851984547605400376211393 638988410704050282158545)
              ·
                refine ⟨479241308028037711618909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638988410704050282158545 479241308028037711618909)
                ·
                  refine ⟨179715490510514141857091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479241308028037711618909 179715490510514141857091)
                  ·
                    refine ⟨269573235765771212785637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179715490510514141857091 269573235765771212785637)
                    ·
                      refine ⟨50544981706082102397307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 269573235765771212785637 50544981706082102397307)
                      ·
                        rfl

theorem cell23_98436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_98436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98436 prefixEnd_98436 := by exact prefixLift 98436
  have htrace : WordTrace (prefixWord ++ tailWord_98436) baseStart_98436 baseEnd_98436 := by
    simpa [prefixWord, tailWord_98436, baseEnd_98436] using wordTrace_append hprefix tailTrace_98436
  have hstable : (prefixWord ++ tailWord_98436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98436).length < 2 ^ (prefixWord ++ tailWord_98436).sum := by decide
  have hdescent : baseEnd_98436 < baseStart_98436 := by decide
  rcases family_descends (prefixWord ++ tailWord_98436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98449 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_98449 : Nat := 118140960795 + 98449 * 2 ^ 59
def prefixEnd_98449 : Nat := 4983230072969 + 3 ^ 40 * 98449 * 2
def baseEnd_98449 : Nat := 50551656954590551534747

theorem tailTrace_98449 : CollatzResearch.WordTrace tailWord_98449 prefixEnd_98449 50551656954590551534747 := by
  unfold tailWord_98449
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590730020343561595698401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2393820013562374397132267 3590730020343561595698401)
  ·
    refine ⟨2693047515257671196773801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3590730020343561595698401 2693047515257671196773801)
    ·
      refine ⟨2019785636443253397580351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2693047515257671196773801 2019785636443253397580351)
      ·
        refine ⟨3029678454664880096370527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019785636443253397580351 3029678454664880096370527)
        ·
          refine ⟨4544517681997320144555791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029678454664880096370527 4544517681997320144555791)
          ·
            refine ⟨6816776522995980216833687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544517681997320144555791 6816776522995980216833687)
            ·
              refine ⟨10225164784493970325250531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816776522995980216833687 10225164784493970325250531)
              ·
                refine ⟨15337747176740955487875797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10225164784493970325250531 15337747176740955487875797)
                ·
                  refine ⟨359478449454866144247089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15337747176740955487875797 359478449454866144247089)
                  ·
                    refine ⟨269608837091149608185317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 359478449454866144247089 269608837091149608185317)
                    ·
                      refine ⟨50551656954590551534747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 269608837091149608185317 50551656954590551534747)
                      ·
                        rfl

theorem cell23_98449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_98449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98449 prefixEnd_98449 := by exact prefixLift 98449
  have htrace : WordTrace (prefixWord ++ tailWord_98449) baseStart_98449 baseEnd_98449 := by
    simpa [prefixWord, tailWord_98449, baseEnd_98449] using wordTrace_append hprefix tailTrace_98449
  have hstable : (prefixWord ++ tailWord_98449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98449).length < 2 ^ (prefixWord ++ tailWord_98449).sum := by decide
  have hdescent : baseEnd_98449 < baseStart_98449 := by decide
  rcases family_descends (prefixWord ++ tailWord_98449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98453 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_98453 : Nat := 118140960795 + 98453 * 2 ^ 59
def prefixEnd_98453 : Nat := 4983230072969 + 3 ^ 40 * 98453 * 2
def baseEnd_98453 : Nat := 50553710877208535884729

theorem tailTrace_98453 : CollatzResearch.WordTrace tailWord_98453 prefixEnd_98453 50553710877208535884729 := by
  unfold tailWord_98453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590875912329070278844013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2393917274886046852562675 3590875912329070278844013)
  ·
    refine ⟨1346578467123401354566505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3590875912329070278844013 1346578467123401354566505)
    ·
      refine ⟨1009933850342551015924879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1346578467123401354566505 1009933850342551015924879)
      ·
        refine ⟨1514900775513826523887319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009933850342551015924879 1514900775513826523887319)
        ·
          refine ⟨2272351163270739785830979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514900775513826523887319 2272351163270739785830979)
          ·
            refine ⟨3408526744906109678746469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272351163270739785830979 3408526744906109678746469)
            ·
              refine ⟨639098764669895564764963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3408526744906109678746469 639098764669895564764963)
              ·
                refine ⟨958648147004843347147445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639098764669895564764963 958648147004843347147445)
                ·
                  refine ⟨89873263781704063795073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 958648147004843347147445 89873263781704063795073)
                  ·
                    refine ⟨67404947836278047846305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89873263781704063795073 67404947836278047846305)
                    ·
                      refine ⟨50553710877208535884729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67404947836278047846305 50553710877208535884729)
                      ·
                        rfl

theorem cell23_98453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_98453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98453 prefixEnd_98453 := by exact prefixLift 98453
  have htrace : WordTrace (prefixWord ++ tailWord_98453) baseStart_98453 baseEnd_98453 := by
    simpa [prefixWord, tailWord_98453, baseEnd_98453] using wordTrace_append hprefix tailTrace_98453
  have hstable : (prefixWord ++ tailWord_98453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98453).length < 2 ^ (prefixWord ++ tailWord_98453).sum := by decide
  have hdescent : baseEnd_98453 < baseStart_98453 := by decide
  rcases family_descends (prefixWord ++ tailWord_98453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98481 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 1, 1, 3]
def baseStart_98481 : Nat := 118140960795 + 98481 * 2 ^ 59
def prefixEnd_98481 : Nat := 4983230072969 + 3 ^ 40 * 98481 * 2
def baseEnd_98481 : Nat := 50568088335534426334601

theorem tailTrace_98481 : CollatzResearch.WordTrace tailWord_98481 prefixEnd_98481 50568088335534426334601 := by
  unfold tailWord_98481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591897156227631060863297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2394598104151754040575531 3591897156227631060863297)
  ·
    refine ⟨2693922867170723295647473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3591897156227631060863297 2693922867170723295647473)
    ·
      refine ⟨2020442150378042471735605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2693922867170723295647473 2020442150378042471735605)
      ·
        refine ⟨189416451597941481725213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2020442150378042471735605 189416451597941481725213)
        ·
          refine ⟨71031169349228055646955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189416451597941481725213 71031169349228055646955)
          ·
            refine ⟨106546754023842083470433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71031169349228055646955 106546754023842083470433)
            ·
              refine ⟨79910065517881562602825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106546754023842083470433 79910065517881562602825)
              ·
                refine ⟨59932549138411171952119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79910065517881562602825 59932549138411171952119)
                ·
                  refine ⟨89898823707616757928179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59932549138411171952119 89898823707616757928179)
                  ·
                    refine ⟨134848235561425136892269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89898823707616757928179 134848235561425136892269)
                    ·
                      refine ⟨50568088335534426334601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 134848235561425136892269 50568088335534426334601)
                      ·
                        rfl

theorem cell23_98481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_98481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98481 prefixEnd_98481 := by exact prefixLift 98481
  have htrace : WordTrace (prefixWord ++ tailWord_98481) baseStart_98481 baseEnd_98481 := by
    simpa [prefixWord, tailWord_98481, baseEnd_98481] using wordTrace_append hprefix tailTrace_98481
  have hstable : (prefixWord ++ tailWord_98481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98481).length < 2 ^ (prefixWord ++ tailWord_98481).sum := by decide
  have hdescent : baseEnd_98481 < baseStart_98481 := by decide
  rcases family_descends (prefixWord ++ tailWord_98481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98487 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 1, 2, 2]
def baseStart_98487 : Nat := 118140960795 + 98487 * 2 ^ 59
def prefixEnd_98487 : Nat := 4983230072969 + 3 ^ 40 * 98487 * 2
def baseEnd_98487 : Nat := 50571169219461402859573

theorem tailTrace_98487 : CollatzResearch.WordTrace tailWord_98487 prefixEnd_98487 50571169219461402859573 := by
  unfold tailWord_98487
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592115994205894085581715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2394743996137262723721143 3592115994205894085581715)
  ·
    refine ⟨5388173991308841128372573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3592115994205894085581715 5388173991308841128372573)
    ·
      refine ⟨2020565246740815423139715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5388173991308841128372573 2020565246740815423139715)
      ·
        refine ⟨3030847870111223134709573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020565246740815423139715 3030847870111223134709573)
        ·
          refine ⟨568283975645854337758045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3030847870111223134709573 568283975645854337758045)
          ·
            refine ⟨213106490867195376659267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 568283975645854337758045 213106490867195376659267)
            ·
              refine ⟨319659736300793064988901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213106490867195376659267 319659736300793064988901)
              ·
                refine ⟨59936200556398699685419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319659736300793064988901 59936200556398699685419)
                ·
                  refine ⟨89904300834598049528129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59936200556398699685419 89904300834598049528129)
                  ·
                    refine ⟨67428225625948537146097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89904300834598049528129 67428225625948537146097)
                    ·
                      refine ⟨50571169219461402859573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67428225625948537146097 50571169219461402859573)
                      ·
                        rfl

theorem cell23_98487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_98487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98487 prefixEnd_98487 := by exact prefixLift 98487
  have htrace : WordTrace (prefixWord ++ tailWord_98487) baseStart_98487 baseEnd_98487 := by
    simpa [prefixWord, tailWord_98487, baseEnd_98487] using wordTrace_append hprefix tailTrace_98487
  have hstable : (prefixWord ++ tailWord_98487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98487).length < 2 ^ (prefixWord ++ tailWord_98487).sum := by decide
  have hdescent : baseEnd_98487 < baseStart_98487 := by decide
  rcases family_descends (prefixWord ++ tailWord_98487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98489 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_98489 : Nat := 118140960795 + 98489 * 2 ^ 59
def prefixEnd_98489 : Nat := 4983230072969 + 3 ^ 40 * 98489 * 2
def baseEnd_98489 : Nat := 16857398726923465011521

theorem tailTrace_98489 : CollatzResearch.WordTrace tailWord_98489 prefixEnd_98489 16857398726923465011521 := by
  unfold tailWord_98489
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592188940198648427154521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2394792626799098951436347 3592188940198648427154521)
  ·
    refine ⟨2694141705148986320365891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3592188940198648427154521 2694141705148986320365891)
    ·
      refine ⟨4041212557723479480548837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694141705148986320365891 4041212557723479480548837)
      ·
        refine ⟨757727354573152402602907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4041212557723479480548837 757727354573152402602907)
        ·
          refine ⟨1136591031859728603904361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757727354573152402602907 1136591031859728603904361)
          ·
            refine ⟨852443273894796452928271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136591031859728603904361 852443273894796452928271)
            ·
              refine ⟨1278664910842194679392407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852443273894796452928271 1278664910842194679392407)
              ·
                refine ⟨1917997366263292019088611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278664910842194679392407 1917997366263292019088611)
                ·
                  refine ⟨2876996049394938028632917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917997366263292019088611 2876996049394938028632917)
                  ·
                    refine ⟨16857398726923465011521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2876996049394938028632917 16857398726923465011521)
                    ·
                      rfl

theorem cell23_98489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_98489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98489 prefixEnd_98489 := by exact prefixLift 98489
  have htrace : WordTrace (prefixWord ++ tailWord_98489) baseStart_98489 baseEnd_98489 := by
    simpa [prefixWord, tailWord_98489, baseEnd_98489] using wordTrace_append hprefix tailTrace_98489
  have hstable : (prefixWord ++ tailWord_98489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98489).length < 2 ^ (prefixWord ++ tailWord_98489).sum := by decide
  have hdescent : baseEnd_98489 < baseStart_98489 := by decide
  rcases family_descends (prefixWord ++ tailWord_98489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98513 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 3, 3, 2]
def baseStart_98513 : Nat := 118140960795 + 98513 * 2 ^ 59
def prefixEnd_98513 : Nat := 4983230072969 + 3 ^ 40 * 98513 * 2
def baseEnd_98513 : Nat := 50584519716478301134453

theorem tailTrace_98513 : CollatzResearch.WordTrace tailWord_98513 prefixEnd_98513 50584519716478301134453 := by
  unfold tailWord_98513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593064292111700526028193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2395376194741133684018795 3593064292111700526028193)
  ·
    refine ⟨2694798219083775394521145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3593064292111700526028193 2694798219083775394521145)
    ·
      refine ⟨2021098664312831545890859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2694798219083775394521145 2021098664312831545890859)
      ·
        refine ⟨3031647996469247318836289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021098664312831545890859 3031647996469247318836289)
        ·
          refine ⟨2273735997351935489127217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031647996469247318836289 2273735997351935489127217)
          ·
            refine ⟨1705301998013951616845413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273735997351935489127217 1705301998013951616845413)
            ·
              refine ⟨319744124627615928158515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1705301998013951616845413 319744124627615928158515)
              ·
                refine ⟨479616186941423892237773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319744124627615928158515 479616186941423892237773)
                ·
                  refine ⟨179856070103033959589165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479616186941423892237773 179856070103033959589165)
                  ·
                    refine ⟨67446026288637734845937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179856070103033959589165 67446026288637734845937)
                    ·
                      refine ⟨50584519716478301134453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67446026288637734845937 50584519716478301134453)
                      ·
                        rfl

theorem cell23_98513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_98513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98513 prefixEnd_98513 := by exact prefixLift 98513
  have htrace : WordTrace (prefixWord ++ tailWord_98513) baseStart_98513 baseEnd_98513 := by
    simpa [prefixWord, tailWord_98513, baseEnd_98513] using wordTrace_append hprefix tailTrace_98513
  have hstable : (prefixWord ++ tailWord_98513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98513).length < 2 ^ (prefixWord ++ tailWord_98513).sum := by decide
  have hdescent : baseEnd_98513 < baseStart_98513 := by decide
  rcases family_descends (prefixWord ++ tailWord_98513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98519 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 8]
def baseStart_98519 : Nat := 118140960795 + 98519 * 2 ^ 59
def prefixEnd_98519 : Nat := 4983230072969 + 3 ^ 40 * 98519 * 2
def baseEnd_98519 : Nat := 16862533533468425886475

theorem tailTrace_98519 : CollatzResearch.WordTrace tailWord_98519 prefixEnd_98519 16862533533468425886475 := by
  unfold tailWord_98519
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593283130089963550746611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2395522086726642367164407 3593283130089963550746611)
  ·
    refine ⟨5389924695134945326119917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593283130089963550746611 5389924695134945326119917)
    ·
      refine ⟨2021221760675604497294969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5389924695134945326119917 2021221760675604497294969)
      ·
        refine ⟨1515916320506703372971227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021221760675604497294969 1515916320506703372971227)
        ·
          refine ⟨2273874480760055059456841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515916320506703372971227 2273874480760055059456841)
          ·
            refine ⟨1705405860570041294592631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273874480760055059456841 1705405860570041294592631)
            ·
              refine ⟨2558108790855061941888947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705405860570041294592631 2558108790855061941888947)
              ·
                refine ⟨3837163186282592912833421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558108790855061941888947 3837163186282592912833421)
                ·
                  refine ⟨1438936194855972342312533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3837163186282592912833421 1438936194855972342312533)
                  ·
                    refine ⟨16862533533468425886475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1438936194855972342312533 16862533533468425886475)
                    ·
                      rfl

theorem cell23_98519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_98519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98519 prefixEnd_98519 := by exact prefixLift 98519
  have htrace : WordTrace (prefixWord ++ tailWord_98519) baseStart_98519 baseEnd_98519 := by
    simpa [prefixWord, tailWord_98519, baseEnd_98519] using wordTrace_append hprefix tailTrace_98519
  have hstable : (prefixWord ++ tailWord_98519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98519).length < 2 ^ (prefixWord ++ tailWord_98519).sum := by decide
  have hdescent : baseEnd_98519 < baseStart_98519 := by decide
  rcases family_descends (prefixWord ++ tailWord_98519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98536 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_98536 : Nat := 118140960795 + 98536 * 2 ^ 59
def prefixEnd_98536 : Nat := 4983230072969 + 3 ^ 40 * 98536 * 2
def baseEnd_98536 : Nat := 16865443257177237048949

theorem tailTrace_98536 : CollatzResearch.WordTrace tailWord_98536 prefixEnd_98536 16865443257177237048949 := by
  unfold tailWord_98536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796951585514187727057731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2395935447352250302743641 1796951585514187727057731)
  ·
    refine ⟨2695427378271281590586597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796951585514187727057731 2695427378271281590586597)
    ·
      refine ⟨505392633425865298234987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2695427378271281590586597 505392633425865298234987)
      ·
        refine ⟨758088950138797947352481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505392633425865298234987 758088950138797947352481)
        ·
          refine ⟨568566712604098460514361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758088950138797947352481 568566712604098460514361)
          ·
            refine ⟨426425034453073845385771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568566712604098460514361 426425034453073845385771)
            ·
              refine ⟨639637551679610768078657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426425034453073845385771 639637551679610768078657)
              ·
                refine ⟨479728163759708076058993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639637551679610768078657 479728163759708076058993)
                ·
                  refine ⟨359796122819781057044245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479728163759708076058993 359796122819781057044245)
                  ·
                    refine ⟨16865443257177237048949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 359796122819781057044245 16865443257177237048949)
                    ·
                      rfl

theorem cell23_98536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_98536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98536 prefixEnd_98536 := by exact prefixLift 98536
  have htrace : WordTrace (prefixWord ++ tailWord_98536) baseStart_98536 baseEnd_98536 := by
    simpa [prefixWord, tailWord_98536, baseEnd_98536] using wordTrace_append hprefix tailTrace_98536
  have hstable : (prefixWord ++ tailWord_98536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98536).length < 2 ^ (prefixWord ++ tailWord_98536).sum := by decide
  have hdescent : baseEnd_98536 < baseStart_98536 := by decide
  rcases family_descends (prefixWord ++ tailWord_98536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98560 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 2, 2, 2]
def baseStart_98560 : Nat := 118140960795 + 98560 * 2 ^ 59
def prefixEnd_98560 : Nat := 4983230072969 + 3 ^ 40 * 98560 * 2
def baseEnd_98560 : Nat := 50608653307239617246737

theorem tailTrace_98560 : CollatzResearch.WordTrace tailWord_98560 prefixEnd_98560 50608653307239617246737 := by
  unfold tailWord_98560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797389261470713776494567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2396519015294285035326089 1797389261470713776494567)
  ·
    refine ⟨2696083892206070664741851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797389261470713776494567 2696083892206070664741851)
    ·
      refine ⟨4044125838309105997112777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2696083892206070664741851 4044125838309105997112777)
      ·
        refine ⟨3033094378731829497834583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4044125838309105997112777 3033094378731829497834583)
        ·
          refine ⟨4549641568097744246751875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033094378731829497834583 4549641568097744246751875)
          ·
            refine ⟨6824462352146616370127813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549641568097744246751875 6824462352146616370127813)
            ·
              refine ⟨1279586691027490569398965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6824462352146616370127813 1279586691027490569398965)
              ·
                refine ⟨119961252283827240881153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1279586691027490569398965 119961252283827240881153)
                ·
                  refine ⟨89970939212870430660865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119961252283827240881153 89970939212870430660865)
                  ·
                    refine ⟨67478204409652822995649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89970939212870430660865 67478204409652822995649)
                    ·
                      refine ⟨50608653307239617246737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67478204409652822995649 50608653307239617246737)
                      ·
                        rfl

theorem cell23_98560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_98560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98560 prefixEnd_98560 := by exact prefixLift 98560
  have htrace : WordTrace (prefixWord ++ tailWord_98560) baseStart_98560 baseEnd_98560 := by
    simpa [prefixWord, tailWord_98560, baseEnd_98560] using wordTrace_append hprefix tailTrace_98560
  have hstable : (prefixWord ++ tailWord_98560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98560).length < 2 ^ (prefixWord ++ tailWord_98560).sum := by decide
  have hdescent : baseEnd_98560 < baseStart_98560 := by decide
  rcases family_descends (prefixWord ++ tailWord_98560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98600 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 7]
def baseStart_98600 : Nat := 118140960795 + 98600 * 2 ^ 59
def prefixEnd_98600 : Nat := 4983230072969 + 3 ^ 40 * 98600 * 2
def baseEnd_98600 : Nat := 5625465837046606749617

theorem tailTrace_98600 : CollatzResearch.WordTrace tailWord_98600 prefixEnd_98600 5625465837046606749617 := by
  unfold tailWord_98600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798118721398257192222627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2397491628531009589630169 1798118721398257192222627)
  ·
    refine ⟨2697178082097385788333941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798118721398257192222627 2697178082097385788333941)
    ·
      refine ⟨252860445196629917656307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2697178082097385788333941 252860445196629917656307)
      ·
        refine ⟨379290667794944876484461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252860445196629917656307 379290667794944876484461)
        ·
          refine ⟨142234000423104328681673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379290667794944876484461 142234000423104328681673)
          ·
            refine ⟨106675500317328246511255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142234000423104328681673 106675500317328246511255)
            ·
              refine ⟨160013250475992369766883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106675500317328246511255 160013250475992369766883)
              ·
                refine ⟨240019875713988554650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160013250475992369766883 240019875713988554650325)
                ·
                  refine ⟨5625465837046606749617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 240019875713988554650325 5625465837046606749617)
                  ·
                    rfl

theorem cell23_98600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 7].length) (baseStart_98600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98600 prefixEnd_98600 := by exact prefixLift 98600
  have htrace : WordTrace (prefixWord ++ tailWord_98600) baseStart_98600 baseEnd_98600 := by
    simpa [prefixWord, tailWord_98600, baseEnd_98600] using wordTrace_append hprefix tailTrace_98600
  have hstable : (prefixWord ++ tailWord_98600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98600).length < 2 ^ (prefixWord ++ tailWord_98600).sum := by decide
  have hdescent : baseEnd_98600 < baseStart_98600 := by decide
  rcases family_descends (prefixWord ++ tailWord_98600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98616 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_98616 : Nat := 118140960795 + 98616 * 2 ^ 59
def prefixEnd_98616 : Nat := 4983230072969 + 3 ^ 40 * 98616 * 2
def baseEnd_98616 : Nat := 50637408223891398146479

theorem tailTrace_98616 : CollatzResearch.WordTrace tailWord_98616 prefixEnd_98616 50637408223891398146479 := by
  unfold tailWord_98616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798410505369274558513851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2397880673825699411351801 1798410505369274558513851)
  ·
    refine ⟨2697615758053911837770777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798410505369274558513851 2697615758053911837770777)
    ·
      refine ⟨2023211818540433878328083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2697615758053911837770777 2023211818540433878328083)
      ·
        refine ⟨3034817727810650817492125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023211818540433878328083 3034817727810650817492125)
        ·
          refine ⟨1138056647928994056559547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3034817727810650817492125 1138056647928994056559547)
          ·
            refine ⟨1707084971893491084839321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138056647928994056559547 1707084971893491084839321)
            ·
              refine ⟨1280313728920118313629491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707084971893491084839321 1280313728920118313629491)
              ·
                refine ⟨1920470593380177470444237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280313728920118313629491 1920470593380177470444237)
                ·
                  refine ⟨720176472517566551416589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1920470593380177470444237 720176472517566551416589)
                  ·
                    refine ⟨270066177194087456781221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720176472517566551416589 270066177194087456781221)
                    ·
                      refine ⟨50637408223891398146479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 270066177194087456781221 50637408223891398146479)
                      ·
                        rfl

theorem cell23_98616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_98616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98616 prefixEnd_98616 := by exact prefixLift 98616
  have htrace : WordTrace (prefixWord ++ tailWord_98616) baseStart_98616 baseEnd_98616 := by
    simpa [prefixWord, tailWord_98616, baseEnd_98616] using wordTrace_append hprefix tailTrace_98616
  have hstable : (prefixWord ++ tailWord_98616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98616).length < 2 ^ (prefixWord ++ tailWord_98616).sum := by decide
  have hdescent : baseEnd_98616 < baseStart_98616 := by decide
  rcases family_descends (prefixWord ++ tailWord_98616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98633 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 4, 4, 2]
def baseStart_98633 : Nat := 118140960795 + 98633 * 2 ^ 59
def prefixEnd_98633 : Nat := 4983230072969 + 3 ^ 40 * 98633 * 2
def baseEnd_98633 : Nat := 50646137395017831633901

theorem tailTrace_98633 : CollatzResearch.WordTrace tailWord_98633 prefixEnd_98633 50646137395017831633901 := by
  unfold tailWord_98633
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597441051676961020396553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2398294034451307346931035 3597441051676961020396553)
  ·
    refine ⟨2698080788757720765297415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3597441051676961020396553 2698080788757720765297415)
    ·
      refine ⟨4047121183136581147946123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698080788757720765297415 4047121183136581147946123)
      ·
        refine ⟨6070681774704871721919185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047121183136581147946123 6070681774704871721919185)
        ·
          refine ⟨4553011331028653791439389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6070681774704871721919185 4553011331028653791439389)
          ·
            refine ⟨1707379249135745171789771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4553011331028653791439389 1707379249135745171789771)
            ·
              refine ⟨2561068873703617757684657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707379249135745171789771 2561068873703617757684657)
              ·
                refine ⟨1920801655277713318263493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561068873703617757684657 1920801655277713318263493)
                ·
                  refine ⟨360150310364571247174405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920801655277713318263493 360150310364571247174405)
                  ·
                    refine ⟨67528183193357108845201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360150310364571247174405 67528183193357108845201)
                    ·
                      refine ⟨50646137395017831633901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67528183193357108845201 50646137395017831633901)
                      ·
                        rfl

theorem cell23_98633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 4, 2].length) (baseStart_98633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98633 prefixEnd_98633 := by exact prefixLift 98633
  have htrace : WordTrace (prefixWord ++ tailWord_98633) baseStart_98633 baseEnd_98633 := by
    simpa [prefixWord, tailWord_98633, baseEnd_98633] using wordTrace_append hprefix tailTrace_98633
  have hstable : (prefixWord ++ tailWord_98633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98633).length < 2 ^ (prefixWord ++ tailWord_98633).sum := by decide
  have hdescent : baseEnd_98633 < baseStart_98633 := by decide
  rcases family_descends (prefixWord ++ tailWord_98633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98750 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_98750 : Nat := 118140960795 + 98750 * 2 ^ 59
def prefixEnd_98750 : Nat := 4983230072969 + 3 ^ 40 * 98750 * 2
def baseEnd_98750 : Nat := 16902071543864624623621

theorem tailTrace_98750 : CollatzResearch.WordTrace tailWord_98750 prefixEnd_98750 16902071543864624623621 := by
  unfold tailWord_98750
  simp only [CollatzResearch.WordTrace]
  refine ⟨450213549031636250300713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2401138928168726668270469 450213549031636250300713)
  ·
    refine ⟨337660161773727187725535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 450213549031636250300713 337660161773727187725535)
    ·
      refine ⟨506490242660590781588303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337660161773727187725535 506490242660590781588303)
      ·
        refine ⟨759735363990886172382455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506490242660590781588303 759735363990886172382455)
        ·
          refine ⟨1139603045986329258573683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759735363990886172382455 1139603045986329258573683)
          ·
            refine ⟨1709404568979493887860525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139603045986329258573683 1709404568979493887860525)
            ·
              refine ⟨641026713367310207947697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1709404568979493887860525 641026713367310207947697)
              ·
                refine ⟨480770035025482655960773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641026713367310207947697 480770035025482655960773)
                ·
                  refine ⟨90144381567277997992645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480770035025482655960773 90144381567277997992645)
                  ·
                    refine ⟨16902071543864624623621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90144381567277997992645 16902071543864624623621)
                    ·
                      rfl

theorem cell23_98750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_98750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98750 prefixEnd_98750 := by exact prefixLift 98750
  have htrace : WordTrace (prefixWord ++ tailWord_98750) baseStart_98750 baseEnd_98750 := by
    simpa [prefixWord, tailWord_98750, baseEnd_98750] using wordTrace_append hprefix tailTrace_98750
  have hstable : (prefixWord ++ tailWord_98750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98750).length < 2 ^ (prefixWord ++ tailWord_98750).sum := by decide
  have hdescent : baseEnd_98750 < baseStart_98750 := by decide
  rcases family_descends (prefixWord ++ tailWord_98750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98760 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_98760 : Nat := 118140960795 + 98760 * 2 ^ 59
def prefixEnd_98760 : Nat := 4983230072969 + 3 ^ 40 * 98760 * 2
def baseEnd_98760 : Nat := 50711349438138834745817

theorem tailTrace_98760 : CollatzResearch.WordTrace tailWord_98760 prefixEnd_98760 50711349438138834745817 := by
  unfold tailWord_98760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801036561108430855134867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2401382081477907806846489 1801036561108430855134867)
  ·
    refine ⟨2701554841662646282702301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801036561108430855134867 2701554841662646282702301)
    ·
      refine ⟨1013083065623492356013363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2701554841662646282702301 1013083065623492356013363)
      ·
        refine ⟨1519624598435238534020045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013083065623492356013363 1519624598435238534020045)
        ·
          refine ⟨569859224413214450257517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1519624598435238534020045 569859224413214450257517)
          ·
            refine ⟨213697209154955418846569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 569859224413214450257517 213697209154955418846569)
            ·
              refine ⟨160272906866216564134927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213697209154955418846569 160272906866216564134927)
              ·
                refine ⟨240409360299324846202391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160272906866216564134927 240409360299324846202391)
                ·
                  refine ⟨360614040448987269303587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240409360299324846202391 360614040448987269303587)
                  ·
                    refine ⟨540921060673480903955381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360614040448987269303587 540921060673480903955381)
                    ·
                      refine ⟨50711349438138834745817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 540921060673480903955381 50711349438138834745817)
                      ·
                        rfl

theorem cell23_98760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_98760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98760 prefixEnd_98760 := by exact prefixLift 98760
  have htrace : WordTrace (prefixWord ++ tailWord_98760) baseStart_98760 baseEnd_98760 := by
    simpa [prefixWord, tailWord_98760, baseEnd_98760] using wordTrace_append hprefix tailTrace_98760
  have hstable : (prefixWord ++ tailWord_98760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98760).length < 2 ^ (prefixWord ++ tailWord_98760).sum := by decide
  have hdescent : baseEnd_98760 < baseStart_98760 := by decide
  rcases family_descends (prefixWord ++ tailWord_98760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98794 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_98794 : Nat := 118140960795 + 98794 * 2 ^ 59
def prefixEnd_98794 : Nat := 4983230072969 + 3 ^ 40 * 98794 * 2
def baseEnd_98794 : Nat := 50728807780391701720661

theorem tailTrace_98794 : CollatzResearch.WordTrace tailWord_98794 prefixEnd_98794 50728807780391701720661 := by
  unfold tailWord_98794
  simp only [CollatzResearch.WordTrace]
  refine ⟨900828301023421379251859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2402208802729123678004957 900828301023421379251859)
  ·
    refine ⟨1351242451535132068877789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 900828301023421379251859 1351242451535132068877789)
    ·
      refine ⟨506715919325674525829171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1351242451535132068877789 506715919325674525829171)
      ·
        refine ⟨760073878988511788743757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506715919325674525829171 760073878988511788743757)
        ·
          refine ⟨285027704620691920778909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 760073878988511788743757 285027704620691920778909)
          ·
            refine ⟨106885389232759470292091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285027704620691920778909 106885389232759470292091)
            ·
              refine ⟨160328083849139205438137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106885389232759470292091 160328083849139205438137)
              ·
                refine ⟨120246062886854404078603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160328083849139205438137 120246062886854404078603)
                ·
                  refine ⟨180369094330281606117905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120246062886854404078603 180369094330281606117905)
                  ·
                    refine ⟨135276820747711204588429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 180369094330281606117905 135276820747711204588429)
                    ·
                      refine ⟨50728807780391701720661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 135276820747711204588429 50728807780391701720661)
                      ·
                        rfl

theorem cell23_98794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_98794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98794 prefixEnd_98794 := by exact prefixLift 98794
  have htrace : WordTrace (prefixWord ++ tailWord_98794) baseStart_98794 baseEnd_98794 := by
    simpa [prefixWord, tailWord_98794, baseEnd_98794] using wordTrace_append hprefix tailTrace_98794
  have hstable : (prefixWord ++ tailWord_98794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98794).length < 2 ^ (prefixWord ++ tailWord_98794).sum := by decide
  have hdescent : baseEnd_98794 < baseStart_98794 := by decide
  rcases family_descends (prefixWord ++ tailWord_98794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98830 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_98830 : Nat := 118140960795 + 98830 * 2 ^ 59
def prefixEnd_98830 : Nat := 4983230072969 + 3 ^ 40 * 98830 * 2
def baseEnd_98830 : Nat := 50747293083953560870495

theorem tailTrace_98830 : CollatzResearch.WordTrace tailWord_98830 prefixEnd_98830 50747293083953560870495 := by
  unfold tailWord_98830
  simp only [CollatzResearch.WordTrace]
  refine ⟨450578278995407958164743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2403084154642175776878629 450578278995407958164743)
  ·
    refine ⟨675867418493111937247115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450578278995407958164743 675867418493111937247115)
    ·
      refine ⟨1013801127739667905870673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675867418493111937247115 1013801127739667905870673)
      ·
        refine ⟨760350845804750929403005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1013801127739667905870673 760350845804750929403005)
        ·
          refine ⟨285131567176781598526127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 760350845804750929403005 285131567176781598526127)
          ·
            refine ⟨427697350765172397789191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285131567176781598526127 427697350765172397789191)
            ·
              refine ⟨641546026147758596683787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427697350765172397789191 641546026147758596683787)
              ·
                refine ⟨962319039221637895025681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641546026147758596683787 962319039221637895025681)
                ·
                  refine ⟨721739279416228421269261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962319039221637895025681 721739279416228421269261)
                  ·
                    refine ⟨270652229781085657975973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721739279416228421269261 270652229781085657975973)
                    ·
                      refine ⟨50747293083953560870495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 270652229781085657975973 50747293083953560870495)
                      ·
                        rfl

theorem cell23_98830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_98830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98830 prefixEnd_98830 := by exact prefixLift 98830
  have htrace : WordTrace (prefixWord ++ tailWord_98830) baseStart_98830 baseEnd_98830 := by
    simpa [prefixWord, tailWord_98830, baseEnd_98830] using wordTrace_append hprefix tailTrace_98830
  have hstable : (prefixWord ++ tailWord_98830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98830).length < 2 ^ (prefixWord ++ tailWord_98830).sum := by decide
  have hdescent : baseEnd_98830 < baseStart_98830 := by decide
  rcases family_descends (prefixWord ++ tailWord_98830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98833 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_98833 : Nat := 118140960795 + 98833 * 2 ^ 59
def prefixEnd_98833 : Nat := 4983230072969 + 3 ^ 40 * 98833 * 2
def baseEnd_98833 : Nat := 50748833525917049132981

theorem tailTrace_98833 : CollatzResearch.WordTrace tailWord_98833 prefixEnd_98833 50748833525917049132981 := by
  unfold tailWord_98833
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604735650952395177677153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2403157100634930118451435 3604735650952395177677153)
  ·
    refine ⟨2703551738214296383257865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3604735650952395177677153 2703551738214296383257865)
    ·
      refine ⟨2027663803660722287443399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703551738214296383257865 2027663803660722287443399)
      ·
        refine ⟨3041495705491083431165099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027663803660722287443399 3041495705491083431165099)
        ·
          refine ⟨4562243558236625146747649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041495705491083431165099 4562243558236625146747649)
          ·
            refine ⟨3421682668677468860060737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4562243558236625146747649 3421682668677468860060737)
            ·
              refine ⟨2566262001508101645045553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421682668677468860060737 2566262001508101645045553)
              ·
                refine ⟨1924696501131076233784165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566262001508101645045553 1924696501131076233784165)
                ·
                  refine ⟨360880593962076793834531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924696501131076233784165 360880593962076793834531)
                  ·
                    refine ⟨541320890943115190751797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360880593962076793834531 541320890943115190751797)
                    ·
                      refine ⟨50748833525917049132981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 541320890943115190751797 50748833525917049132981)
                      ·
                        rfl

theorem cell23_98833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_98833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98833 prefixEnd_98833 := by exact prefixLift 98833
  have htrace : WordTrace (prefixWord ++ tailWord_98833) baseStart_98833 baseEnd_98833 := by
    simpa [prefixWord, tailWord_98833, baseEnd_98833] using wordTrace_append hprefix tailTrace_98833
  have hstable : (prefixWord ++ tailWord_98833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98833).length < 2 ^ (prefixWord ++ tailWord_98833).sum := by decide
  have hdescent : baseEnd_98833 < baseStart_98833 := by decide
  rcases family_descends (prefixWord ++ tailWord_98833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98840 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_98840 : Nat := 118140960795 + 98840 * 2 ^ 59
def prefixEnd_98840 : Nat := 4983230072969 + 3 ^ 40 * 98840 * 2
def baseEnd_98840 : Nat := 16917475963499507248483

theorem tailTrace_98840 : CollatzResearch.WordTrace tailWord_98840 prefixEnd_98840 16917475963499507248483 := by
  unfold tailWord_98840
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802495480963517686590987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2403327307951356915454649 1802495480963517686590987)
  ·
    refine ⟨2703743221445276529886481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802495480963517686590987 2703743221445276529886481)
    ·
      refine ⟨2027807416083957397414861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703743221445276529886481 2027807416083957397414861)
      ·
        refine ⟨760427781031484024030573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2027807416083957397414861 760427781031484024030573)
        ·
          refine ⟨285160417886806509011465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 760427781031484024030573 285160417886806509011465)
          ·
            refine ⟨213870313415104881758599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285160417886806509011465 213870313415104881758599)
            ·
              refine ⟨320805470122657322637899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213870313415104881758599 320805470122657322637899)
              ·
                refine ⟨481208205183985983956849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320805470122657322637899 481208205183985983956849)
                ·
                  refine ⟨360906153887989487967637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481208205183985983956849 360906153887989487967637)
                  ·
                    refine ⟨16917475963499507248483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 360906153887989487967637 16917475963499507248483)
                    ·
                      rfl

theorem cell23_98840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_98840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98840 prefixEnd_98840 := by exact prefixLift 98840
  have htrace : WordTrace (prefixWord ++ tailWord_98840) baseStart_98840 baseEnd_98840 := by
    simpa [prefixWord, tailWord_98840, baseEnd_98840] using wordTrace_append hprefix tailTrace_98840
  have hstable : (prefixWord ++ tailWord_98840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98840).length < 2 ^ (prefixWord ++ tailWord_98840).sum := by decide
  have hdescent : baseEnd_98840 < baseStart_98840 := by decide
  rcases family_descends (prefixWord ++ tailWord_98840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98847 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 6, 2, 2]
def baseStart_98847 : Nat := 118140960795 + 98847 * 2 ^ 59
def prefixEnd_98847 : Nat := 4983230072969 + 3 ^ 40 * 98847 * 2
def baseEnd_98847 : Nat := 50756022255079994357917

theorem tailTrace_98847 : CollatzResearch.WordTrace tailWord_98847 prefixEnd_98847 50756022255079994357917 := by
  unfold tailWord_98847
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605246272901675568686795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2403497515267783712457863 3605246272901675568686795)
  ·
    refine ⟨5407869409352513353030193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605246272901675568686795 5407869409352513353030193)
    ·
      refine ⟨4055902057014385014772645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5407869409352513353030193 4055902057014385014772645)
      ·
        refine ⟨760481635690197190269871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4055902057014385014772645 760481635690197190269871)
        ·
          refine ⟨1140722453535295785404807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760481635690197190269871 1140722453535295785404807)
          ·
            refine ⟨1711083680302943678107211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140722453535295785404807 1711083680302943678107211)
            ·
              refine ⟨2566625520454415517160817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711083680302943678107211 2566625520454415517160817)
              ·
                refine ⟨1924969140340811637870613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566625520454415517160817 1924969140340811637870613)
                ·
                  refine ⟨90232928453475545525185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1924969140340811637870613 90232928453475545525185)
                  ·
                    refine ⟨67674696340106659143889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90232928453475545525185 67674696340106659143889)
                    ·
                      refine ⟨50756022255079994357917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67674696340106659143889 50756022255079994357917)
                      ·
                        rfl

theorem cell23_98847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_98847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98847 prefixEnd_98847 := by exact prefixLift 98847
  have htrace : WordTrace (prefixWord ++ tailWord_98847) baseStart_98847 baseEnd_98847 := by
    simpa [prefixWord, tailWord_98847, baseEnd_98847] using wordTrace_append hprefix tailTrace_98847
  have hstable : (prefixWord ++ tailWord_98847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98847).length < 2 ^ (prefixWord ++ tailWord_98847).sum := by decide
  have hdescent : baseEnd_98847 < baseStart_98847 := by decide
  rcases family_descends (prefixWord ++ tailWord_98847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98850 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_98850 : Nat := 118140960795 + 98850 * 2 ^ 59
def prefixEnd_98850 : Nat := 4983230072969 + 3 ^ 40 * 98850 * 2
def baseEnd_98850 : Nat := 50757562697043482620403

theorem tailTrace_98850 : CollatzResearch.WordTrace tailWord_98850 prefixEnd_98850 50757562697043482620403 := by
  unfold tailWord_98850
  simp only [CollatzResearch.WordTrace]
  refine ⟨901338922972701770261501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2403570461260538054030669 901338922972701770261501)
  ·
    refine ⟨338002096114763163848063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 901338922972701770261501 338002096114763163848063)
    ·
      refine ⟨507003144172144745772095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338002096114763163848063 507003144172144745772095)
      ·
        refine ⟨760504716258217118658143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507003144172144745772095 760504716258217118658143)
        ·
          refine ⟨1140757074387325677987215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760504716258217118658143 1140757074387325677987215)
          ·
            refine ⟨1711135611580988516980823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140757074387325677987215 1711135611580988516980823)
            ·
              refine ⟨2566703417371482775471235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711135611580988516980823 2566703417371482775471235)
              ·
                refine ⟨3850055126057224163206853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566703417371482775471235 3850055126057224163206853)
                ·
                  refine ⟨721885336135729530601285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3850055126057224163206853 721885336135729530601285)
                  ·
                    refine ⟨135353500525449286987741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721885336135729530601285 135353500525449286987741)
                    ·
                      refine ⟨50757562697043482620403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 135353500525449286987741 50757562697043482620403)
                      ·
                        rfl

theorem cell23_98850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_98850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98850 prefixEnd_98850 := by exact prefixLift 98850
  have htrace : WordTrace (prefixWord ++ tailWord_98850) baseStart_98850 baseEnd_98850 := by
    simpa [prefixWord, tailWord_98850, baseEnd_98850] using wordTrace_append hprefix tailTrace_98850
  have hstable : (prefixWord ++ tailWord_98850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98850).length < 2 ^ (prefixWord ++ tailWord_98850).sum := by decide
  have hdescent : baseEnd_98850 < baseStart_98850 := by decide
  rcases family_descends (prefixWord ++ tailWord_98850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98853 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 9]
def baseStart_98853 : Nat := 118140960795 + 98853 * 2 ^ 59
def prefixEnd_98853 : Nat := 4983230072969 + 3 ^ 40 * 98853 * 2
def baseEnd_98853 : Nat := 5639900348778552320321

theorem tailTrace_98853 : CollatzResearch.WordTrace tailWord_98853 prefixEnd_98853 5639900348778552320321 := by
  unfold tailWord_98853
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605465110879938593405213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2403643407253292395603475 3605465110879938593405213)
  ·
    refine ⟨1352049416579976972526955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3605465110879938593405213 1352049416579976972526955)
    ·
      refine ⟨2028074124869965458790433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1352049416579976972526955 2028074124869965458790433)
      ·
        refine ⟨1521055593652474094092825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2028074124869965458790433 1521055593652474094092825)
        ·
          refine ⟨1140791695239355570569619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521055593652474094092825 1140791695239355570569619)
          ·
            refine ⟨1711187542859033355854429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140791695239355570569619 1711187542859033355854429)
            ·
              refine ⟨641695328572137508445411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1711187542859033355854429 641695328572137508445411)
              ·
                refine ⟨962542992858206262668117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641695328572137508445411 962542992858206262668117)
                ·
                  refine ⟨5639900348778552320321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 962542992858206262668117 5639900348778552320321)
                  ·
                    rfl

theorem cell23_98853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_98853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98853 prefixEnd_98853 := by exact prefixLift 98853
  have htrace : WordTrace (prefixWord ++ tailWord_98853) baseStart_98853 baseEnd_98853 := by
    simpa [prefixWord, tailWord_98853, baseEnd_98853] using wordTrace_append hprefix tailTrace_98853
  have hstable : (prefixWord ++ tailWord_98853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98853).length < 2 ^ (prefixWord ++ tailWord_98853).sum := by decide
  have hdescent : baseEnd_98853 < baseStart_98853 := by decide
  rcases family_descends (prefixWord ++ tailWord_98853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98868 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_98868 : Nat := 118140960795 + 98868 * 2 ^ 59
def prefixEnd_98868 : Nat := 4983230072969 + 3 ^ 40 * 98868 * 2
def baseEnd_98868 : Nat := 50766805348824412195321

theorem tailTrace_98868 : CollatzResearch.WordTrace tailWord_98868 prefixEnd_98868 50766805348824412195321 := by
  unfold tailWord_98868
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803006102912798077600629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2404008137217064103467505 1803006102912798077600629)
  ·
    refine ⟨169031822148074819775059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1803006102912798077600629 169031822148074819775059)
    ·
      refine ⟨253547733222112229662589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169031822148074819775059 253547733222112229662589)
      ·
        refine ⟨95080399958292086123471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253547733222112229662589 95080399958292086123471)
        ·
          refine ⟨142620599937438129185207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95080399958292086123471 142620599937438129185207)
          ·
            refine ⟨213930899906157193777811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142620599937438129185207 213930899906157193777811)
            ·
              refine ⟨320896349859235790666717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213930899906157193777811 320896349859235790666717)
              ·
                refine ⟨120336131197213421500019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320896349859235790666717 120336131197213421500019)
                ·
                  refine ⟨180504196795820132250029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120336131197213421500019 180504196795820132250029)
                  ·
                    refine ⟨67689073798432549593761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180504196795820132250029 67689073798432549593761)
                    ·
                      refine ⟨50766805348824412195321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67689073798432549593761 50766805348824412195321)
                      ·
                        rfl

theorem cell23_98868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_98868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98868 prefixEnd_98868 := by exact prefixLift 98868
  have htrace : WordTrace (prefixWord ++ tailWord_98868) baseStart_98868 baseEnd_98868 := by
    simpa [prefixWord, tailWord_98868, baseEnd_98868] using wordTrace_append hprefix tailTrace_98868
  have hstable : (prefixWord ++ tailWord_98868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98868).length < 2 ^ (prefixWord ++ tailWord_98868).sum := by decide
  have hdescent : baseEnd_98868 < baseStart_98868 := by decide
  rcases family_descends (prefixWord ++ tailWord_98868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98880 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_98880 : Nat := 118140960795 + 98880 * 2 ^ 59
def prefixEnd_98880 : Nat := 4983230072969 + 3 ^ 40 * 98880 * 2
def baseEnd_98880 : Nat := 50772967116678365245265

theorem tailTrace_98880 : CollatzResearch.WordTrace tailWord_98880 prefixEnd_98880 50772967116678365245265 := by
  unfold tailWord_98880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803224940891061102319047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2404299921188081469758729 1803224940891061102319047)
  ·
    refine ⟨2704837411336591653478571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1803224940891061102319047 2704837411336591653478571)
    ·
      refine ⟨4057256117004887480217857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704837411336591653478571 4057256117004887480217857)
      ·
        refine ⟨3042942087753665610163393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4057256117004887480217857 3042942087753665610163393)
        ·
          refine ⟨2282206565815249207622545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3042942087753665610163393 2282206565815249207622545)
          ·
            refine ⟨1711654924361436905716909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282206565815249207622545 1711654924361436905716909)
            ·
              refine ⟨641870596635538839643841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1711654924361436905716909 641870596635538839643841)
              ·
                refine ⟨481402947476654129732881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641870596635538839643841 481402947476654129732881)
                ·
                  refine ⟨361052210607490597299661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481402947476654129732881 361052210607490597299661)
                  ·
                    refine ⟨135394578977808973987373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 361052210607490597299661 135394578977808973987373)
                    ·
                      refine ⟨50772967116678365245265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 135394578977808973987373 50772967116678365245265)
                      ·
                        rfl

theorem cell23_98880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_98880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98880 prefixEnd_98880 := by exact prefixLift 98880
  have htrace : WordTrace (prefixWord ++ tailWord_98880) baseStart_98880 baseEnd_98880 := by
    simpa [prefixWord, tailWord_98880, baseEnd_98880] using wordTrace_append hprefix tailTrace_98880
  have hstable : (prefixWord ++ tailWord_98880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98880).length < 2 ^ (prefixWord ++ tailWord_98880).sum := by decide
  have hdescent : baseEnd_98880 < baseStart_98880 := by decide
  rcases family_descends (prefixWord ++ tailWord_98880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98881 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_98881 : Nat := 118140960795 + 98881 * 2 ^ 59
def prefixEnd_98881 : Nat := 4983230072969 + 3 ^ 40 * 98881 * 2
def baseEnd_98881 : Nat := 50773480597332861332761

theorem tailTrace_98881 : CollatzResearch.WordTrace tailWord_98881 prefixEnd_98881 50773480597332861332761 := by
  unfold tailWord_98881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606486354778499375424497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2404324236518999583616331 3606486354778499375424497)
  ·
    refine ⟨2704864766083874531568373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3606486354778499375424497 2704864766083874531568373)
    ·
      refine ⟨253581071820363237334535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2704864766083874531568373 253581071820363237334535)
      ·
        refine ⟨380371607730544856001803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253581071820363237334535 380371607730544856001803)
        ·
          refine ⟨570557411595817284002705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380371607730544856001803 570557411595817284002705)
          ·
            refine ⟨427918058696862963002029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570557411595817284002705 427918058696862963002029)
            ·
              refine ⟨160469272011323611125761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427918058696862963002029 160469272011323611125761)
              ·
                refine ⟨120351954008492708344321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160469272011323611125761 120351954008492708344321)
                ·
                  refine ⟨90263965506369531258241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120351954008492708344321 90263965506369531258241)
                  ·
                    refine ⟨67697974129777148443681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90263965506369531258241 67697974129777148443681)
                    ·
                      refine ⟨50773480597332861332761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67697974129777148443681 50773480597332861332761)
                      ·
                        rfl

theorem cell23_98881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_98881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98881 prefixEnd_98881 := by exact prefixLift 98881
  have htrace : WordTrace (prefixWord ++ tailWord_98881) baseStart_98881 baseEnd_98881 := by
    simpa [prefixWord, tailWord_98881, baseEnd_98881] using wordTrace_append hprefix tailTrace_98881
  have hstable : (prefixWord ++ tailWord_98881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98881).length < 2 ^ (prefixWord ++ tailWord_98881).sum := by decide
  have hdescent : baseEnd_98881 < baseStart_98881 := by decide
  rcases family_descends (prefixWord ++ tailWord_98881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98887 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 5]
def baseStart_98887 : Nat := 118140960795 + 98887 * 2 ^ 59
def prefixEnd_98887 : Nat := 4983230072969 + 3 ^ 40 * 98887 * 2
def baseEnd_98887 : Nat := 5641840164584426428637

theorem tailTrace_98887 : CollatzResearch.WordTrace tailWord_98887 prefixEnd_98887 5641840164584426428637 := by
  unfold tailWord_98887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606705192756762400142915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2404470128504508266761943 3606705192756762400142915)
  ·
    refine ⟨5410057789135143600214373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606705192756762400142915 5410057789135143600214373)
    ·
      refine ⟨1014385835462839425040195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5410057789135143600214373 1014385835462839425040195)
      ·
        refine ⟨1521578753194259137560293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014385835462839425040195 1521578753194259137560293)
        ·
          refine ⟨285296016223923588292555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1521578753194259137560293 285296016223923588292555)
          ·
            refine ⟨427944024335885382438833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285296016223923588292555 427944024335885382438833)
            ·
              refine ⟨320958018251914036829125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427944024335885382438833 320958018251914036829125)
              ·
                refine ⟨60179628422233881905461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320958018251914036829125 60179628422233881905461)
                ·
                  refine ⟨5641840164584426428637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60179628422233881905461 5641840164584426428637)
                  ·
                    rfl

theorem cell23_98887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 5].length) (baseStart_98887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98887 prefixEnd_98887 := by exact prefixLift 98887
  have htrace : WordTrace (prefixWord ++ tailWord_98887) baseStart_98887 baseEnd_98887 := by
    simpa [prefixWord, tailWord_98887, baseEnd_98887] using wordTrace_append hprefix tailTrace_98887
  have hstable : (prefixWord ++ tailWord_98887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98887).length < 2 ^ (prefixWord ++ tailWord_98887).sum := by decide
  have hdescent : baseEnd_98887 < baseStart_98887 := by decide
  rcases family_descends (prefixWord ++ tailWord_98887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98900 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_98900 : Nat := 118140960795 + 98900 * 2 ^ 59
def prefixEnd_98900 : Nat := 4983230072969 + 3 ^ 40 * 98900 * 2
def baseEnd_98900 : Nat := 16927745576589428998391

theorem tailTrace_98900 : CollatzResearch.WordTrace tailWord_98900 prefixEnd_98900 16927745576589428998391 := by
  unfold tailWord_98900
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803589670854832810183077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2404786227806443746910769 1803589670854832810183077)
  ·
    refine ⟨338173063285281151909327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1803589670854832810183077 338173063285281151909327)
    ·
      refine ⟨507259594927921727863991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338173063285281151909327 507259594927921727863991)
      ·
        refine ⟨760889392391882591795987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507259594927921727863991 760889392391882591795987)
        ·
          refine ⟨1141334088587823887693981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760889392391882591795987 1141334088587823887693981)
          ·
            refine ⟨428000283220433957885243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1141334088587823887693981 428000283220433957885243)
            ·
              refine ⟨642000424830650936827865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428000283220433957885243 642000424830650936827865)
              ·
                refine ⟨481500318622988202620899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642000424830650936827865 481500318622988202620899)
                ·
                  refine ⟨722250477934482303931349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481500318622988202620899 722250477934482303931349)
                  ·
                    refine ⟨16927745576589428998391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 722250477934482303931349 16927745576589428998391)
                    ·
                      rfl

theorem cell23_98900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_98900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98900 prefixEnd_98900 := by exact prefixLift 98900
  have htrace : WordTrace (prefixWord ++ tailWord_98900) baseStart_98900 baseEnd_98900 := by
    simpa [prefixWord, tailWord_98900, baseEnd_98900] using wordTrace_append hprefix tailTrace_98900
  have hstable : (prefixWord ++ tailWord_98900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98900).length < 2 ^ (prefixWord ++ tailWord_98900).sum := by decide
  have hdescent : baseEnd_98900 < baseStart_98900 := by decide
  rcases family_descends (prefixWord ++ tailWord_98900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98934 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_98934 : Nat := 118140960795 + 98934 * 2 ^ 59
def prefixEnd_98934 : Nat := 4983230072969 + 3 ^ 40 * 98934 * 2
def baseEnd_98934 : Nat := 16933565024007051323339

theorem tailTrace_98934 : CollatzResearch.WordTrace tailWord_98934 prefixEnd_98934 16933565024007051323339 := by
  unfold tailWord_98934
  simp only [CollatzResearch.WordTrace]
  refine ⟨225526213974155589193991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2405612949057659618069237 225526213974155589193991)
  ·
    refine ⟨338289320961233383790987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225526213974155589193991 338289320961233383790987)
    ·
      refine ⟨507433981441850075686481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338289320961233383790987 507433981441850075686481)
      ·
        refine ⟨380575486081387556764861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507433981441850075686481 380575486081387556764861)
        ·
          refine ⟨142715807280520333786823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380575486081387556764861 142715807280520333786823)
          ·
            refine ⟨214073710920780500680235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142715807280520333786823 214073710920780500680235)
            ·
              refine ⟨321110566381170751020353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214073710920780500680235 321110566381170751020353)
              ·
                refine ⟨240832924785878063265265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321110566381170751020353 240832924785878063265265)
                ·
                  refine ⟨180624693589408547448949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240832924785878063265265 180624693589408547448949)
                  ·
                    refine ⟨16933565024007051323339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180624693589408547448949 16933565024007051323339)
                    ·
                      rfl

theorem cell23_98934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_98934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98934 prefixEnd_98934 := by exact prefixLift 98934
  have htrace : WordTrace (prefixWord ++ tailWord_98934) baseStart_98934 baseEnd_98934 := by
    simpa [prefixWord, tailWord_98934, baseEnd_98934] using wordTrace_append hprefix tailTrace_98934
  have hstable : (prefixWord ++ tailWord_98934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98934).length < 2 ^ (prefixWord ++ tailWord_98934).sum := by decide
  have hdescent : baseEnd_98934 < baseStart_98934 := by decide
  rcases family_descends (prefixWord ++ tailWord_98934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98937 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_98937 : Nat := 118140960795 + 98937 * 2 ^ 59
def prefixEnd_98937 : Nat := 4983230072969 + 3 ^ 40 * 98937 * 2
def baseEnd_98937 : Nat := 50802235513984642232503

theorem tailTrace_98937 : CollatzResearch.WordTrace tailWord_98937 prefixEnd_98937 50802235513984642232503 := by
  unfold tailWord_98937
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608528842575620939463065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2405685895050413959642043 3608528842575620939463065)
  ·
    refine ⟨2706396631931715704597299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3608528842575620939463065 2706396631931715704597299)
    ·
      refine ⟨4059594947897573556895949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706396631931715704597299 4059594947897573556895949)
      ·
        refine ⟨1522348105461590083835981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4059594947897573556895949 1522348105461590083835981)
        ·
          refine ⟨570880539548096281438493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1522348105461590083835981 570880539548096281438493)
          ·
            refine ⟨214080202330536105539435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 570880539548096281438493 214080202330536105539435)
            ·
              refine ⟨321120303495804158309153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214080202330536105539435 321120303495804158309153)
              ·
                refine ⟨240840227621853118731865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321120303495804158309153 240840227621853118731865)
                ·
                  refine ⟨180630170716389839048899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240840227621853118731865 180630170716389839048899)
                  ·
                    refine ⟨270945256074584758573349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180630170716389839048899 270945256074584758573349)
                    ·
                      refine ⟨50802235513984642232503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 270945256074584758573349 50802235513984642232503)
                      ·
                        rfl

theorem cell23_98937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_98937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98937 prefixEnd_98937 := by exact prefixLift 98937
  have htrace : WordTrace (prefixWord ++ tailWord_98937) baseStart_98937 baseEnd_98937 := by
    simpa [prefixWord, tailWord_98937, baseEnd_98937] using wordTrace_append hprefix tailTrace_98937
  have hstable : (prefixWord ++ tailWord_98937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98937).length < 2 ^ (prefixWord ++ tailWord_98937).sum := by decide
  have hdescent : baseEnd_98937 < baseStart_98937 := by decide
  rcases family_descends (prefixWord ++ tailWord_98937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98947 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 3, 4]
def baseStart_98947 : Nat := 118140960795 + 98947 * 2 ^ 59
def prefixEnd_98947 : Nat := 4983230072969 + 3 ^ 40 * 98947 * 2
def baseEnd_98947 : Nat := 16935790106843201035819

theorem tailTrace_98947 : CollatzResearch.WordTrace tailWord_98947 prefixEnd_98947 16935790106843201035819 := by
  unfold tailWord_98947
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608893572539392647327095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2405929048359595098218063 3608893572539392647327095)
  ·
    refine ⟨5413340358809088970990643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608893572539392647327095 5413340358809088970990643)
    ·
      refine ⟨8120010538213633456485965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413340358809088970990643 8120010538213633456485965)
      ·
        refine ⟨3045003951830112546182237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8120010538213633456485965 3045003951830112546182237)
        ·
          refine ⟨1141876481936292204818339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3045003951830112546182237 1141876481936292204818339)
          ·
            refine ⟨1712814722904438307227509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141876481936292204818339 1712814722904438307227509)
            ·
              refine ⟨160576380272291091302579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1712814722904438307227509 160576380272291091302579)
              ·
                refine ⟨240864570408436636953869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160576380272291091302579 240864570408436636953869)
                ·
                  refine ⟨90324213903163738857701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240864570408436636953869 90324213903163738857701)
                  ·
                    refine ⟨16935790106843201035819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90324213903163738857701 16935790106843201035819)
                    ·
                      rfl

theorem cell23_98947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 4].length) (baseStart_98947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_98947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_98947 prefixEnd_98947 := by exact prefixLift 98947
  have htrace : WordTrace (prefixWord ++ tailWord_98947) baseStart_98947 baseEnd_98947 := by
    simpa [prefixWord, tailWord_98947, baseEnd_98947] using wordTrace_append hprefix tailTrace_98947
  have hstable : (prefixWord ++ tailWord_98947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98947).length < 2 ^ (prefixWord ++ tailWord_98947).sum := by decide
  have hdescent : baseEnd_98947 < baseStart_98947 := by decide
  rcases family_descends (prefixWord ++ tailWord_98947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99004 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_99004 : Nat := 118140960795 + 99004 * 2 ^ 59
def prefixEnd_99004 : Nat := 4983230072969 + 3 ^ 40 * 99004 * 2
def baseEnd_99004 : Nat := 50836638717835880094695

theorem tailTrace_99004 : CollatzResearch.WordTrace tailWord_99004 prefixEnd_99004 50836638717835880094695 := by
  unfold tailWord_99004
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805486266666445691076033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2407315022221927588101377 1805486266666445691076033)
  ·
    refine ⟨1354114699999834268307025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1805486266666445691076033 1354114699999834268307025)
    ·
      refine ⟨1015586024999875701230269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1354114699999834268307025 1015586024999875701230269)
      ·
        refine ⟨380844759374953387961351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1015586024999875701230269 380844759374953387961351)
        ·
          refine ⟨571267139062430081942027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380844759374953387961351 571267139062430081942027)
          ·
            refine ⟨856900708593645122913041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571267139062430081942027 856900708593645122913041)
            ·
              refine ⟨642675531445233842184781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856900708593645122913041 642675531445233842184781)
              ·
                refine ⟨241003324291962690819293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642675531445233842184781 241003324291962690819293)
                ·
                  refine ⟨90376246609486009057235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241003324291962690819293 90376246609486009057235)
                  ·
                    refine ⟨135564369914229013585853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90376246609486009057235 135564369914229013585853)
                    ·
                      refine ⟨50836638717835880094695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 135564369914229013585853 50836638717835880094695)
                      ·
                        rfl

theorem cell23_99004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_99004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99004 prefixEnd_99004 := by exact prefixLift 99004
  have htrace : WordTrace (prefixWord ++ tailWord_99004) baseStart_99004 baseEnd_99004 := by
    simpa [prefixWord, tailWord_99004, baseEnd_99004] using wordTrace_append hprefix tailTrace_99004
  have hstable : (prefixWord ++ tailWord_99004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99004).length < 2 ^ (prefixWord ++ tailWord_99004).sum := by decide
  have hdescent : baseEnd_99004 < baseStart_99004 := by decide
  rcases family_descends (prefixWord ++ tailWord_99004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99031 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 2, 3, 2]
def baseStart_99031 : Nat := 118140960795 + 99031 * 2 ^ 59
def prefixEnd_99031 : Nat := 4983230072969 + 3 ^ 40 * 99031 * 2
def baseEnd_99031 : Nat := 50850502695507274457071

theorem tailTrace_99031 : CollatzResearch.WordTrace tailWord_99031 prefixEnd_99031 50850502695507274457071 := by
  unfold tailWord_99031
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611957304235074993384947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2407971536156716662256631 3611957304235074993384947)
  ·
    refine ⟨5417935956352612490077421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3611957304235074993384947 5417935956352612490077421)
    ·
      refine ⟨2031725983632229683779033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5417935956352612490077421 2031725983632229683779033)
      ·
        refine ⟨1523794487724172262834275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2031725983632229683779033 1523794487724172262834275)
        ·
          refine ⟨2285691731586258394251413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523794487724172262834275 2285691731586258394251413)
          ·
            refine ⟨107141799918105862230535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2285691731586258394251413 107141799918105862230535)
            ·
              refine ⟨160712699877158793345803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107141799918105862230535 160712699877158793345803)
              ·
                refine ⟨241069049815738190018705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160712699877158793345803 241069049815738190018705)
                ·
                  refine ⟨180801787361803642514029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241069049815738190018705 180801787361803642514029)
                  ·
                    refine ⟨67800670260676365942761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180801787361803642514029 67800670260676365942761)
                    ·
                      refine ⟨50850502695507274457071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67800670260676365942761 50850502695507274457071)
                      ·
                        rfl

theorem cell23_99031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_99031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99031 prefixEnd_99031 := by exact prefixLift 99031
  have htrace : WordTrace (prefixWord ++ tailWord_99031) baseStart_99031 baseEnd_99031 := by
    simpa [prefixWord, tailWord_99031, baseEnd_99031] using wordTrace_append hprefix tailTrace_99031
  have hstable : (prefixWord ++ tailWord_99031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99031).length < 2 ^ (prefixWord ++ tailWord_99031).sum := by decide
  have hdescent : baseEnd_99031 < baseStart_99031 := by decide
  rcases family_descends (prefixWord ++ tailWord_99031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99040 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_99040 : Nat := 118140960795 + 99040 * 2 ^ 59
def prefixEnd_99040 : Nat := 4983230072969 + 3 ^ 40 * 99040 * 2
def baseEnd_99040 : Nat := 50855124021397739244529

theorem tailTrace_99040 : CollatzResearch.WordTrace tailWord_99040 prefixEnd_99040 50855124021397739244529 := by
  unfold tailWord_99040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806142780601234765231287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2408190374134979686975049 1806142780601234765231287)
  ·
    refine ⟨2709214170901852147846931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1806142780601234765231287 2709214170901852147846931)
    ·
      refine ⟨4063821256352778221770397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2709214170901852147846931 4063821256352778221770397)
      ·
        refine ⟨1523932971132291833163899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4063821256352778221770397 1523932971132291833163899)
        ·
          refine ⟨2285899456698437749745849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523932971132291833163899 2285899456698437749745849)
          ·
            refine ⟨1714424592523828312309387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2285899456698437749745849 1714424592523828312309387)
            ·
              refine ⟨2571636888785742468464081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714424592523828312309387 2571636888785742468464081)
              ·
                refine ⟨1928727666589306851348061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571636888785742468464081 1928727666589306851348061)
                ·
                  refine ⟨723272874970990069255523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1928727666589306851348061 723272874970990069255523)
                  ·
                    refine ⟨1084909312456485103883285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 723272874970990069255523 1084909312456485103883285)
                    ·
                      refine ⟨50855124021397739244529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1084909312456485103883285 50855124021397739244529)
                      ·
                        rfl

theorem cell23_99040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_99040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99040 prefixEnd_99040 := by exact prefixLift 99040
  have htrace : WordTrace (prefixWord ++ tailWord_99040) baseStart_99040 baseEnd_99040 := by
    simpa [prefixWord, tailWord_99040, baseEnd_99040] using wordTrace_append hprefix tailTrace_99040
  have hstable : (prefixWord ++ tailWord_99040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99040).length < 2 ^ (prefixWord ++ tailWord_99040).sum := by decide
  have hdescent : baseEnd_99040 < baseStart_99040 := by decide
  rcases family_descends (prefixWord ++ tailWord_99040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99041 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 1, 5]
def baseStart_99041 : Nat := 118140960795 + 99041 * 2 ^ 59
def prefixEnd_99041 : Nat := 4983230072969 + 3 ^ 40 * 99041 * 2
def baseEnd_99041 : Nat := 16951879167350745110675

theorem tailTrace_99041 : CollatzResearch.WordTrace tailWord_99041 prefixEnd_99041 16951879167350745110675 := by
  unfold tailWord_99041
  simp only [CollatzResearch.WordTrace]
  refine ⟨3612322034198846701248977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2408214689465897800832651 3612322034198846701248977)
  ·
    refine ⟨2709241525649135025936733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3612322034198846701248977 2709241525649135025936733)
    ·
      refine ⟨1015965572118425634726275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2709241525649135025936733 1015965572118425634726275)
      ·
        refine ⟨1523948358177638452089413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015965572118425634726275 1523948358177638452089413)
        ·
          refine ⟨285740317158307209766765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1523948358177638452089413 285740317158307209766765)
          ·
            refine ⟨107152618934365203662537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285740317158307209766765 107152618934365203662537)
            ·
              refine ⟨80364464200773902746903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107152618934365203662537 80364464200773902746903)
              ·
                refine ⟨120546696301160854120355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80364464200773902746903 120546696301160854120355)
                ·
                  refine ⟨180820044451741281180533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120546696301160854120355 180820044451741281180533)
                  ·
                    refine ⟨16951879167350745110675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180820044451741281180533 16951879167350745110675)
                    ·
                      rfl

theorem cell23_99041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_99041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99041 prefixEnd_99041 := by exact prefixLift 99041
  have htrace : WordTrace (prefixWord ++ tailWord_99041) baseStart_99041 baseEnd_99041 := by
    simpa [prefixWord, tailWord_99041, baseEnd_99041] using wordTrace_append hprefix tailTrace_99041
  have hstable : (prefixWord ++ tailWord_99041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99041).length < 2 ^ (prefixWord ++ tailWord_99041).sum := by decide
  have hdescent : baseEnd_99041 < baseStart_99041 := by decide
  rcases family_descends (prefixWord ++ tailWord_99041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99044 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_99044 : Nat := 118140960795 + 99044 * 2 ^ 59
def prefixEnd_99044 : Nat := 4983230072969 + 3 ^ 40 * 99044 * 2
def baseEnd_99044 : Nat := 50857177944015723594511

theorem tailTrace_99044 : CollatzResearch.WordTrace tailWord_99044 prefixEnd_99044 50857177944015723594511 := by
  unfold tailWord_99044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806215726593989106804093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2408287635458652142405457 1806215726593989106804093)
  ·
    refine ⟨677330897472745915051535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1806215726593989106804093 677330897472745915051535)
    ·
      refine ⟨1015996346209118872577303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677330897472745915051535 1015996346209118872577303)
      ·
        refine ⟨1523994519313678308865955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015996346209118872577303 1523994519313678308865955)
        ·
          refine ⟨2285991778970517463298933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523994519313678308865955 2285991778970517463298933)
          ·
            refine ⟨214311729278486012184275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2285991778970517463298933 214311729278486012184275)
            ·
              refine ⟨321467593917729018276413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214311729278486012184275 321467593917729018276413)
              ·
                refine ⟨120550347719148381853655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321467593917729018276413 120550347719148381853655)
                ·
                  refine ⟨180825521578722572780483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120550347719148381853655 180825521578722572780483)
                  ·
                    refine ⟨271238282368083859170725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180825521578722572780483 271238282368083859170725)
                    ·
                      refine ⟨50857177944015723594511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 271238282368083859170725 50857177944015723594511)
                      ·
                        rfl

theorem cell23_99044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_99044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99044 prefixEnd_99044 := by exact prefixLift 99044
  have htrace : WordTrace (prefixWord ++ tailWord_99044) baseStart_99044 baseEnd_99044 := by
    simpa [prefixWord, tailWord_99044, baseEnd_99044] using wordTrace_append hprefix tailTrace_99044
  have hstable : (prefixWord ++ tailWord_99044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99044).length < 2 ^ (prefixWord ++ tailWord_99044).sum := by decide
  have hdescent : baseEnd_99044 < baseStart_99044 := by decide
  rcases family_descends (prefixWord ++ tailWord_99044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99054 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_99054 : Nat := 118140960795 + 99054 * 2 ^ 59
def prefixEnd_99054 : Nat := 4983230072969 + 3 ^ 40 * 99054 * 2
def baseEnd_99054 : Nat := 16954104250186894823155

theorem tailTrace_99054 : CollatzResearch.WordTrace tailWord_99054 prefixEnd_99054 16954104250186894823155 := by
  unfold tailWord_99054
  simp only [CollatzResearch.WordTrace]
  refine ⟨451599522893968740184027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2408530788767833280981477 451599522893968740184027)
  ·
    refine ⟨677399284340953110276041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451599522893968740184027 677399284340953110276041)
    ·
      refine ⟨508049463255714832707031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677399284340953110276041 508049463255714832707031)
      ·
        refine ⟨762074194883572249060547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508049463255714832707031 762074194883572249060547)
        ·
          refine ⟨1143111292325358373590821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762074194883572249060547 1143111292325358373590821)
          ·
            refine ⟨214333367311004695048279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1143111292325358373590821 214333367311004695048279)
            ·
              refine ⟨321500050966507042572419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214333367311004695048279 321500050966507042572419)
              ·
                refine ⟨482250076449760563858629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321500050966507042572419 482250076449760563858629)
                ·
                  refine ⟨90421889334330105723493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482250076449760563858629 90421889334330105723493)
                  ·
                    refine ⟨16954104250186894823155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90421889334330105723493 16954104250186894823155)
                    ·
                      rfl

theorem cell23_99054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_99054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99054 prefixEnd_99054 := by exact prefixLift 99054
  have htrace : WordTrace (prefixWord ++ tailWord_99054) baseStart_99054 baseEnd_99054 := by
    simpa [prefixWord, tailWord_99054, baseEnd_99054] using wordTrace_append hprefix tailTrace_99054
  have hstable : (prefixWord ++ tailWord_99054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99054).length < 2 ^ (prefixWord ++ tailWord_99054).sum := by decide
  have hdescent : baseEnd_99054 < baseStart_99054 := by decide
  rcases family_descends (prefixWord ++ tailWord_99054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99074 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_99074 : Nat := 118140960795 + 99074 * 2 ^ 59
def prefixEnd_99074 : Nat := 4983230072969 + 3 ^ 40 * 99074 * 2
def baseEnd_99074 : Nat := 50872582363650606219373

theorem tailTrace_99074 : CollatzResearch.WordTrace tailWord_99074 prefixEnd_99074 50872582363650606219373 := by
  unfold tailWord_99074
  simp only [CollatzResearch.WordTrace]
  refine ⟨903381410769823334300069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2409017095386195558133517 903381410769823334300069)
  ·
    refine ⟨169384014519341875181263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 903381410769823334300069 169384014519341875181263)
    ·
      refine ⟨254076021779012812771895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169384014519341875181263 254076021779012812771895)
      ·
        refine ⟨381114032668519219157843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254076021779012812771895 381114032668519219157843)
        ·
          refine ⟨571671049002778828736765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381114032668519219157843 571671049002778828736765)
          ·
            refine ⟨214376643376042060776287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 571671049002778828736765 214376643376042060776287)
            ·
              refine ⟨321564965064063091164431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214376643376042060776287 321564965064063091164431)
              ·
                refine ⟨482347447596094636746647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321564965064063091164431 482347447596094636746647)
                ·
                  refine ⟨723521171394141955119971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482347447596094636746647 723521171394141955119971)
                  ·
                    refine ⟨1085281757091212932679957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 723521171394141955119971 1085281757091212932679957)
                    ·
                      refine ⟨50872582363650606219373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1085281757091212932679957 50872582363650606219373)
                      ·
                        rfl

theorem cell23_99074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_99074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99074 prefixEnd_99074 := by exact prefixLift 99074
  have htrace : WordTrace (prefixWord ++ tailWord_99074) baseStart_99074 baseEnd_99074 := by
    simpa [prefixWord, tailWord_99074, baseEnd_99074] using wordTrace_append hprefix tailTrace_99074
  have hstable : (prefixWord ++ tailWord_99074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99074).length < 2 ^ (prefixWord ++ tailWord_99074).sum := by decide
  have hdescent : baseEnd_99074 < baseStart_99074 := by decide
  rcases family_descends (prefixWord ++ tailWord_99074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99101 : List Nat := [1, 4, 2, 4, 2, 1, 9]
def baseStart_99101 : Nat := 118140960795 + 99101 * 2 ^ 59
def prefixEnd_99101 : Nat := 4983230072969 + 3 ^ 40 * 99101 * 2
def baseEnd_99101 : Nat := 628227732608913587429

theorem tailTrace_99101 : CollatzResearch.WordTrace tailWord_99101 prefixEnd_99101 628227732608913587429 := by
  unfold tailWord_99101
  simp only [CollatzResearch.WordTrace]
  refine ⟨3614510413981476948433157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2409673609320984632288771 3614510413981476948433157)
  ·
    refine ⟨677720702621526927831217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3614510413981476948433157 677720702621526927831217)
    ·
      refine ⟨508290526966145195873413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677720702621526927831217 508290526966145195873413)
      ·
        refine ⟨95304473806152224226265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 508290526966145195873413 95304473806152224226265)
        ·
          refine ⟨71478355354614168169699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95304473806152224226265 71478355354614168169699)
          ·
            refine ⟨107217533031921252254549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71478355354614168169699 107217533031921252254549)
            ·
              refine ⟨628227732608913587429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 107217533031921252254549 628227732608913587429)
              ·
                rfl

theorem cell23_99101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 9].length) (baseStart_99101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99101 prefixEnd_99101 := by exact prefixLift 99101
  have htrace : WordTrace (prefixWord ++ tailWord_99101) baseStart_99101 baseEnd_99101 := by
    simpa [prefixWord, tailWord_99101, baseEnd_99101] using wordTrace_append hprefix tailTrace_99101
  have hstable : (prefixWord ++ tailWord_99101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99101).length < 2 ^ (prefixWord ++ tailWord_99101).sum := by decide
  have hdescent : baseEnd_99101 < baseStart_99101 := by decide
  rcases family_descends (prefixWord ++ tailWord_99101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99168 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 2, 2, 2]
def baseStart_99168 : Nat := 118140960795 + 99168 * 2 ^ 59
def prefixEnd_99168 : Nat := 4983230072969 + 3 ^ 40 * 99168 * 2
def baseEnd_99168 : Nat := 50920849545173238443941

theorem tailTrace_99168 : CollatzResearch.WordTrace tailWord_99168 prefixEnd_99168 50920849545173238443941 := by
  unfold tailWord_99168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808477052369373695561079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2411302736492498260748105 1808477052369373695561079)
  ·
    refine ⟨2712715578554060543341619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1808477052369373695561079 2712715578554060543341619)
    ·
      refine ⟨4069073367831090815012429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712715578554060543341619 4069073367831090815012429)
      ·
        refine ⟨1525902512936659055629661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4069073367831090815012429 1525902512936659055629661)
        ·
          refine ⟨572213442351247145861123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1525902512936659055629661 572213442351247145861123)
          ·
            refine ⟨858320163526870718791685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572213442351247145861123 858320163526870718791685)
            ·
              refine ⟨160935030661288259773441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 858320163526870718791685 160935030661288259773441)
              ·
                refine ⟨120701272995966194830081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160935030661288259773441 120701272995966194830081)
                ·
                  refine ⟨90525954746974646122561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120701272995966194830081 90525954746974646122561)
                  ·
                    refine ⟨67894466060230984591921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90525954746974646122561 67894466060230984591921)
                    ·
                      refine ⟨50920849545173238443941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67894466060230984591921 50920849545173238443941)
                      ·
                        rfl

theorem cell23_99168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_99168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99168 prefixEnd_99168 := by exact prefixLift 99168
  have htrace : WordTrace (prefixWord ++ tailWord_99168) baseStart_99168 baseEnd_99168 := by
    simpa [prefixWord, tailWord_99168, baseEnd_99168] using wordTrace_append hprefix tailTrace_99168
  have hstable : (prefixWord ++ tailWord_99168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99168).length < 2 ^ (prefixWord ++ tailWord_99168).sum := by decide
  have hdescent : baseEnd_99168 < baseStart_99168 := by decide
  rcases family_descends (prefixWord ++ tailWord_99168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99187 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 4, 5]
def baseStart_99187 : Nat := 118140960795 + 99187 * 2 ^ 59
def prefixEnd_99187 : Nat := 4983230072969 + 3 ^ 40 * 99187 * 2
def baseEnd_99187 : Nat := 16976868559202888035451

theorem tailTrace_99187 : CollatzResearch.WordTrace tailWord_99187 prefixEnd_99187 16976868559202888035451 := by
  unfold tailWord_99187
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617647091669913636063815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2411764727779942424042543 3617647091669913636063815)
  ·
    refine ⟨5426470637504870454095723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3617647091669913636063815 5426470637504870454095723)
    ·
      refine ⟨8139705956257305681143585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5426470637504870454095723 8139705956257305681143585)
      ·
        refine ⟨6104779467192979260857689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139705956257305681143585 6104779467192979260857689)
        ·
          refine ⟨4578584600394734445643267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104779467192979260857689 4578584600394734445643267)
          ·
            refine ⟨6867876900592101668464901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578584600394734445643267 6867876900592101668464901)
            ·
              refine ⟨1287726918861019062837169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6867876900592101668464901 1287726918861019062837169)
              ·
                refine ⟨965795189145764297127877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287726918861019062837169 965795189145764297127877)
                ·
                  refine ⟨181086597964830805711477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965795189145764297127877 181086597964830805711477)
                  ·
                    refine ⟨16976868559202888035451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181086597964830805711477 16976868559202888035451)
                    ·
                      rfl

theorem cell23_99187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 5].length) (baseStart_99187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99187 prefixEnd_99187 := by exact prefixLift 99187
  have htrace : WordTrace (prefixWord ++ tailWord_99187) baseStart_99187 baseEnd_99187 := by
    simpa [prefixWord, tailWord_99187, baseEnd_99187] using wordTrace_append hprefix tailTrace_99187
  have hstable : (prefixWord ++ tailWord_99187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99187).length < 2 ^ (prefixWord ++ tailWord_99187).sum := by decide
  have hdescent : baseEnd_99187 < baseStart_99187 := by decide
  rcases family_descends (prefixWord ++ tailWord_99187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99194 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2]
def baseStart_99194 : Nat := 118140960795 + 99194 * 2 ^ 59
def prefixEnd_99194 : Nat := 4983230072969 + 3 ^ 40 * 99194 * 2
def baseEnd_99194 : Nat := 50934200042190136718821

theorem tailTrace_99194 : CollatzResearch.WordTrace tailWord_99194 prefixEnd_99194 50934200042190136718821 := by
  unfold tailWord_99194
  simp only [CollatzResearch.WordTrace]
  refine ⟨904475600661138457892159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2411934935096369221045757 904475600661138457892159)
  ·
    refine ⟨1356713400991707686838239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 904475600661138457892159 1356713400991707686838239)
    ·
      refine ⟨2035070101487561530257359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356713400991707686838239 2035070101487561530257359)
      ·
        refine ⟨3052605152231342295386039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035070101487561530257359 3052605152231342295386039)
        ·
          refine ⟨4578907728347013443079059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052605152231342295386039 4578907728347013443079059)
          ·
            refine ⟨6868361592520520164618589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578907728347013443079059 6868361592520520164618589)
            ·
              refine ⟨2575635597195195061731971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6868361592520520164618589 2575635597195195061731971)
              ·
                refine ⟨3863453395792792592597957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575635597195195061731971 3863453395792792592597957)
                ·
                  refine ⟨724397511711148611112117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3863453395792792592597957 724397511711148611112117)
                  ·
                    refine ⟨67912266722920182291761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 724397511711148611112117 67912266722920182291761)
                    ·
                      refine ⟨50934200042190136718821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 67912266722920182291761 50934200042190136718821)
                      ·
                        rfl

theorem cell23_99194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_99194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99194 prefixEnd_99194 := by exact prefixLift 99194
  have htrace : WordTrace (prefixWord ++ tailWord_99194) baseStart_99194 baseEnd_99194 := by
    simpa [prefixWord, tailWord_99194, baseEnd_99194] using wordTrace_append hprefix tailTrace_99194
  have hstable : (prefixWord ++ tailWord_99194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99194).length < 2 ^ (prefixWord ++ tailWord_99194).sum := by decide
  have hdescent : baseEnd_99194 < baseStart_99194 := by decide
  rcases family_descends (prefixWord ++ tailWord_99194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99197 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_99197 : Nat := 118140960795 + 99197 * 2 ^ 59
def prefixEnd_99197 : Nat := 4983230072969 + 3 ^ 40 * 99197 * 2
def baseEnd_99197 : Nat := 50935740484153624981307

theorem tailTrace_99197 : CollatzResearch.WordTrace tailWord_99197 prefixEnd_99197 50935740484153624981307 := by
  unfold tailWord_99197
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618011821633685343927845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2412007881089123562618563 3618011821633685343927845)
  ·
    refine ⟨678377216556316001986471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3618011821633685343927845 678377216556316001986471)
    ·
      refine ⟨1017565824834474002979707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678377216556316001986471 1017565824834474002979707)
      ·
        refine ⟨1526348737251711004469561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017565824834474002979707 1526348737251711004469561)
        ·
          refine ⟨1144761552938783253352171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1526348737251711004469561 1144761552938783253352171)
          ·
            refine ⟨1717142329408174880028257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144761552938783253352171 1717142329408174880028257)
            ·
              refine ⟨1287856747056131160021193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717142329408174880028257 1287856747056131160021193)
              ·
                refine ⟨965892560292098370015895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287856747056131160021193 965892560292098370015895)
                ·
                  refine ⟨1448838840438147555023843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965892560292098370015895 1448838840438147555023843)
                  ·
                    refine ⟨2173258260657221332535765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1448838840438147555023843 2173258260657221332535765)
                    ·
                      refine ⟨50935740484153624981307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2173258260657221332535765 50935740484153624981307)
                      ·
                        rfl

theorem cell23_99197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_99197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99197 prefixEnd_99197 := by exact prefixLift 99197
  have htrace : WordTrace (prefixWord ++ tailWord_99197) baseStart_99197 baseEnd_99197 := by
    simpa [prefixWord, tailWord_99197, baseEnd_99197] using wordTrace_append hprefix tailTrace_99197
  have hstable : (prefixWord ++ tailWord_99197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99197).length < 2 ^ (prefixWord ++ tailWord_99197).sum := by decide
  have hdescent : baseEnd_99197 < baseStart_99197 := by decide
  rcases family_descends (prefixWord ++ tailWord_99197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99244 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_99244 : Nat := 118140960795 + 99244 * 2 ^ 59
def prefixEnd_99244 : Nat := 4983230072969 + 3 ^ 40 * 99244 * 2
def baseEnd_99244 : Nat := 50959874074914941093591

theorem tailTrace_99244 : CollatzResearch.WordTrace tailWord_99244 prefixEnd_99244 50959874074914941093591 := by
  unfold tailWord_99244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809863026231706185444393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2413150701642274913925857 1809863026231706185444393)
  ·
    refine ⟨1357397269673779639083295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1809863026231706185444393 1357397269673779639083295)
    ·
      refine ⟨2036095904510669458624943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357397269673779639083295 2036095904510669458624943)
      ·
        refine ⟨3054143856766004187937415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036095904510669458624943 3054143856766004187937415)
        ·
          refine ⟨4581215785149006281906123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054143856766004187937415 4581215785149006281906123)
          ·
            refine ⟨6871823677723509422859185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581215785149006281906123 6871823677723509422859185)
            ·
              refine ⟨5153867758292632067144389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6871823677723509422859185 5153867758292632067144389)
              ·
                refine ⟨966350204679868512589573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5153867758292632067144389 966350204679868512589573)
                ·
                  refine ⟨181190663377475346110545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966350204679868512589573 181190663377475346110545)
                  ·
                    refine ⟨135892997533106509582909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181190663377475346110545 135892997533106509582909)
                    ·
                      refine ⟨50959874074914941093591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 135892997533106509582909 50959874074914941093591)
                      ·
                        rfl

theorem cell23_99244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_99244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99244 prefixEnd_99244 := by exact prefixLift 99244
  have htrace : WordTrace (prefixWord ++ tailWord_99244) baseStart_99244 baseEnd_99244 := by
    simpa [prefixWord, tailWord_99244, baseEnd_99244] using wordTrace_append hprefix tailTrace_99244
  have hstable : (prefixWord ++ tailWord_99244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99244).length < 2 ^ (prefixWord ++ tailWord_99244).sum := by decide
  have hdescent : baseEnd_99244 < baseStart_99244 := by decide
  rcases family_descends (prefixWord ++ tailWord_99244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_99267 : Nat := 118140960795 + 99267 * 2 ^ 59
def prefixEnd_99267 : Nat := 4983230072969 + 3 ^ 40 * 99267 * 2
def baseEnd_99267 : Nat := 50971684129968351105985

theorem tailTrace_99267 : CollatzResearch.WordTrace tailWord_99267 prefixEnd_99267 50971684129968351105985 := by
  unfold tailWord_99267
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620564931380087298976055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2413709954253391532650703 3620564931380087298976055)
  ·
    refine ⟨5430847397070130948464083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3620564931380087298976055 5430847397070130948464083)
    ·
      refine ⟨8146271095605196422696125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5430847397070130948464083 8146271095605196422696125)
      ·
        refine ⟨3054851660851948658511047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8146271095605196422696125 3054851660851948658511047)
        ·
          refine ⟨4582277491277922987766571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054851660851948658511047 4582277491277922987766571)
          ·
            refine ⟨6873416236916884481649857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582277491277922987766571 6873416236916884481649857)
            ·
              refine ⟨5155062177687663361237393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6873416236916884481649857 5155062177687663361237393)
              ·
                refine ⟨3866296633265747520928045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5155062177687663361237393 3866296633265747520928045)
                ·
                  refine ⟨1449861237474655320348017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3866296633265747520928045 1449861237474655320348017)
                  ·
                    refine ⟨1087395928105991490261013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449861237474655320348017 1087395928105991490261013)
                    ·
                      refine ⟨50971684129968351105985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1087395928105991490261013 50971684129968351105985)
                      ·
                        rfl

theorem cell23_99267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_99267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99267 prefixEnd_99267 := by exact prefixLift 99267
  have htrace : WordTrace (prefixWord ++ tailWord_99267) baseStart_99267 baseEnd_99267 := by
    simpa [prefixWord, tailWord_99267, baseEnd_99267] using wordTrace_append hprefix tailTrace_99267
  have hstable : (prefixWord ++ tailWord_99267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99267).length < 2 ^ (prefixWord ++ tailWord_99267).sum := by decide
  have hdescent : baseEnd_99267 < baseStart_99267 := by decide
  rcases family_descends (prefixWord ++ tailWord_99267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99285 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_99285 : Nat := 118140960795 + 99285 * 2 ^ 59
def prefixEnd_99285 : Nat := 4983230072969 + 3 ^ 40 * 99285 * 2
def baseEnd_99285 : Nat := 16993642260583093560301

theorem tailTrace_99285 : CollatzResearch.WordTrace tailWord_99285 prefixEnd_99285 16993642260583093560301 := by
  unfold tailWord_99285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621221445314876373131309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2414147630209917582087539 3621221445314876373131309)
  ·
    refine ⟨1357958041993078639924241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3621221445314876373131309 1357958041993078639924241)
    ·
      refine ⟨1018468531494808979943181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1357958041993078639924241 1018468531494808979943181)
      ·
        refine ⟨381925699310553367478693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1018468531494808979943181 381925699310553367478693)
        ·
          refine ⟨71611068620728756402255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381925699310553367478693 71611068620728756402255)
          ·
            refine ⟨107416602931093134603383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71611068620728756402255 107416602931093134603383)
            ·
              refine ⟨161124904396639701905075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107416602931093134603383 161124904396639701905075)
              ·
                refine ⟨241687356594959552857613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161124904396639701905075 241687356594959552857613)
                ·
                  refine ⟨90632758723109832321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241687356594959552857613 90632758723109832321605)
                  ·
                    refine ⟨16993642260583093560301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90632758723109832321605 16993642260583093560301)
                    ·
                      rfl

theorem cell23_99285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_99285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99285 prefixEnd_99285 := by exact prefixLift 99285
  have htrace : WordTrace (prefixWord ++ tailWord_99285) baseStart_99285 baseEnd_99285 := by
    simpa [prefixWord, tailWord_99285, baseEnd_99285] using wordTrace_append hprefix tailTrace_99285
  have hstable : (prefixWord ++ tailWord_99285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99285).length < 2 ^ (prefixWord ++ tailWord_99285).sum := by decide
  have hdescent : baseEnd_99285 < baseStart_99285 := by decide
  rcases family_descends (prefixWord ++ tailWord_99285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99298 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_99298 : Nat := 118140960795 + 99298 * 2 ^ 59
def prefixEnd_99298 : Nat := 4983230072969 + 3 ^ 40 * 99298 * 2
def baseEnd_99298 : Nat := 5665289114473081090927

theorem tailTrace_99298 : CollatzResearch.WordTrace tailWord_99298 prefixEnd_99298 5665289114473081090927 := by
  unfold tailWord_99298
  simp only [CollatzResearch.WordTrace]
  refine ⟨905423898566944898338637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2414463729511853062236365 905423898566944898338637)
  ·
    refine ⟨339533961962604336876989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 905423898566944898338637 339533961962604336876989)
    ·
      refine ⟨127325235735976626328871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339533961962604336876989 127325235735976626328871)
      ·
        refine ⟨190987853603964939493307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127325235735976626328871 190987853603964939493307)
        ·
          refine ⟨286481780405947409239961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190987853603964939493307 286481780405947409239961)
          ·
            refine ⟨214861335304460556929971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286481780405947409239961 214861335304460556929971)
            ·
              refine ⟨322292002956690835394957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214861335304460556929971 322292002956690835394957)
              ·
                refine ⟨120859501108759063273109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322292002956690835394957 120859501108759063273109)
                ·
                  refine ⟨5665289114473081090927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120859501108759063273109 5665289114473081090927)
                  ·
                    rfl

theorem cell23_99298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_99298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99298 prefixEnd_99298 := by exact prefixLift 99298
  have htrace : WordTrace (prefixWord ++ tailWord_99298) baseStart_99298 baseEnd_99298 := by
    simpa [prefixWord, tailWord_99298, baseEnd_99298] using wordTrace_append hprefix tailTrace_99298
  have hstable : (prefixWord ++ tailWord_99298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99298).length < 2 ^ (prefixWord ++ tailWord_99298).sum := by decide
  have hdescent : baseEnd_99298 < baseStart_99298 := by decide
  rcases family_descends (prefixWord ++ tailWord_99298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99311 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 1, 5]
def baseStart_99311 : Nat := 118140960795 + 99311 * 2 ^ 59
def prefixEnd_99311 : Nat := 4983230072969 + 3 ^ 40 * 99311 * 2
def baseEnd_99311 : Nat := 16998092426255392985261

theorem tailTrace_99311 : CollatzResearch.WordTrace tailWord_99311 prefixEnd_99311 16998092426255392985261 := by
  unfold tailWord_99311
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622169743220682813577787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2414779828813788542385191 3622169743220682813577787)
  ·
    refine ⟨5433254614831024220366681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3622169743220682813577787 5433254614831024220366681)
    ·
      refine ⟨4074940961123268165275011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5433254614831024220366681 4074940961123268165275011)
      ·
        refine ⟨6112411441684902247912517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074940961123268165275011 6112411441684902247912517)
        ·
          refine ⟨1146077145315919171483597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6112411441684902247912517 1146077145315919171483597)
          ·
            refine ⟨429778929493469689306349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1146077145315919171483597 429778929493469689306349)
            ·
              refine ⟨161167098560051133489881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 429778929493469689306349 161167098560051133489881)
              ·
                refine ⟨120875323920038350117411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161167098560051133489881 120875323920038350117411)
                ·
                  refine ⟨181312985880057525176117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120875323920038350117411 181312985880057525176117)
                  ·
                    refine ⟨16998092426255392985261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181312985880057525176117 16998092426255392985261)
                    ·
                      rfl

theorem cell23_99311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_99311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99311 prefixEnd_99311 := by exact prefixLift 99311
  have htrace : WordTrace (prefixWord ++ tailWord_99311) baseStart_99311 baseEnd_99311 := by
    simpa [prefixWord, tailWord_99311, baseEnd_99311] using wordTrace_append hprefix tailTrace_99311
  have hstable : (prefixWord ++ tailWord_99311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99311).length < 2 ^ (prefixWord ++ tailWord_99311).sum := by decide
  have hdescent : baseEnd_99311 < baseStart_99311 := by decide
  rcases family_descends (prefixWord ++ tailWord_99311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99324 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_99324 : Nat := 118140960795 + 99324 * 2 ^ 59
def prefixEnd_99324 : Nat := 4983230072969 + 3 ^ 40 * 99324 * 2
def baseEnd_99324 : Nat := 17000317509091542697741

theorem tailTrace_99324 : CollatzResearch.WordTrace tailWord_99324 prefixEnd_99324 17000317509091542697741 := by
  unfold tailWord_99324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811321946086793016900513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2415095928115724022534017 1811321946086793016900513)
  ·
    refine ⟨1358491459565094762675385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1811321946086793016900513 1358491459565094762675385)
    ·
      refine ⟨1018868594673821072006539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358491459565094762675385 1018868594673821072006539)
      ·
        refine ⟨1528302892010731608009809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018868594673821072006539 1528302892010731608009809)
        ·
          refine ⟨1146227169008048706007357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528302892010731608009809 1146227169008048706007357)
          ·
            refine ⟨429835188378018264752759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1146227169008048706007357 429835188378018264752759)
            ·
              refine ⟨644752782567027397129139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429835188378018264752759 644752782567027397129139)
              ·
                refine ⟨967129173850541095693709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644752782567027397129139 967129173850541095693709)
                ·
                  refine ⟨362673440193952910885141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967129173850541095693709 362673440193952910885141)
                  ·
                    refine ⟨17000317509091542697741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 362673440193952910885141 17000317509091542697741)
                    ·
                      rfl

theorem cell23_99324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_99324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99324 prefixEnd_99324 := by exact prefixLift 99324
  have htrace : WordTrace (prefixWord ++ tailWord_99324) baseStart_99324 baseEnd_99324 := by
    simpa [prefixWord, tailWord_99324, baseEnd_99324] using wordTrace_append hprefix tailTrace_99324
  have hstable : (prefixWord ++ tailWord_99324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99324).length < 2 ^ (prefixWord ++ tailWord_99324).sum := by decide
  have hdescent : baseEnd_99324 < baseStart_99324 := by decide
  rcases family_descends (prefixWord ++ tailWord_99324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99342 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_99342 : Nat := 118140960795 + 99342 * 2 ^ 59
def prefixEnd_99342 : Nat := 4983230072969 + 3 ^ 40 * 99342 * 2
def baseEnd_99342 : Nat := 51010195179055557668141

theorem tailTrace_99342 : CollatzResearch.WordTrace tailWord_99342 prefixEnd_99342 51010195179055557668141 := by
  unfold tailWord_99342
  simp only [CollatzResearch.WordTrace]
  refine ⟨452912550763546888494535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2415533604072250071970853 452912550763546888494535)
  ·
    refine ⟨679368826145320332741803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 452912550763546888494535 679368826145320332741803)
    ·
      refine ⟨1019053239217980499112705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679368826145320332741803 1019053239217980499112705)
      ·
        refine ⟨764289929413485374334529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019053239217980499112705 764289929413485374334529)
        ·
          refine ⟨573217447060114030750897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764289929413485374334529 573217447060114030750897)
          ·
            refine ⟨429913085295085523063173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573217447060114030750897 429913085295085523063173)
            ·
              refine ⟨80608703492828535574345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 429913085295085523063173 80608703492828535574345)
              ·
                refine ⟨60456527619621401680759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80608703492828535574345 60456527619621401680759)
                ·
                  refine ⟨90684791429432102521139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60456527619621401680759 90684791429432102521139)
                  ·
                    refine ⟨136027187144148153781709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90684791429432102521139 136027187144148153781709)
                    ·
                      refine ⟨51010195179055557668141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136027187144148153781709 51010195179055557668141)
                      ·
                        rfl

theorem cell23_99342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_99342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99342 prefixEnd_99342 := by exact prefixLift 99342
  have htrace : WordTrace (prefixWord ++ tailWord_99342) baseStart_99342 baseEnd_99342 := by
    simpa [prefixWord, tailWord_99342, baseEnd_99342] using wordTrace_append hprefix tailTrace_99342
  have hstable : (prefixWord ++ tailWord_99342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99342).length < 2 ^ (prefixWord ++ tailWord_99342).sum := by decide
  have hdescent : baseEnd_99342 < baseStart_99342 := by decide
  rcases family_descends (prefixWord ++ tailWord_99342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99361 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_99361 : Nat := 118140960795 + 99361 * 2 ^ 59
def prefixEnd_99361 : Nat := 4983230072969 + 3 ^ 40 * 99361 * 2
def baseEnd_99361 : Nat := 51019951311490983330553

theorem tailTrace_99361 : CollatzResearch.WordTrace tailWord_99361 prefixEnd_99361 51019951311490983330553 := by
  unfold tailWord_99361
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623993393039541352897937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2415995595359694235265291 3623993393039541352897937)
  ·
    refine ⟨2717995044779656014673453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3623993393039541352897937 2717995044779656014673453)
    ·
      refine ⟨1019248141792371005502545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2717995044779656014673453 1019248141792371005502545)
      ·
        refine ⟨764436106344278254126909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019248141792371005502545 764436106344278254126909)
        ·
          refine ⟨286663539879104345297591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764436106344278254126909 286663539879104345297591)
          ·
            refine ⟨429995309818656517946387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286663539879104345297591 429995309818656517946387)
            ·
              refine ⟨644992964727984776919581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429995309818656517946387 644992964727984776919581)
              ·
                refine ⟨241872361772994291344843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644992964727984776919581 241872361772994291344843)
                ·
                  refine ⟨362808542659491437017265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241872361772994291344843 362808542659491437017265)
                  ·
                    refine ⟨272106406994618577762949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362808542659491437017265 272106406994618577762949)
                    ·
                      refine ⟨51019951311490983330553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 272106406994618577762949 51019951311490983330553)
                      ·
                        rfl

theorem cell23_99361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_99361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99361 prefixEnd_99361 := by exact prefixLift 99361
  have htrace : WordTrace (prefixWord ++ tailWord_99361) baseStart_99361 baseEnd_99361 := by
    simpa [prefixWord, tailWord_99361, baseEnd_99361] using wordTrace_append hprefix tailTrace_99361
  have hstable : (prefixWord ++ tailWord_99361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99361).length < 2 ^ (prefixWord ++ tailWord_99361).sum := by decide
  have hdescent : baseEnd_99361 < baseStart_99361 := by decide
  rcases family_descends (prefixWord ++ tailWord_99361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99382 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_99382 : Nat := 118140960795 + 99382 * 2 ^ 59
def prefixEnd_99382 : Nat := 4983230072969 + 3 ^ 40 * 99382 * 2
def baseEnd_99382 : Nat := 51030734405235401167957

theorem tailTrace_99382 : CollatzResearch.WordTrace tailWord_99382 prefixEnd_99382 51030734405235401167957 := by
  unfold tailWord_99382
  simp only [CollatzResearch.WordTrace]
  refine ⟨226547457872716371213275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2416506217308974626274933 226547457872716371213275)
  ·
    refine ⟨339821186809074556819913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226547457872716371213275 339821186809074556819913)
    ·
      refine ⟨254865890106805917614935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339821186809074556819913 254865890106805917614935)
      ·
        refine ⟨382298835160208876422403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254865890106805917614935 382298835160208876422403)
        ·
          refine ⟨573448252740313314633605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382298835160208876422403 573448252740313314633605)
          ·
            refine ⟨107521547388808746493801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 573448252740313314633605 107521547388808746493801)
            ·
              refine ⟨80641160541606559870351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107521547388808746493801 80641160541606559870351)
              ·
                refine ⟨120961740812409839805527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80641160541606559870351 120961740812409839805527)
                ·
                  refine ⟨181442611218614759708291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120961740812409839805527 181442611218614759708291)
                  ·
                    refine ⟨272163916827922139562437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181442611218614759708291 272163916827922139562437)
                    ·
                      refine ⟨51030734405235401167957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 272163916827922139562437 51030734405235401167957)
                      ·
                        rfl

theorem cell23_99382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_99382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99382 prefixEnd_99382 := by exact prefixLift 99382
  have htrace : WordTrace (prefixWord ++ tailWord_99382) baseStart_99382 baseEnd_99382 := by
    simpa [prefixWord, tailWord_99382, baseEnd_99382] using wordTrace_append hprefix tailTrace_99382
  have hstable : (prefixWord ++ tailWord_99382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99382).length < 2 ^ (prefixWord ++ tailWord_99382).sum := by decide
  have hdescent : baseEnd_99382 < baseStart_99382 := by decide
  rcases family_descends (prefixWord ++ tailWord_99382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99385 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 1, 2, 3]
def baseStart_99385 : Nat := 118140960795 + 99385 * 2 ^ 59
def prefixEnd_99385 : Nat := 4983230072969 + 3 ^ 40 * 99385 * 2
def baseEnd_99385 : Nat := 51032274847198889430443

theorem tailTrace_99385 : CollatzResearch.WordTrace tailWord_99385 prefixEnd_99385 51032274847198889430443 := by
  unfold tailWord_99385
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624868744952593451771609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2416579163301728967847739 3624868744952593451771609)
  ·
    refine ⟨2718651558714445088828707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3624868744952593451771609 2718651558714445088828707)
    ·
      refine ⟨4077977338071667633243061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718651558714445088828707 4077977338071667633243061)
      ·
        refine ⟨382310375444218840616537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4077977338071667633243061 382310375444218840616537)
        ·
          refine ⟨286732781583164130462403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382310375444218840616537 286732781583164130462403)
          ·
            refine ⟨430099172374746195693605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286732781583164130462403 430099172374746195693605)
            ·
              refine ⟨80643594820264911692551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 430099172374746195693605 80643594820264911692551)
              ·
                refine ⟨120965392230397367538827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80643594820264911692551 120965392230397367538827)
                ·
                  refine ⟨181448088345596051308241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120965392230397367538827 181448088345596051308241)
                  ·
                    refine ⟨136086066259197038481181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181448088345596051308241 136086066259197038481181)
                    ·
                      refine ⟨51032274847198889430443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136086066259197038481181 51032274847198889430443)
                      ·
                        rfl

theorem cell23_99385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_99385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99385 prefixEnd_99385 := by exact prefixLift 99385
  have htrace : WordTrace (prefixWord ++ tailWord_99385) baseStart_99385 baseEnd_99385 := by
    simpa [prefixWord, tailWord_99385, baseEnd_99385] using wordTrace_append hprefix tailTrace_99385
  have hstable : (prefixWord ++ tailWord_99385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99385).length < 2 ^ (prefixWord ++ tailWord_99385).sum := by decide
  have hdescent : baseEnd_99385 < baseStart_99385 := by decide
  rcases family_descends (prefixWord ++ tailWord_99385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99422 : List Nat := [4, 4, 1, 1, 1, 3, 2, 7]
def baseStart_99422 : Nat := 118140960795 + 99422 * 2 ^ 59
def prefixEnd_99422 : Nat := 4983230072969 + 3 ^ 40 * 99422 * 2
def baseEnd_99422 : Nat := 1890787912274638691399

theorem tailTrace_99422 : CollatzResearch.WordTrace tailWord_99422 prefixEnd_99422 1890787912274638691399 := by
  unfold tailWord_99422
  simp only [CollatzResearch.WordTrace]
  refine ⟨453277280727318596358565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2417478830545699180579013 453277280727318596358565)
  ·
    refine ⟨84989490136372236817231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 453277280727318596358565 84989490136372236817231)
    ·
      refine ⟨127484235204558355225847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84989490136372236817231 127484235204558355225847)
      ·
        refine ⟨191226352806837532838771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127484235204558355225847 191226352806837532838771)
        ·
          refine ⟨286839529210256299258157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191226352806837532838771 286839529210256299258157)
          ·
            refine ⟨107564823453846112221809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286839529210256299258157 107564823453846112221809)
            ·
              refine ⟨80673617590384584166357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107564823453846112221809 80673617590384584166357)
              ·
                refine ⟨1890787912274638691399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80673617590384584166357 1890787912274638691399)
                ·
                  rfl

theorem cell23_99422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_99422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99422 prefixEnd_99422 := by exact prefixLift 99422
  have htrace : WordTrace (prefixWord ++ tailWord_99422) baseStart_99422 baseEnd_99422 := by
    simpa [prefixWord, tailWord_99422, baseEnd_99422] using wordTrace_append hprefix tailTrace_99422
  have hstable : (prefixWord ++ tailWord_99422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99422).length < 2 ^ (prefixWord ++ tailWord_99422).sum := by decide
  have hdescent : baseEnd_99422 < baseStart_99422 := by decide
  rcases family_descends (prefixWord ++ tailWord_99422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99518 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_99518 : Nat := 118140960795 + 99518 * 2 ^ 59
def prefixEnd_99518 : Nat := 4983230072969 + 3 ^ 40 * 99518 * 2
def baseEnd_99518 : Nat := 51100567774246869067331

theorem tailTrace_99518 : CollatzResearch.WordTrace tailWord_99518 prefixEnd_99518 51100567774246869067331 := by
  unfold tailWord_99518
  simp only [CollatzResearch.WordTrace]
  refine ⟨453714956683844645795401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2419813102313838110908805 453714956683844645795401)
  ·
    refine ⟨340286217512883484346551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 453714956683844645795401 340286217512883484346551)
    ·
      refine ⟨510429326269325226519827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340286217512883484346551 510429326269325226519827)
      ·
        refine ⟨765643989403987839779741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510429326269325226519827 765643989403987839779741)
        ·
          refine ⟨287116496026495439917403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 765643989403987839779741 287116496026495439917403)
          ·
            refine ⟨430674744039743159876105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287116496026495439917403 430674744039743159876105)
            ·
              refine ⟨323006058029807369907079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430674744039743159876105 323006058029807369907079)
              ·
                refine ⟨484509087044711054860619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323006058029807369907079 484509087044711054860619)
                ·
                  refine ⟨726763630567066582290929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484509087044711054860619 726763630567066582290929)
                  ·
                    refine ⟨545072722925299936718197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 726763630567066582290929 545072722925299936718197)
                    ·
                      refine ⟨51100567774246869067331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 545072722925299936718197 51100567774246869067331)
                      ·
                        rfl

theorem cell23_99518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_99518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99518 prefixEnd_99518 := by exact prefixLift 99518
  have htrace : WordTrace (prefixWord ++ tailWord_99518) baseStart_99518 baseEnd_99518 := by
    simpa [prefixWord, tailWord_99518, baseEnd_99518] using wordTrace_append hprefix tailTrace_99518
  have hstable : (prefixWord ++ tailWord_99518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99518).length < 2 ^ (prefixWord ++ tailWord_99518).sum := by decide
  have hdescent : baseEnd_99518 < baseStart_99518 := by decide
  rcases family_descends (prefixWord ++ tailWord_99518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99528 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_99528 : Nat := 118140960795 + 99528 * 2 ^ 59
def prefixEnd_99528 : Nat := 4983230072969 + 3 ^ 40 * 99528 * 2
def baseEnd_99528 : Nat := 51105702580791829942285

theorem tailTrace_99528 : CollatzResearch.WordTrace tailWord_99528 prefixEnd_99528 51105702580791829942285 := by
  unfold tailWord_99528
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815042191717264437113619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2420056255623019249484825 1815042191717264437113619)
  ·
    refine ⟨2722563287575896655670429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815042191717264437113619 2722563287575896655670429)
    ·
      refine ⟨1020961232840961245876411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2722563287575896655670429 1020961232840961245876411)
      ·
        refine ⟨1531441849261441868814617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020961232840961245876411 1531441849261441868814617)
        ·
          refine ⟨1148581386946081401610963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1531441849261441868814617 1148581386946081401610963)
          ·
            refine ⟨1722872080419122102416445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148581386946081401610963 1722872080419122102416445)
            ·
              refine ⟨646077030157170788406167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1722872080419122102416445 646077030157170788406167)
              ·
                refine ⟨969115545235756182609251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646077030157170788406167 969115545235756182609251)
                ·
                  refine ⟨1453673317853634273913877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969115545235756182609251 1453673317853634273913877)
                  ·
                    refine ⟨68140936774389106589713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1453673317853634273913877 68140936774389106589713)
                    ·
                      refine ⟨51105702580791829942285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68140936774389106589713 51105702580791829942285)
                      ·
                        rfl

theorem cell23_99528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_99528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99528 prefixEnd_99528 := by exact prefixLift 99528
  have htrace : WordTrace (prefixWord ++ tailWord_99528) baseStart_99528 baseEnd_99528 := by
    simpa [prefixWord, tailWord_99528, baseEnd_99528] using wordTrace_append hprefix tailTrace_99528
  have hstable : (prefixWord ++ tailWord_99528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99528).length < 2 ^ (prefixWord ++ tailWord_99528).sum := by decide
  have hdescent : baseEnd_99528 < baseStart_99528 := by decide
  rcases family_descends (prefixWord ++ tailWord_99528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99571 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6]
def baseStart_99571 : Nat := 118140960795 + 99571 * 2 ^ 59
def prefixEnd_99571 : Nat := 4983230072969 + 3 ^ 40 * 99571 * 2
def baseEnd_99571 : Nat := 51127782248935161704587

theorem tailTrace_99571 : CollatzResearch.WordTrace tailWord_99571 prefixEnd_99571 51127782248935161704587 := by
  unfold tailWord_99571
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631652722278747218042567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2421101814852498145361711 3631652722278747218042567)
  ·
    refine ⟨5447479083418120827063851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3631652722278747218042567 5447479083418120827063851)
    ·
      refine ⟨8171218625127181240595777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5447479083418120827063851 8171218625127181240595777)
      ·
        refine ⟨6128413968845385930446833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8171218625127181240595777 6128413968845385930446833)
        ·
          refine ⟨4596310476634039447835125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128413968845385930446833 4596310476634039447835125)
          ·
            refine ⟨430904107184441198234543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4596310476634039447835125 430904107184441198234543)
            ·
              refine ⟨646356160776661797351815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430904107184441198234543 646356160776661797351815)
              ·
                refine ⟨969534241164992696027723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646356160776661797351815 969534241164992696027723)
                ·
                  refine ⟨1454301361747489044041585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969534241164992696027723 1454301361747489044041585)
                  ·
                    refine ⟨1090726021310616783031189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1454301361747489044041585 1090726021310616783031189)
                    ·
                      refine ⟨51127782248935161704587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1090726021310616783031189 51127782248935161704587)
                      ·
                        rfl

theorem cell23_99571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_99571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99571 prefixEnd_99571 := by exact prefixLift 99571
  have htrace : WordTrace (prefixWord ++ tailWord_99571) baseStart_99571 baseEnd_99571 := by
    simpa [prefixWord, tailWord_99571, baseEnd_99571] using wordTrace_append hprefix tailTrace_99571
  have hstable : (prefixWord ++ tailWord_99571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99571).length < 2 ^ (prefixWord ++ tailWord_99571).sum := by decide
  have hdescent : baseEnd_99571 < baseStart_99571 := by decide
  rcases family_descends (prefixWord ++ tailWord_99571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99585 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 6]
def baseStart_99585 : Nat := 118140960795 + 99585 * 2 ^ 59
def prefixEnd_99585 : Nat := 4983230072969 + 3 ^ 40 * 99585 * 2
def baseEnd_99585 : Nat := 5681663442010900769947

theorem tailTrace_99585 : CollatzResearch.WordTrace tailWord_99585 prefixEnd_99585 5681663442010900769947 := by
  unfold tailWord_99585
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632163344228027609052209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2421442229485351739368139 3632163344228027609052209)
  ·
    refine ⟨2724122508171020706789157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3632163344228027609052209 2724122508171020706789157)
    ·
      refine ⟨510772970282066382522967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2724122508171020706789157 510772970282066382522967)
      ·
        refine ⟨766159455423099573784451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510772970282066382522967 766159455423099573784451)
        ·
          refine ⟨1149239183134649360676677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766159455423099573784451 1149239183134649360676677)
          ·
            refine ⟨215482346837746755126877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1149239183134649360676677 215482346837746755126877)
            ·
              refine ⟨80805880064155033172579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215482346837746755126877 80805880064155033172579)
              ·
                refine ⟨121208820096232549758869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80805880064155033172579 121208820096232549758869)
                ·
                  refine ⟨5681663442010900769947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121208820096232549758869 5681663442010900769947)
                  ·
                    rfl

theorem cell23_99585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 6].length) (baseStart_99585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99585 prefixEnd_99585 := by exact prefixLift 99585
  have htrace : WordTrace (prefixWord ++ tailWord_99585) baseStart_99585 baseEnd_99585 := by
    simpa [prefixWord, tailWord_99585, baseEnd_99585] using wordTrace_append hprefix tailTrace_99585
  have hstable : (prefixWord ++ tailWord_99585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99585).length < 2 ^ (prefixWord ++ tailWord_99585).sum := by decide
  have hdescent : baseEnd_99585 < baseStart_99585 := by decide
  rcases family_descends (prefixWord ++ tailWord_99585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99595 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 3]
def baseStart_99595 : Nat := 118140960795 + 99595 * 2 ^ 59
def prefixEnd_99595 : Nat := 4983230072969 + 3 ^ 40 * 99595 * 2
def baseEnd_99595 : Nat := 51140105784643067804477

theorem tailTrace_99595 : CollatzResearch.WordTrace tailWord_99595 prefixEnd_99595 51140105784643067804477 := by
  unfold tailWord_99595
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632528074191799316916239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2421685382794532877944159 3632528074191799316916239)
  ·
    refine ⟨5448792111287698975374359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632528074191799316916239 5448792111287698975374359)
    ·
      refine ⟨8173188166931548463061539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5448792111287698975374359 8173188166931548463061539)
      ·
        refine ⟨12259782250397322694592309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173188166931548463061539 12259782250397322694592309)
        ·
          refine ⟨1149354585974749002618029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12259782250397322694592309 1149354585974749002618029)
          ·
            refine ⟨431007969740530875981761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1149354585974749002618029 431007969740530875981761)
            ·
              refine ⟨323255977305398156986321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431007969740530875981761 323255977305398156986321)
              ·
                refine ⟨242441982979048617739741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323255977305398156986321 242441982979048617739741)
                ·
                  refine ⟨90915743617143231652403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242441982979048617739741 90915743617143231652403)
                  ·
                    refine ⟨136373615425714847478605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90915743617143231652403 136373615425714847478605)
                    ·
                      refine ⟨51140105784643067804477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136373615425714847478605 51140105784643067804477)
                      ·
                        rfl

theorem cell23_99595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 3].length) (baseStart_99595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99595 prefixEnd_99595 := by exact prefixLift 99595
  have htrace : WordTrace (prefixWord ++ tailWord_99595) baseStart_99595 baseEnd_99595 := by
    simpa [prefixWord, tailWord_99595, baseEnd_99595] using wordTrace_append hprefix tailTrace_99595
  have hstable : (prefixWord ++ tailWord_99595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99595).length < 2 ^ (prefixWord ++ tailWord_99595).sum := by decide
  have hdescent : baseEnd_99595 < baseStart_99595 := by decide
  rcases family_descends (prefixWord ++ tailWord_99595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99605 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_99605 : Nat := 118140960795 + 99605 * 2 ^ 59
def prefixEnd_99605 : Nat := 4983230072969 + 3 ^ 40 * 99605 * 2
def baseEnd_99605 : Nat := 51145240591188028679431

theorem tailTrace_99605 : CollatzResearch.WordTrace tailWord_99605 prefixEnd_99605 51145240591188028679431 := by
  unfold tailWord_99605
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632892804155571024780269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2421928536103714016520179 3632892804155571024780269)
  ·
    refine ⟨1362334801558339134292601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3632892804155571024780269 1362334801558339134292601)
    ·
      refine ⟨1021751101168754350719451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1362334801558339134292601 1021751101168754350719451)
      ·
        refine ⟨1532626651753131526079177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021751101168754350719451 1532626651753131526079177)
        ·
          refine ⟨1149469988814848644559383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532626651753131526079177 1149469988814848644559383)
          ·
            refine ⟨1724204983222272966839075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149469988814848644559383 1724204983222272966839075)
            ·
              refine ⟨2586307474833409450258613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724204983222272966839075 2586307474833409450258613)
              ·
                refine ⟨242466325765632135961745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2586307474833409450258613 242466325765632135961745)
                ·
                  refine ⟨181849744324224101971309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242466325765632135961745 181849744324224101971309)
                  ·
                    refine ⟨68193654121584038239241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181849744324224101971309 68193654121584038239241)
                    ·
                      refine ⟨51145240591188028679431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68193654121584038239241 51145240591188028679431)
                      ·
                        rfl

theorem cell23_99605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_99605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99605 prefixEnd_99605 := by exact prefixLift 99605
  have htrace : WordTrace (prefixWord ++ tailWord_99605) baseStart_99605 baseEnd_99605 := by
    simpa [prefixWord, tailWord_99605, baseEnd_99605] using wordTrace_append hprefix tailTrace_99605
  have hstable : (prefixWord ++ tailWord_99605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99605).length < 2 ^ (prefixWord ++ tailWord_99605).sum := by decide
  have hdescent : baseEnd_99605 < baseStart_99605 := by decide
  rcases family_descends (prefixWord ++ tailWord_99605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99611 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 3, 6]
def baseStart_99611 : Nat := 118140960795 + 99611 * 2 ^ 59
def prefixEnd_99611 : Nat := 4983230072969 + 3 ^ 40 * 99611 * 2
def baseEnd_99611 : Nat := 17049440491705001734801

theorem tailTrace_99611 : CollatzResearch.WordTrace tailWord_99611 prefixEnd_99611 17049440491705001734801 := by
  unfold tailWord_99611
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633111642133834049498687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2422074428089222699665791 3633111642133834049498687)
  ·
    refine ⟨5449667463200751074248031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3633111642133834049498687 5449667463200751074248031)
    ·
      refine ⟨8174501194801126611372047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5449667463200751074248031 8174501194801126611372047)
      ·
        refine ⟨12261751792201689917058071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8174501194801126611372047 12261751792201689917058071)
        ·
          refine ⟨18392627688302534875587107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12261751792201689917058071 18392627688302534875587107)
          ·
            refine ⟨27588941532453802313380661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18392627688302534875587107 27588941532453802313380661)
            ·
              refine ⟨2586463268667543966879437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27588941532453802313380661 2586463268667543966879437)
              ·
                refine ⟨969923725750328987579789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586463268667543966879437 969923725750328987579789)
                ·
                  refine ⟨363721397156373370342421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969923725750328987579789 363721397156373370342421)
                  ·
                    refine ⟨17049440491705001734801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 363721397156373370342421 17049440491705001734801)
                    ·
                      rfl

theorem cell23_99611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_99611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99611 prefixEnd_99611 := by exact prefixLift 99611
  have htrace : WordTrace (prefixWord ++ tailWord_99611) baseStart_99611 baseEnd_99611 := by
    simpa [prefixWord, tailWord_99611, baseEnd_99611] using wordTrace_append hprefix tailTrace_99611
  have hstable : (prefixWord ++ tailWord_99611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99611).length < 2 ^ (prefixWord ++ tailWord_99611).sum := by decide
  have hdescent : baseEnd_99611 < baseStart_99611 := by decide
  rcases family_descends (prefixWord ++ tailWord_99611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99629 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_99629 : Nat := 118140960795 + 99629 * 2 ^ 59
def prefixEnd_99629 : Nat := 4983230072969 + 3 ^ 40 * 99629 * 2
def baseEnd_99629 : Nat := 51157564126895934779321

theorem tailTrace_99629 : CollatzResearch.WordTrace tailWord_99629 prefixEnd_99629 51157564126895934779321 := by
  unfold tailWord_99629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633768156068623123653941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2422512104045748749102627 3633768156068623123653941)
  ·
    refine ⟨340665764631433417842557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3633768156068623123653941 340665764631433417842557)
    ·
      refine ⟨127749661736787531690959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340665764631433417842557 127749661736787531690959)
      ·
        refine ⟨191624492605181297536439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127749661736787531690959 191624492605181297536439)
        ·
          refine ⟨287436738907771946304659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191624492605181297536439 287436738907771946304659)
          ·
            refine ⟨431155108361657919456989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287436738907771946304659 431155108361657919456989)
            ·
              refine ⟨161683165635621719796371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431155108361657919456989 161683165635621719796371)
              ·
                refine ⟨242524748453432579694557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161683165635621719796371 242524748453432579694557)
                ·
                  refine ⟨90946780670037217385459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242524748453432579694557 90946780670037217385459)
                  ·
                    refine ⟨136420171005055826078189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90946780670037217385459 136420171005055826078189)
                    ·
                      refine ⟨51157564126895934779321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136420171005055826078189 51157564126895934779321)
                      ·
                        rfl

theorem cell23_99629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_99629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99629 prefixEnd_99629 := by exact prefixLift 99629
  have htrace : WordTrace (prefixWord ++ tailWord_99629) baseStart_99629 baseEnd_99629 := by
    simpa [prefixWord, tailWord_99629, baseEnd_99629] using wordTrace_append hprefix tailTrace_99629
  have hstable : (prefixWord ++ tailWord_99629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99629).length < 2 ^ (prefixWord ++ tailWord_99629).sum := by decide
  have hdescent : baseEnd_99629 < baseStart_99629 := by decide
  rcases family_descends (prefixWord ++ tailWord_99629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99648 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_99648 : Nat := 118140960795 + 99648 * 2 ^ 59
def prefixEnd_99648 : Nat := 4983230072969 + 3 ^ 40 * 99648 * 2
def baseEnd_99648 : Nat := 51167320259331360441733

theorem tailTrace_99648 : CollatzResearch.WordTrace tailWord_99648 prefixEnd_99648 51167320259331360441733 := by
  unfold tailWord_99648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817230571499894684297799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2422974095333192912397065 1817230571499894684297799)
  ·
    refine ⟨2725845857249842026446699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1817230571499894684297799 2725845857249842026446699)
    ·
      refine ⟨4088768785874763039670049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2725845857249842026446699 4088768785874763039670049)
      ·
        refine ⟨3066576589406072279752537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4088768785874763039670049 3066576589406072279752537)
        ·
          refine ⟨2299932442054554209814403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066576589406072279752537 2299932442054554209814403)
          ·
            refine ⟨3449898663081831314721605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299932442054554209814403 3449898663081831314721605)
            ·
              refine ⟨646855999327843371510301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3449898663081831314721605 646855999327843371510301)
              ·
                refine ⟨242570999747941264316363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646855999327843371510301 242570999747941264316363)
                ·
                  refine ⟨363856499621911896474545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242570999747941264316363 363856499621911896474545)
                  ·
                    refine ⟨272892374716433922355909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 363856499621911896474545 272892374716433922355909)
                    ·
                      refine ⟨51167320259331360441733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 272892374716433922355909 51167320259331360441733)
                      ·
                        rfl

theorem cell23_99648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_99648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99648 prefixEnd_99648 := by exact prefixLift 99648
  have htrace : WordTrace (prefixWord ++ tailWord_99648) baseStart_99648 baseEnd_99648 := by
    simpa [prefixWord, tailWord_99648, baseEnd_99648] using wordTrace_append hprefix tailTrace_99648
  have hstable : (prefixWord ++ tailWord_99648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99648).length < 2 ^ (prefixWord ++ tailWord_99648).sum := by decide
  have hdescent : baseEnd_99648 < baseStart_99648 := by decide
  rcases family_descends (prefixWord ++ tailWord_99648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99652 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_99652 : Nat := 118140960795 + 99652 * 2 ^ 59
def prefixEnd_99652 : Nat := 4983230072969 + 3 ^ 40 * 99652 * 2
def baseEnd_99652 : Nat := 51169374181949344791715

theorem tailTrace_99652 : CollatzResearch.WordTrace tailWord_99652 prefixEnd_99652 51169374181949344791715 := by
  unfold tailWord_99652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817303517492649025870605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2423071356656865367827473 1817303517492649025870605)
  ·
    refine ⟨681488819059743384701477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1817303517492649025870605 681488819059743384701477)
    ·
      refine ⟨127779153573701884631527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 681488819059743384701477 127779153573701884631527)
      ·
        refine ⟨191668730360552826947291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127779153573701884631527 191668730360552826947291)
        ·
          refine ⟨287503095540829240420937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191668730360552826947291 287503095540829240420937)
          ·
            refine ⟨215627321655621930315703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287503095540829240420937 215627321655621930315703)
            ·
              refine ⟨323440982483432895473555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215627321655621930315703 323440982483432895473555)
              ·
                refine ⟨485161473725149343210333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323440982483432895473555 485161473725149343210333)
                ·
                  refine ⟨181935552646931003703875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485161473725149343210333 181935552646931003703875)
                  ·
                    refine ⟨272903328970396505555813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181935552646931003703875 272903328970396505555813)
                    ·
                      refine ⟨51169374181949344791715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 272903328970396505555813 51169374181949344791715)
                      ·
                        rfl

theorem cell23_99652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_99652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99652 prefixEnd_99652 := by exact prefixLift 99652
  have htrace : WordTrace (prefixWord ++ tailWord_99652) baseStart_99652 baseEnd_99652 := by
    simpa [prefixWord, tailWord_99652, baseEnd_99652] using wordTrace_append hprefix tailTrace_99652
  have hstable : (prefixWord ++ tailWord_99652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99652).length < 2 ^ (prefixWord ++ tailWord_99652).sum := by decide
  have hdescent : baseEnd_99652 < baseStart_99652 := by decide
  rcases family_descends (prefixWord ++ tailWord_99652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99655 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_99655 : Nat := 118140960795 + 99655 * 2 ^ 59
def prefixEnd_99655 : Nat := 4983230072969 + 3 ^ 40 * 99655 * 2
def baseEnd_99655 : Nat := 51170914623912833054201

theorem tailTrace_99655 : CollatzResearch.WordTrace tailWord_99655 prefixEnd_99655 51170914623912833054201 := by
  unfold tailWord_99655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634716453974429564100419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2423144302649619709400279 3634716453974429564100419)
  ·
    refine ⟨5452074680961644346150629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3634716453974429564100419 5452074680961644346150629)
    ·
      refine ⟨1022264002680308314903243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5452074680961644346150629 1022264002680308314903243)
      ·
        refine ⟨1533396004020462472354865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022264002680308314903243 1533396004020462472354865)
        ·
          refine ⟨1150047003015346854266149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1533396004020462472354865 1150047003015346854266149)
          ·
            refine ⟨215633813065377535174903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1150047003015346854266149 215633813065377535174903)
            ·
              refine ⟨323450719598066302762355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215633813065377535174903 323450719598066302762355)
              ·
                refine ⟨485176079397099454143533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323450719598066302762355 485176079397099454143533)
                ·
                  refine ⟨181941029773912295303825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485176079397099454143533 181941029773912295303825)
                  ·
                    refine ⟨136455772330434221477869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181941029773912295303825 136455772330434221477869)
                    ·
                      refine ⟨51170914623912833054201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136455772330434221477869 51170914623912833054201)
                      ·
                        rfl

theorem cell23_99655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_99655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99655 prefixEnd_99655 := by exact prefixLift 99655
  have htrace : WordTrace (prefixWord ++ tailWord_99655) baseStart_99655 baseEnd_99655 := by
    simpa [prefixWord, tailWord_99655, baseEnd_99655] using wordTrace_append hprefix tailTrace_99655
  have hstable : (prefixWord ++ tailWord_99655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99655).length < 2 ^ (prefixWord ++ tailWord_99655).sum := by decide
  have hdescent : baseEnd_99655 < baseStart_99655 := by decide
  rcases family_descends (prefixWord ++ tailWord_99655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99672 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 1, 2, 3]
def baseStart_99672 : Nat := 118140960795 + 99672 * 2 ^ 59
def prefixEnd_99672 : Nat := 4983230072969 + 3 ^ 40 * 99672 * 2
def baseEnd_99672 : Nat := 51179643795039266541623

theorem tailTrace_99672 : CollatzResearch.WordTrace tailWord_99672 prefixEnd_99672 51179643795039266541623 := by
  unfold tailWord_99672
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817668247456420733734635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2423557663275227644979513 1817668247456420733734635)
  ·
    refine ⟨2726502371184631100601953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1817668247456420733734635 2726502371184631100601953)
    ·
      refine ⟨2044876778388473325451465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2726502371184631100601953 2044876778388473325451465)
      ·
        refine ⟨1533657583791354994088599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2044876778388473325451465 1533657583791354994088599)
        ·
          refine ⟨2300486375687032491132899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533657583791354994088599 2300486375687032491132899)
          ·
            refine ⟨3450729563530548736699349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300486375687032491132899 3450729563530548736699349)
            ·
              refine ⟨80876474145247236016391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3450729563530548736699349 80876474145247236016391)
              ·
                refine ⟨121314711217870854024587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80876474145247236016391 121314711217870854024587)
                ·
                  refine ⟨181972066826806281036881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121314711217870854024587 181972066826806281036881)
                  ·
                    refine ⟨136479050120104710777661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181972066826806281036881 136479050120104710777661)
                    ·
                      refine ⟨51179643795039266541623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136479050120104710777661 51179643795039266541623)
                      ·
                        rfl

theorem cell23_99672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_99672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99672 prefixEnd_99672 := by exact prefixLift 99672
  have htrace : WordTrace (prefixWord ++ tailWord_99672) baseStart_99672 baseEnd_99672 := by
    simpa [prefixWord, tailWord_99672, baseEnd_99672] using wordTrace_append hprefix tailTrace_99672
  have hstable : (prefixWord ++ tailWord_99672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99672).length < 2 ^ (prefixWord ++ tailWord_99672).sum := by decide
  have hdescent : baseEnd_99672 < baseStart_99672 := by decide
  rcases family_descends (prefixWord ++ tailWord_99672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99695 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 5, 3, 2]
def baseStart_99695 : Nat := 118140960795 + 99695 * 2 ^ 59
def prefixEnd_99695 : Nat := 4983230072969 + 3 ^ 40 * 99695 * 2
def baseEnd_99695 : Nat := 51191453850092676554017

theorem tailTrace_99695 : CollatzResearch.WordTrace tailWord_99695 prefixEnd_99695 51191453850092676554017 := by
  unfold tailWord_99695
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636175373829516395556539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2424116915886344263704359 3636175373829516395556539)
  ·
    refine ⟨5454263060744274593334809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636175373829516395556539 5454263060744274593334809)
    ·
      refine ⟨4090697295558205945001107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5454263060744274593334809 4090697295558205945001107)
      ·
        refine ⟨6136045943337308917501661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090697295558205945001107 6136045943337308917501661)
        ·
          refine ⟨2301017228751490844063123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6136045943337308917501661 2301017228751490844063123)
          ·
            refine ⟨3451525843127236266094685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301017228751490844063123 3451525843127236266094685)
            ·
              refine ⟨1294322191172713599785507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3451525843127236266094685 1294322191172713599785507)
              ·
                refine ⟨1941483286759070399678261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294322191172713599785507 1941483286759070399678261)
                ·
                  refine ⟨182014058133662849969837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1941483286759070399678261 182014058133662849969837)
                  ·
                    refine ⟨68255271800123568738689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182014058133662849969837 68255271800123568738689)
                    ·
                      refine ⟨51191453850092676554017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68255271800123568738689 51191453850092676554017)
                      ·
                        rfl

theorem cell23_99695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3, 2].length) (baseStart_99695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99695 prefixEnd_99695 := by exact prefixLift 99695
  have htrace : WordTrace (prefixWord ++ tailWord_99695) baseStart_99695 baseEnd_99695 := by
    simpa [prefixWord, tailWord_99695, baseEnd_99695] using wordTrace_append hprefix tailTrace_99695
  have hstable : (prefixWord ++ tailWord_99695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99695).length < 2 ^ (prefixWord ++ tailWord_99695).sum := by decide
  have hdescent : baseEnd_99695 < baseStart_99695 := by decide
  rcases family_descends (prefixWord ++ tailWord_99695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99708 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_99708 : Nat := 118140960795 + 99708 * 2 ^ 59
def prefixEnd_99708 : Nat := 4983230072969 + 3 ^ 40 * 99708 * 2
def baseEnd_99708 : Nat := 51198129098601125691457

theorem tailTrace_99708 : CollatzResearch.WordTrace tailWord_99708 prefixEnd_99708 51198129098601125691457 := by
  unfold tailWord_99708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818324761391209807889889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2424433015188279743853185 1818324761391209807889889)
  ·
    refine ⟨1363743571043407355917417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1818324761391209807889889 1363743571043407355917417)
    ·
      refine ⟨1022807678282555516938063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1363743571043407355917417 1022807678282555516938063)
      ·
        refine ⟨1534211517423833275407095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022807678282555516938063 1534211517423833275407095)
        ·
          refine ⟨2301317276135749913110643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534211517423833275407095 2301317276135749913110643)
          ·
            refine ⟨3451975914203624869665965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301317276135749913110643 3451975914203624869665965)
            ·
              refine ⟨1294490967826359326124737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3451975914203624869665965 1294490967826359326124737)
              ·
                refine ⟨970868225869769494593553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294490967826359326124737 970868225869769494593553)
                ·
                  refine ⟨728151169402327120945165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 970868225869769494593553 728151169402327120945165)
                  ·
                    refine ⟨273056688525872670354437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728151169402327120945165 273056688525872670354437)
                    ·
                      refine ⟨51198129098601125691457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 273056688525872670354437 51198129098601125691457)
                      ·
                        rfl

theorem cell23_99708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_99708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99708 prefixEnd_99708 := by exact prefixLift 99708
  have htrace : WordTrace (prefixWord ++ tailWord_99708) baseStart_99708 baseEnd_99708 := by
    simpa [prefixWord, tailWord_99708, baseEnd_99708] using wordTrace_append hprefix tailTrace_99708
  have hstable : (prefixWord ++ tailWord_99708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99708).length < 2 ^ (prefixWord ++ tailWord_99708).sum := by decide
  have hdescent : baseEnd_99708 < baseStart_99708 := by decide
  rcases family_descends (prefixWord ++ tailWord_99708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99736 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_99736 : Nat := 118140960795 + 99736 * 2 ^ 59
def prefixEnd_99736 : Nat := 4983230072969 + 3 ^ 40 * 99736 * 2
def baseEnd_99736 : Nat := 51212506556927016141329

theorem tailTrace_99736 : CollatzResearch.WordTrace tailWord_99736 prefixEnd_99736 51212506556927016141329 := by
  unfold tailWord_99736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818835383340490198899531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2425113844453986931866041 1818835383340490198899531)
  ·
    refine ⟨2728253075010735298349297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1818835383340490198899531 2728253075010735298349297)
    ·
      refine ⟨2046189806258051473761973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2728253075010735298349297 2046189806258051473761973)
      ·
        refine ⟨191830294336692325665185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2046189806258051473761973 191830294336692325665185)
        ·
          refine ⟨143872720752519244248889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191830294336692325665185 143872720752519244248889)
          ·
            refine ⟨107904540564389433186667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143872720752519244248889 107904540564389433186667)
            ·
              refine ⟨161856810846584149780001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107904540564389433186667 161856810846584149780001)
              ·
                refine ⟨121392608134938112335001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161856810846584149780001 121392608134938112335001)
                ·
                  refine ⟨91044456101203584251251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121392608134938112335001 91044456101203584251251)
                  ·
                    refine ⟨136566684151805376376877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91044456101203584251251 136566684151805376376877)
                    ·
                      refine ⟨51212506556927016141329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136566684151805376376877 51212506556927016141329)
                      ·
                        rfl

theorem cell23_99736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_99736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99736 prefixEnd_99736 := by exact prefixLift 99736
  have htrace : WordTrace (prefixWord ++ tailWord_99736) baseStart_99736 baseEnd_99736 := by
    simpa [prefixWord, tailWord_99736, baseEnd_99736] using wordTrace_append hprefix tailTrace_99736
  have hstable : (prefixWord ++ tailWord_99736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99736).length < 2 ^ (prefixWord ++ tailWord_99736).sum := by decide
  have hdescent : baseEnd_99736 < baseStart_99736 := by decide
  rcases family_descends (prefixWord ++ tailWord_99736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99765 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 7]
def baseStart_99765 : Nat := 118140960795 + 99765 * 2 ^ 59
def prefixEnd_99765 : Nat := 4983230072969 + 3 ^ 40 * 99765 * 2
def baseEnd_99765 : Nat := 5691933055100822519855

theorem tailTrace_99765 : CollatzResearch.WordTrace tailWord_99765 prefixEnd_99765 5691933055100822519855 := by
  unfold tailWord_99765
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638728483575918350604749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2425818989050612233736499 3638728483575918350604749)
  ·
    refine ⟨1364523181340969381476781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3638728483575918350604749 1364523181340969381476781)
    ·
      refine ⟨511696193002863518053793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1364523181340969381476781 511696193002863518053793)
      ·
        refine ⟨383772144752147638540345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511696193002863518053793 383772144752147638540345)
        ·
          refine ⟨287829108564110728905259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383772144752147638540345 287829108564110728905259)
          ·
            refine ⟨431743662846166093357889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287829108564110728905259 431743662846166093357889)
            ·
              refine ⟨323807747134624570018417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431743662846166093357889 323807747134624570018417)
              ·
                refine ⟨242855810350968427513813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323807747134624570018417 242855810350968427513813)
                ·
                  refine ⟨5691933055100822519855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 242855810350968427513813 5691933055100822519855)
                  ·
                    rfl

theorem cell23_99765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_99765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99765 prefixEnd_99765 := by exact prefixLift 99765
  have htrace : WordTrace (prefixWord ++ tailWord_99765) baseStart_99765 baseEnd_99765 := by
    simpa [prefixWord, tailWord_99765, baseEnd_99765] using wordTrace_append hprefix tailTrace_99765
  have hstable : (prefixWord ++ tailWord_99765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99765).length < 2 ^ (prefixWord ++ tailWord_99765).sum := by decide
  have hdescent : baseEnd_99765 < baseStart_99765 := by decide
  rcases family_descends (prefixWord ++ tailWord_99765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99785 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 7, 2]
def baseStart_99785 : Nat := 118140960795 + 99785 * 2 ^ 59
def prefixEnd_99785 : Nat := 4983230072969 + 3 ^ 40 * 99785 * 2
def baseEnd_99785 : Nat := 51237667108997324428603

theorem tailTrace_99785 : CollatzResearch.WordTrace tailWord_99785 prefixEnd_99785 51237667108997324428603 := by
  unfold tailWord_99785
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639457943503461766332809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2426305295668974510888539 3639457943503461766332809)
  ·
    refine ⟨2729593457627596324749607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3639457943503461766332809 2729593457627596324749607)
    ·
      refine ⟨4094390186441394487124411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2729593457627596324749607 4094390186441394487124411)
      ·
        refine ⟨6141585279662091730686617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094390186441394487124411 6141585279662091730686617)
        ·
          refine ⟨4606188959746568798014963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6141585279662091730686617 4606188959746568798014963)
          ·
            refine ⟨6909283439619853197022445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606188959746568798014963 6909283439619853197022445)
            ·
              refine ⟨2590981289857444948883417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6909283439619853197022445 2590981289857444948883417)
              ·
                refine ⟨1943235967393083711662563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590981289857444948883417 1943235967393083711662563)
                ·
                  refine ⟨2914853951089625567493845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943235967393083711662563 2914853951089625567493845)
                  ·
                    refine ⟨68316889478663099238137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2914853951089625567493845 68316889478663099238137)
                    ·
                      refine ⟨51237667108997324428603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68316889478663099238137 51237667108997324428603)
                      ·
                        rfl

theorem cell23_99785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 7, 2].length) (baseStart_99785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99785 prefixEnd_99785 := by exact prefixLift 99785
  have htrace : WordTrace (prefixWord ++ tailWord_99785) baseStart_99785 baseEnd_99785 := by
    simpa [prefixWord, tailWord_99785, baseEnd_99785] using wordTrace_append hprefix tailTrace_99785
  have hstable : (prefixWord ++ tailWord_99785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99785).length < 2 ^ (prefixWord ++ tailWord_99785).sum := by decide
  have hdescent : baseEnd_99785 < baseStart_99785 := by decide
  rcases family_descends (prefixWord ++ tailWord_99785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99805 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_99805 : Nat := 118140960795 + 99805 * 2 ^ 59
def prefixEnd_99805 : Nat := 4983230072969 + 3 ^ 40 * 99805 * 2
def baseEnd_99805 : Nat := 51247936722087246178511

theorem tailTrace_99805 : CollatzResearch.WordTrace tailWord_99805 prefixEnd_99805 51247936722087246178511 := by
  unfold tailWord_99805
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640187403431005182060869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2426791602287336788040579 3640187403431005182060869)
  ·
    refine ⟨682535138143313471636413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3640187403431005182060869 682535138143313471636413)
    ·
      refine ⟨255950676803742551863655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 682535138143313471636413 255950676803742551863655)
      ·
        refine ⟨383926015205613827795483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255950676803742551863655 383926015205613827795483)
        ·
          refine ⟨575889022808420741693225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383926015205613827795483 575889022808420741693225)
          ·
            refine ⟨431916767106315556269919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575889022808420741693225 431916767106315556269919)
            ·
              refine ⟨647875150659473334404879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431916767106315556269919 647875150659473334404879)
              ·
                refine ⟨971812725989210001607319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647875150659473334404879 971812725989210001607319)
                ·
                  refine ⟨1457719088983815002410979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971812725989210001607319 1457719088983815002410979)
                  ·
                    refine ⟨2186578633475722503616469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1457719088983815002410979 2186578633475722503616469)
                    ·
                      refine ⟨51247936722087246178511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2186578633475722503616469 51247936722087246178511)
                      ·
                        rfl

theorem cell23_99805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_99805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99805 prefixEnd_99805 := by exact prefixLift 99805
  have htrace : WordTrace (prefixWord ++ tailWord_99805) baseStart_99805 baseEnd_99805 := by
    simpa [prefixWord, tailWord_99805, baseEnd_99805] using wordTrace_append hprefix tailTrace_99805
  have hstable : (prefixWord ++ tailWord_99805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99805).length < 2 ^ (prefixWord ++ tailWord_99805).sum := by decide
  have hdescent : baseEnd_99805 < baseStart_99805 := by decide
  rcases family_descends (prefixWord ++ tailWord_99805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99808 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_99808 : Nat := 118140960795 + 99808 * 2 ^ 59
def prefixEnd_99808 : Nat := 4983230072969 + 3 ^ 40 * 99808 * 2
def baseEnd_99808 : Nat := 17083159054683578146999

theorem tailTrace_99808 : CollatzResearch.WordTrace tailWord_99808 prefixEnd_99808 17083159054683578146999 := by
  unfold tailWord_99808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820148411210068347210039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2426864548280091129613385 1820148411210068347210039)
  ·
    refine ⟨2730222616815102520815059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1820148411210068347210039 2730222616815102520815059)
    ·
      refine ⟨4095333925222653781222589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2730222616815102520815059 4095333925222653781222589)
      ·
        refine ⟨1535750221958495167958471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4095333925222653781222589 1535750221958495167958471)
        ·
          refine ⟨2303625332937742751937707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535750221958495167958471 2303625332937742751937707)
          ·
            refine ⟨3455437999406614127906561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303625332937742751937707 3455437999406614127906561)
            ·
              refine ⟨2591578499554960595929921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455437999406614127906561 2591578499554960595929921)
              ·
                refine ⟨1943683874666220446947441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591578499554960595929921 1943683874666220446947441)
                ·
                  refine ⟨1457762905999665335210581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1943683874666220446947441 1457762905999665335210581)
                  ·
                    refine ⟨17083159054683578146999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1457762905999665335210581 17083159054683578146999)
                    ·
                      rfl

theorem cell23_99808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_99808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99808 prefixEnd_99808 := by exact prefixLift 99808
  have htrace : WordTrace (prefixWord ++ tailWord_99808) baseStart_99808 baseEnd_99808 := by
    simpa [prefixWord, tailWord_99808, baseEnd_99808] using wordTrace_append hprefix tailTrace_99808
  have hstable : (prefixWord ++ tailWord_99808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99808).length < 2 ^ (prefixWord ++ tailWord_99808).sum := by decide
  have hdescent : baseEnd_99808 < baseStart_99808 := by decide
  rcases family_descends (prefixWord ++ tailWord_99808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99829 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_99829 : Nat := 118140960795 + 99829 * 2 ^ 59
def prefixEnd_99829 : Nat := 4983230072969 + 3 ^ 40 * 99829 * 2
def baseEnd_99829 : Nat := 17086753419265050759467

theorem tailTrace_99829 : CollatzResearch.WordTrace tailWord_99829 prefixEnd_99829 17086753419265050759467 := by
  unfold tailWord_99829
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641062755344057280934541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2427375170229371520623027 3641062755344057280934541)
  ·
    refine ⟨1365398533254021480350453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3641062755344057280934541 1365398533254021480350453)
    ·
      refine ⟨128006112492564513782855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1365398533254021480350453 128006112492564513782855)
      ·
        refine ⟨192009168738846770674283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128006112492564513782855 192009168738846770674283)
        ·
          refine ⟨288013753108270156011425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192009168738846770674283 288013753108270156011425)
          ·
            refine ⟨216010314831202617008569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288013753108270156011425 216010314831202617008569)
            ·
              refine ⟨162007736123401962756427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216010314831202617008569 162007736123401962756427)
              ·
                refine ⟨243011604185102944134641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162007736123401962756427 243011604185102944134641)
                ·
                  refine ⟨182258703138827208100981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243011604185102944134641 182258703138827208100981)
                  ·
                    refine ⟨17086753419265050759467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182258703138827208100981 17086753419265050759467)
                    ·
                      rfl

theorem cell23_99829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_99829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99829 prefixEnd_99829 := by exact prefixLift 99829
  have htrace : WordTrace (prefixWord ++ tailWord_99829) baseStart_99829 baseEnd_99829 := by
    simpa [prefixWord, tailWord_99829, baseEnd_99829] using wordTrace_append hprefix tailTrace_99829
  have hstable : (prefixWord ++ tailWord_99829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99829).length < 2 ^ (prefixWord ++ tailWord_99829).sum := by decide
  have hdescent : baseEnd_99829 < baseStart_99829 := by decide
  rcases family_descends (prefixWord ++ tailWord_99829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99832 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_99832 : Nat := 118140960795 + 99832 * 2 ^ 59
def prefixEnd_99832 : Nat := 4983230072969 + 3 ^ 40 * 99832 * 2
def baseEnd_99832 : Nat := 51261800699758640540887

theorem tailTrace_99832 : CollatzResearch.WordTrace tailWord_99832 prefixEnd_99832 51261800699758640540887 := by
  unfold tailWord_99832
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820586087166594396646875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2427448116222125862195833 1820586087166594396646875)
  ·
    refine ⟨2730879130749891594970313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1820586087166594396646875 2730879130749891594970313)
    ·
      refine ⟨2048159348062418696227735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2730879130749891594970313 2048159348062418696227735)
      ·
        refine ⟨3072239022093628044341603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048159348062418696227735 3072239022093628044341603)
        ·
          refine ⟨4608358533140442066512405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072239022093628044341603 4608358533140442066512405)
          ·
            refine ⟨216016806240958221867769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4608358533140442066512405 216016806240958221867769)
            ·
              refine ⟨162012604680718666400827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216016806240958221867769 162012604680718666400827)
              ·
                refine ⟨243018907021077999601241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162012604680718666400827 243018907021077999601241)
                ·
                  refine ⟨182264180265808499700931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243018907021077999601241 182264180265808499700931)
                  ·
                    refine ⟨273396270398712749551397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182264180265808499700931 273396270398712749551397)
                    ·
                      refine ⟨51261800699758640540887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 273396270398712749551397 51261800699758640540887)
                      ·
                        rfl

theorem cell23_99832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_99832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99832 prefixEnd_99832 := by exact prefixLift 99832
  have htrace : WordTrace (prefixWord ++ tailWord_99832) baseStart_99832 baseEnd_99832 := by
    simpa [prefixWord, tailWord_99832, baseEnd_99832] using wordTrace_append hprefix tailTrace_99832
  have hstable : (prefixWord ++ tailWord_99832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99832).length < 2 ^ (prefixWord ++ tailWord_99832).sum := by decide
  have hdescent : baseEnd_99832 < baseStart_99832 := by decide
  rcases family_descends (prefixWord ++ tailWord_99832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99835 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 3]
def baseStart_99835 : Nat := 118140960795 + 99835 * 2 ^ 59
def prefixEnd_99835 : Nat := 4983230072969 + 3 ^ 40 * 99835 * 2
def baseEnd_99835 : Nat := 51263341141722128803373

theorem tailTrace_99835 : CollatzResearch.WordTrace tailWord_99835 prefixEnd_99835 51263341141722128803373 := by
  unfold tailWord_99835
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641281593322320305652959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2427521062214880203768639 3641281593322320305652959)
  ·
    refine ⟨5461922389983480458479439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3641281593322320305652959 5461922389983480458479439)
    ·
      refine ⟨8192883584975220687719159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5461922389983480458479439 8192883584975220687719159)
      ·
        refine ⟨12289325377462831031578739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8192883584975220687719159 12289325377462831031578739)
        ·
          refine ⟨18433988066194246547368109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12289325377462831031578739 18433988066194246547368109)
          ·
            refine ⟨6912745524822842455263041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18433988066194246547368109 6912745524822842455263041)
            ·
              refine ⟨5184559143617131841447281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912745524822842455263041 5184559143617131841447281)
              ·
                refine ⟨3888419357712848881085461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184559143617131841447281 3888419357712848881085461)
                ·
                  refine ⟨182269657392789791300881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3888419357712848881085461 182269657392789791300881)
                  ·
                    refine ⟨136702243044592343475661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182269657392789791300881 136702243044592343475661)
                    ·
                      refine ⟨51263341141722128803373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136702243044592343475661 51263341141722128803373)
                      ·
                        rfl

theorem cell23_99835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 3].length) (baseStart_99835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99835 prefixEnd_99835 := by exact prefixLift 99835
  have htrace : WordTrace (prefixWord ++ tailWord_99835) baseStart_99835 baseEnd_99835 := by
    simpa [prefixWord, tailWord_99835, baseEnd_99835] using wordTrace_append hprefix tailTrace_99835
  have hstable : (prefixWord ++ tailWord_99835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99835).length < 2 ^ (prefixWord ++ tailWord_99835).sum := by decide
  have hdescent : baseEnd_99835 < baseStart_99835 := by decide
  rcases family_descends (prefixWord ++ tailWord_99835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99859 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 1, 4]
def baseStart_99859 : Nat := 118140960795 + 99859 * 2 ^ 59
def prefixEnd_99859 : Nat := 4983230072969 + 3 ^ 40 * 99859 * 2
def baseEnd_99859 : Nat := 17091888225810011634421

theorem tailTrace_99859 : CollatzResearch.WordTrace tailWord_99859 prefixEnd_99859 17091888225810011634421 := by
  unfold tailWord_99859
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642156945235372404526631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2428104630156914936351087 3642156945235372404526631)
  ·
    refine ⟨5463235417853058606789947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3642156945235372404526631 5463235417853058606789947)
    ·
      refine ⟨8194853126779587910184921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5463235417853058606789947 8194853126779587910184921)
      ·
        refine ⟨6146139845084690932638691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8194853126779587910184921 6146139845084690932638691)
        ·
          refine ⟨9219209767627036398958037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146139845084690932638691 9219209767627036398958037)
          ·
            refine ⟨216075228928758665600579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9219209767627036398958037 216075228928758665600579)
            ·
              refine ⟨324112843393137998400869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216075228928758665600579 324112843393137998400869)
              ·
                refine ⟨60771158136213374700163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324112843393137998400869 60771158136213374700163)
                ·
                  refine ⟨91156737204320062050245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60771158136213374700163 91156737204320062050245)
                  ·
                    refine ⟨17091888225810011634421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91156737204320062050245 17091888225810011634421)
                    ·
                      rfl

theorem cell23_99859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 1, 4].length) (baseStart_99859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99859 prefixEnd_99859 := by exact prefixLift 99859
  have htrace : WordTrace (prefixWord ++ tailWord_99859) baseStart_99859 baseEnd_99859 := by
    simpa [prefixWord, tailWord_99859, baseEnd_99859] using wordTrace_append hprefix tailTrace_99859
  have hstable : (prefixWord ++ tailWord_99859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99859).length < 2 ^ (prefixWord ++ tailWord_99859).sum := by decide
  have hdescent : baseEnd_99859 < baseStart_99859 := by decide
  rcases family_descends (prefixWord ++ tailWord_99859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99872 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 6]
def baseStart_99872 : Nat := 118140960795 + 99872 * 2 ^ 59
def prefixEnd_99872 : Nat := 4983230072969 + 3 ^ 40 * 99872 * 2
def baseEnd_99872 : Nat := 5698037769548720448967

theorem tailTrace_99872 : CollatzResearch.WordTrace tailWord_99872 prefixEnd_99872 5698037769548720448967 := by
  unfold tailWord_99872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821315547094137812374935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2428420729458850416499913 1821315547094137812374935)
  ·
    refine ⟨2731973320641206718562403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821315547094137812374935 2731973320641206718562403)
    ·
      refine ⟨4097959980961810077843605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731973320641206718562403 4097959980961810077843605)
      ·
        refine ⟨192091874107584847398919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4097959980961810077843605 192091874107584847398919)
        ·
          refine ⟨288137811161377271098379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192091874107584847398919 288137811161377271098379)
          ·
            refine ⟨432206716742065906647569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288137811161377271098379 432206716742065906647569)
            ·
              refine ⟨324155037556549429985677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432206716742065906647569 324155037556549429985677)
              ·
                refine ⟨121558139083706036244629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324155037556549429985677 121558139083706036244629)
                ·
                  refine ⟨5698037769548720448967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121558139083706036244629 5698037769548720448967)
                  ·
                    rfl

theorem cell23_99872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_99872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99872 prefixEnd_99872 := by exact prefixLift 99872
  have htrace : WordTrace (prefixWord ++ tailWord_99872) baseStart_99872 baseEnd_99872 := by
    simpa [prefixWord, tailWord_99872, baseEnd_99872] using wordTrace_append hprefix tailTrace_99872
  have hstable : (prefixWord ++ tailWord_99872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99872).length < 2 ^ (prefixWord ++ tailWord_99872).sum := by decide
  have hdescent : baseEnd_99872 < baseStart_99872 := by decide
  rcases family_descends (prefixWord ++ tailWord_99872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99886 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_99886 : Nat := 118140960795 + 99886 * 2 ^ 59
def prefixEnd_99886 : Nat := 4983230072969 + 3 ^ 40 * 99886 * 2
def baseEnd_99886 : Nat := 51289528655101429265639

theorem tailTrace_99886 : CollatzResearch.WordTrace tailWord_99886 prefixEnd_99886 51289528655101429265639 := by
  unfold tailWord_99886
  simp only [CollatzResearch.WordTrace]
  refine ⟨455392714517194501969939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2428761144091704010506341 455392714517194501969939)
  ·
    refine ⟨683089071775791752954909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455392714517194501969939 683089071775791752954909)
    ·
      refine ⟨256158401915921907358091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 683089071775791752954909 256158401915921907358091)
      ·
        refine ⟨384237602873882861037137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256158401915921907358091 384237602873882861037137)
        ·
          refine ⟨288178202155412145777853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384237602873882861037137 288178202155412145777853)
          ·
            refine ⟨108066825808279554666695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288178202155412145777853 108066825808279554666695)
            ·
              refine ⟨162100238712419332000043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108066825808279554666695 162100238712419332000043)
              ·
                refine ⟨243150358068628998000065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162100238712419332000043 243150358068628998000065)
                ·
                  refine ⟨182362768551471748500049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243150358068628998000065 182362768551471748500049)
                  ·
                    refine ⟨136772076413603811375037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182362768551471748500049 136772076413603811375037)
                    ·
                      refine ⟨51289528655101429265639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136772076413603811375037 51289528655101429265639)
                      ·
                        rfl

theorem cell23_99886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_99886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99886 prefixEnd_99886 := by exact prefixLift 99886
  have htrace : WordTrace (prefixWord ++ tailWord_99886) baseStart_99886 baseEnd_99886 := by
    simpa [prefixWord, tailWord_99886, baseEnd_99886] using wordTrace_append hprefix tailTrace_99886
  have hstable : (prefixWord ++ tailWord_99886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99886).length < 2 ^ (prefixWord ++ tailWord_99886).sum := by decide
  have hdescent : baseEnd_99886 < baseStart_99886 := by decide
  rcases family_descends (prefixWord ++ tailWord_99886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99916 : List Nat := [2, 2, 1, 3, 1, 3, 2, 4, 1, 1, 3]
def baseStart_99916 : Nat := 118140960795 + 99916 * 2 ^ 59
def prefixEnd_99916 : Nat := 4983230072969 + 3 ^ 40 * 99916 * 2
def baseEnd_99916 : Nat := 51304933074736311890501

theorem tailTrace_99916 : CollatzResearch.WordTrace tailWord_99916 prefixEnd_99916 51304933074736311890501 := by
  unfold tailWord_99916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822117953014435569675801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2429490604019247426234401 1822117953014435569675801)
  ·
    refine ⟨1366588464760826677256851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1822117953014435569675801 1366588464760826677256851)
    ·
      refine ⟨2049882697141240015885277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366588464760826677256851 2049882697141240015885277)
      ·
        refine ⟨768706011427965005956979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2049882697141240015885277 768706011427965005956979)
        ·
          refine ⟨1153059017141947508935469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768706011427965005956979 1153059017141947508935469)
          ·
            refine ⟨432397131428230315850801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1153059017141947508935469 432397131428230315850801)
            ·
              refine ⟨324297848571172736888101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432397131428230315850801 324297848571172736888101)
              ·
                refine ⟨60805846607094888166519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324297848571172736888101 60805846607094888166519)
                ·
                  refine ⟨91208769910642332249779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60805846607094888166519 91208769910642332249779)
                  ·
                    refine ⟨136813154865963498374669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91208769910642332249779 136813154865963498374669)
                    ·
                      refine ⟨51304933074736311890501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136813154865963498374669 51304933074736311890501)
                      ·
                        rfl

theorem cell23_99916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_99916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99916 prefixEnd_99916 := by exact prefixLift 99916
  have htrace : WordTrace (prefixWord ++ tailWord_99916) baseStart_99916 baseEnd_99916 := by
    simpa [prefixWord, tailWord_99916, baseEnd_99916] using wordTrace_append hprefix tailTrace_99916
  have hstable : (prefixWord ++ tailWord_99916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99916).length < 2 ^ (prefixWord ++ tailWord_99916).sum := by decide
  have hdescent : baseEnd_99916 < baseStart_99916 := by decide
  rcases family_descends (prefixWord ++ tailWord_99916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99939 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 4]
def baseStart_99939 : Nat := 118140960795 + 99939 * 2 ^ 59
def prefixEnd_99939 : Nat := 4983230072969 + 3 ^ 40 * 99939 * 2
def baseEnd_99939 : Nat := 51316743129789721902895

theorem tailTrace_99939 : CollatzResearch.WordTrace tailWord_99939 prefixEnd_99939 51316743129789721902895 := by
  unfold tailWord_99939
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645074784945546067438871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2430049856630364044959247 3645074784945546067438871)
  ·
    refine ⟨5467612177418319101158307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3645074784945546067438871 5467612177418319101158307)
    ·
      refine ⟨8201418266127478651737461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5467612177418319101158307 8201418266127478651737461)
      ·
        refine ⟨768882962449451123600387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8201418266127478651737461 768882962449451123600387)
        ·
          refine ⟨1153324443674176685400581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768882962449451123600387 1153324443674176685400581)
          ·
            refine ⟨216248333188908128512609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1153324443674176685400581 216248333188908128512609)
            ·
              refine ⟨162186249891681096384457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216248333188908128512609 162186249891681096384457)
              ·
                refine ⟨121639687418760822288343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162186249891681096384457 121639687418760822288343)
                ·
                  refine ⟨182459531128141233432515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121639687418760822288343 182459531128141233432515)
                  ·
                    refine ⟨273689296692211850148773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182459531128141233432515 273689296692211850148773)
                    ·
                      refine ⟨51316743129789721902895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 273689296692211850148773 51316743129789721902895)
                      ·
                        rfl

theorem cell23_99939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_99939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99939 prefixEnd_99939 := by exact prefixLift 99939
  have htrace : WordTrace (prefixWord ++ tailWord_99939) baseStart_99939 baseEnd_99939 := by
    simpa [prefixWord, tailWord_99939, baseEnd_99939] using wordTrace_append hprefix tailTrace_99939
  have hstable : (prefixWord ++ tailWord_99939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99939).length < 2 ^ (prefixWord ++ tailWord_99939).sum := by decide
  have hdescent : baseEnd_99939 < baseStart_99939 := by decide
  rcases family_descends (prefixWord ++ tailWord_99939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99950 : List Nat := [4, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_99950 : Nat := 118140960795 + 99950 * 2 ^ 59
def prefixEnd_99950 : Nat := 4983230072969 + 3 ^ 40 * 99950 * 2
def baseEnd_99950 : Nat := 51322391416989178865345

theorem tailTrace_99950 : CollatzResearch.WordTrace tailWord_99950 prefixEnd_99950 51322391416989178865345 := by
  unfold tailWord_99950
  simp only [CollatzResearch.WordTrace]
  refine ⟨455684498488211868261163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2430317325270463297392869 455684498488211868261163)
  ·
    refine ⟨683526747732317802391745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455684498488211868261163 683526747732317802391745)
    ·
      refine ⟨512645060799238351793809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 683526747732317802391745 512645060799238351793809)
      ·
        refine ⟨384483795599428763845357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512645060799238351793809 384483795599428763845357)
        ·
          refine ⟨144181423349785786442009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384483795599428763845357 144181423349785786442009)
          ·
            refine ⟨108136067512339339831507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144181423349785786442009 108136067512339339831507)
            ·
              refine ⟨162204101268509009747261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108136067512339339831507 162204101268509009747261)
              ·
                refine ⟨60826537975690878655223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162204101268509009747261 60826537975690878655223)
                ·
                  refine ⟨91239806963536317982835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60826537975690878655223 91239806963536317982835)
                  ·
                    refine ⟨136859710445304476974253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91239806963536317982835 136859710445304476974253)
                    ·
                      refine ⟨51322391416989178865345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136859710445304476974253 51322391416989178865345)
                      ·
                        rfl

theorem cell23_99950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_99950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99950 prefixEnd_99950 := by exact prefixLift 99950
  have htrace : WordTrace (prefixWord ++ tailWord_99950) baseStart_99950 baseEnd_99950 := by
    simpa [prefixWord, tailWord_99950, baseEnd_99950] using wordTrace_append hprefix tailTrace_99950
  have hstable : (prefixWord ++ tailWord_99950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99950).length < 2 ^ (prefixWord ++ tailWord_99950).sum := by decide
  have hdescent : baseEnd_99950 < baseStart_99950 := by decide
  rcases family_descends (prefixWord ++ tailWord_99950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99985 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_99985 : Nat := 118140960795 + 99985 * 2 ^ 59
def prefixEnd_99985 : Nat := 4983230072969 + 3 ^ 40 * 99985 * 2
def baseEnd_99985 : Nat := 51340363239896541927683

theorem tailTrace_99985 : CollatzResearch.WordTrace tailWord_99985 prefixEnd_99985 51340363239896541927683 := by
  unfold tailWord_99985
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646752542778895923613409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2431168361852597282408939 3646752542778895923613409)
  ·
    refine ⟨2735064407084171942710057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3646752542778895923613409 2735064407084171942710057)
    ·
      refine ⟨2051298305313128957032543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2735064407084171942710057 2051298305313128957032543)
      ·
        refine ⟨3076947457969693435548815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051298305313128957032543 3076947457969693435548815)
        ·
          refine ⟨4615421186954540153323223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076947457969693435548815 4615421186954540153323223)
          ·
            refine ⟨6923131780431810229984835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615421186954540153323223 6923131780431810229984835)
            ·
              refine ⟨10384697670647715344977253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6923131780431810229984835 10384697670647715344977253)
              ·
                refine ⟨1947130813246446627183235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10384697670647715344977253 1947130813246446627183235)
                ·
                  refine ⟨2920696219869669940774853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947130813246446627183235 2920696219869669940774853)
                  ·
                    refine ⟨547630541225563113895285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920696219869669940774853 547630541225563113895285)
                    ·
                      refine ⟨51340363239896541927683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 547630541225563113895285 51340363239896541927683)
                      ·
                        rfl

theorem cell23_99985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_99985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_99985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_99985 prefixEnd_99985 := by exact prefixLift 99985
  have htrace : WordTrace (prefixWord ++ tailWord_99985) baseStart_99985 baseEnd_99985 := by
    simpa [prefixWord, tailWord_99985, baseEnd_99985] using wordTrace_append hprefix tailTrace_99985
  have hstable : (prefixWord ++ tailWord_99985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99985).length < 2 ^ (prefixWord ++ tailWord_99985).sum := by decide
  have hdescent : baseEnd_99985 < baseStart_99985 := by decide
  rcases family_descends (prefixWord ++ tailWord_99985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
