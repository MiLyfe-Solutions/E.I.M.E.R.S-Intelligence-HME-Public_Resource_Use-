import V185TrunkScan23Chunk0199

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1183940 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1183940 : Nat := 118140960795 + 1183940 * 2 ^ 59
def prefixEnd_1183940 : Nat := 4983230072969 + 3 ^ 40 * 1183940 * 2
def baseEnd_1183940 : Nat := 202643428694734354335055

theorem tailTrace_1183940 : CollatzResearch.WordTrace tailWord_1183940 prefixEnd_1183940 202643428694734354335055 := by
  unfold tailWord_1183940
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590919665397527849538637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28787892887196703799384849 21590919665397527849538637)
  ·
    refine ⟨8096594874524072943576989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21590919665397527849538637 8096594874524072943576989)
    ·
      refine ⟨3036223077946527353841371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8096594874524072943576989 3036223077946527353841371)
      ·
        refine ⟨4554334616919791030762057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036223077946527353841371 4554334616919791030762057)
        ·
          refine ⟨3415750962689843273071543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4554334616919791030762057 3415750962689843273071543)
          ·
            refine ⟨5123626444034764909607315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415750962689843273071543 5123626444034764909607315)
            ·
              refine ⟨7685439666052147364410973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5123626444034764909607315 7685439666052147364410973)
              ·
                refine ⟨2882039874769555261654115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7685439666052147364410973 2882039874769555261654115)
                ·
                  refine ⟨4323059812154332892481173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882039874769555261654115 4323059812154332892481173)
                  ·
                    refine ⟨202643428694734354335055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4323059812154332892481173 202643428694734354335055)
                    ·
                      rfl

theorem cell23_1183940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1183940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183940 prefixEnd_1183940 := by exact prefixLift 1183940
  have htrace : WordTrace (prefixWord ++ tailWord_1183940) baseStart_1183940 baseEnd_1183940 := by
    simpa [prefixWord, tailWord_1183940, baseEnd_1183940] using wordTrace_append hprefix tailTrace_1183940
  have hstable : (prefixWord ++ tailWord_1183940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183940).length < 2 ^ (prefixWord ++ tailWord_1183940).sum := by decide
  have hdescent : baseEnd_1183940 < baseStart_1183940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183947 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 3, 2, 2]
def baseStart_1183947 : Nat := 118140960795 + 1183947 * 2 ^ 59
def prefixEnd_1183947 : Nat := 4983230072969 + 3 ^ 40 * 1183947 * 2
def baseEnd_1183947 : Nat := 607933880448784535617633

theorem tailTrace_1183947 : CollatzResearch.WordTrace tailWord_1183947 prefixEnd_1183947 607933880448784535617633 := by
  unfold tailWord_1183947
  simp only [CollatzResearch.WordTrace]
  refine ⟨43182094641769695894582095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28788063094513130596388063 43182094641769695894582095)
  ·
    refine ⟨64773141962654543841873143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43182094641769695894582095 64773141962654543841873143)
    ·
      refine ⟨97159712943981815762809715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64773141962654543841873143 97159712943981815762809715)
      ·
        refine ⟨145739569415972723644214573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97159712943981815762809715 145739569415972723644214573)
        ·
          refine ⟨54652338530989771366580465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145739569415972723644214573 54652338530989771366580465)
          ·
            refine ⟨40989253898242328524935349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54652338530989771366580465 40989253898242328524935349)
            ·
              refine ⟨3842742552960218299212689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40989253898242328524935349 3842742552960218299212689)
              ·
                refine ⟨2882056914720163724409517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842742552960218299212689 2882056914720163724409517)
                ·
                  refine ⟨1080771343020061396653569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2882056914720163724409517 1080771343020061396653569)
                  ·
                    refine ⟨810578507265046047490177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1080771343020061396653569 810578507265046047490177)
                    ·
                      refine ⟨607933880448784535617633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810578507265046047490177 607933880448784535617633)
                      ·
                        rfl

theorem cell23_1183947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 2, 2].length) (baseStart_1183947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183947 prefixEnd_1183947 := by exact prefixLift 1183947
  have htrace : WordTrace (prefixWord ++ tailWord_1183947) baseStart_1183947 baseEnd_1183947 := by
    simpa [prefixWord, tailWord_1183947, baseEnd_1183947] using wordTrace_append hprefix tailTrace_1183947
  have hstable : (prefixWord ++ tailWord_1183947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183947).length < 2 ^ (prefixWord ++ tailWord_1183947).sum := by decide
  have hdescent : baseEnd_1183947 < baseStart_1183947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183958 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1183958 : Nat := 118140960795 + 1183958 * 2 ^ 59
def prefixEnd_1183958 : Nat := 4983230072969 + 3 ^ 40 * 1183958 * 2
def baseEnd_1183958 : Nat := 607939528735983992580083

theorem tailTrace_1183958 : CollatzResearch.WordTrace tailWord_1183958 prefixEnd_1183958 607939528735983992580083 := by
  unfold tailWord_1183958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698905990295615298327033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28788330563153229848821685 2698905990295615298327033)
  ·
    refine ⟨2024179492721711473745275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2698905990295615298327033 2024179492721711473745275)
    ·
      refine ⟨3036269239082567210617913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024179492721711473745275 3036269239082567210617913)
      ·
        refine ⟨2277201929311925407963435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3036269239082567210617913 2277201929311925407963435)
        ·
          refine ⟨3415802893967888111945153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277201929311925407963435 3415802893967888111945153)
          ·
            refine ⟨2561852170475916083958865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3415802893967888111945153 2561852170475916083958865)
            ·
              refine ⟨1921389127856937062969149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561852170475916083958865 1921389127856937062969149)
              ·
                refine ⟨720520922946351398613431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1921389127856937062969149 720520922946351398613431)
                ·
                  refine ⟨1080781384419527097920147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720520922946351398613431 1080781384419527097920147)
                  ·
                    refine ⟨1621172076629290646880221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1080781384419527097920147 1621172076629290646880221)
                    ·
                      refine ⟨607939528735983992580083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621172076629290646880221 607939528735983992580083)
                      ·
                        rfl

theorem cell23_1183958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1183958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183958 prefixEnd_1183958 := by exact prefixLift 1183958
  have htrace : WordTrace (prefixWord ++ tailWord_1183958) baseStart_1183958 baseEnd_1183958 := by
    simpa [prefixWord, tailWord_1183958, baseEnd_1183958] using wordTrace_append hprefix tailTrace_1183958
  have hstable : (prefixWord ++ tailWord_1183958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183958).length < 2 ^ (prefixWord ++ tailWord_1183958).sum := by decide
  have hdescent : baseEnd_1183958 < baseStart_1183958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183960 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1183960 : Nat := 118140960795 + 1183960 * 2 ^ 59
def prefixEnd_1183960 : Nat := 4983230072969 + 3 ^ 40 * 1183960 * 2
def baseEnd_1183960 : Nat := 607940555697292984755073

theorem tailTrace_1183960 : CollatzResearch.WordTrace tailWord_1183960 prefixEnd_1183960 607940555697292984755073 := by
  unfold tailWord_1183960
  simp only [CollatzResearch.WordTrace]
  refine ⟨21591284395361299557402667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28788379193815066076536889 21591284395361299557402667)
  ·
    refine ⟨32386926593041949336104001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21591284395361299557402667 32386926593041949336104001)
    ·
      refine ⟨24290194944781462002078001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32386926593041949336104001 24290194944781462002078001)
      ·
        refine ⟨18217646208586096501558501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24290194944781462002078001 18217646208586096501558501)
        ·
          refine ⟨3415808664109893094042219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18217646208586096501558501 3415808664109893094042219)
          ·
            refine ⟨5123712996164839641063329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415808664109893094042219 5123712996164839641063329)
            ·
              refine ⟨3842784747123629730797497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123712996164839641063329 3842784747123629730797497)
              ·
                refine ⟨2882088560342722298098123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842784747123629730797497 2882088560342722298098123)
                ·
                  refine ⟨4323132840514083447147185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882088560342722298098123 4323132840514083447147185)
                  ·
                    refine ⟨3242349630385562585360389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323132840514083447147185 3242349630385562585360389)
                    ·
                      refine ⟨607940555697292984755073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3242349630385562585360389 607940555697292984755073)
                      ·
                        rfl

theorem cell23_1183960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1183960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183960 prefixEnd_1183960 := by exact prefixLift 1183960
  have htrace : WordTrace (prefixWord ++ tailWord_1183960) baseStart_1183960 baseEnd_1183960 := by
    simpa [prefixWord, tailWord_1183960, baseEnd_1183960] using wordTrace_append hprefix tailTrace_1183960
  have hstable : (prefixWord ++ tailWord_1183960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183960).length < 2 ^ (prefixWord ++ tailWord_1183960).sum := by decide
  have hdescent : baseEnd_1183960 < baseStart_1183960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183981 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1183981 : Nat := 118140960795 + 1183981 * 2 ^ 59
def prefixEnd_1183981 : Nat := 4983230072969 + 3 ^ 40 * 1183981 * 2
def baseEnd_1183981 : Nat := 607951338791037402592477

theorem tailTrace_1183981 : CollatzResearch.WordTrace tailWord_1183981 prefixEnd_1183981 607951338791037402592477 := by
  unfold tailWord_1183981
  simp only [CollatzResearch.WordTrace]
  refine ⟨43183334723646519701319797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28788889815764346467546531 43183334723646519701319797)
  ·
    refine ⟨4048437630341861221998731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43183334723646519701319797 4048437630341861221998731)
    ·
      refine ⟨6072656445512791832998097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048437630341861221998731 6072656445512791832998097)
      ·
        refine ⟨4554492334134593874748573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6072656445512791832998097 4554492334134593874748573)
        ·
          refine ⟨1707934625300472703030715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4554492334134593874748573 1707934625300472703030715)
          ·
            refine ⟨2561901937950709054546073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707934625300472703030715 2561901937950709054546073)
            ·
              refine ⟨1921426453463031790909555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561901937950709054546073 1921426453463031790909555)
              ·
                refine ⟨2882139680194547686364333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921426453463031790909555 2882139680194547686364333)
                ·
                  refine ⟨1080802380072955382386625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2882139680194547686364333 1080802380072955382386625)
                  ·
                    refine ⟨810601785054716536789969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1080802380072955382386625 810601785054716536789969)
                    ·
                      refine ⟨607951338791037402592477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810601785054716536789969 607951338791037402592477)
                      ·
                        rfl

theorem cell23_1183981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1183981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183981 prefixEnd_1183981 := by exact prefixLift 1183981
  have htrace : WordTrace (prefixWord ++ tailWord_1183981) baseStart_1183981 baseEnd_1183981 := by
    simpa [prefixWord, tailWord_1183981, baseEnd_1183981] using wordTrace_append hprefix tailTrace_1183981
  have hstable : (prefixWord ++ tailWord_1183981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183981).length < 2 ^ (prefixWord ++ tailWord_1183981).sum := by decide
  have hdescent : baseEnd_1183981 < baseStart_1183981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183997 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_1183997 : Nat := 118140960795 + 1183997 * 2 ^ 59
def prefixEnd_1183997 : Nat := 4983230072969 + 3 ^ 40 * 1183997 * 2
def baseEnd_1183997 : Nat := 607959554481509339992403

theorem tailTrace_1183997 : CollatzResearch.WordTrace tailWord_1183997 prefixEnd_1183997 607959554481509339992403 := by
  unfold tailWord_1183997
  simp only [CollatzResearch.WordTrace]
  refine ⟨43183918291588554433902245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28789278861059036289268163 43183918291588554433902245)
  ·
    refine ⟨8096984679672853956356671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43183918291588554433902245 8096984679672853956356671)
    ·
      refine ⟨12145477019509280934535007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8096984679672853956356671 12145477019509280934535007)
      ·
        refine ⟨18218215529263921401802511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12145477019509280934535007 18218215529263921401802511)
        ·
          refine ⟨27327323293895882102703767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18218215529263921401802511 27327323293895882102703767)
          ·
            refine ⟨40990984940843823154055651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27327323293895882102703767 40990984940843823154055651)
            ·
              refine ⟨61486477411265734731083477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40990984940843823154055651 61486477411265734731083477)
              ·
                refine ⟨1441089314326540657759769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61486477411265734731083477 1441089314326540657759769)
                ·
                  refine ⟨1080816985744905493319827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441089314326540657759769 1080816985744905493319827)
                  ·
                    refine ⟨1621225478617358239979741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1080816985744905493319827 1621225478617358239979741)
                    ·
                      refine ⟨607959554481509339992403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621225478617358239979741 607959554481509339992403)
                      ·
                        rfl

theorem cell23_1183997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_1183997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183997 prefixEnd_1183997 := by exact prefixLift 1183997
  have htrace : WordTrace (prefixWord ++ tailWord_1183997) baseStart_1183997 baseEnd_1183997 := by
    simpa [prefixWord, tailWord_1183997, baseEnd_1183997] using wordTrace_append hprefix tailTrace_1183997
  have hstable : (prefixWord ++ tailWord_1183997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183997).length < 2 ^ (prefixWord ++ tailWord_1183997).sum := by decide
  have hdescent : baseEnd_1183997 < baseStart_1183997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184004 : List Nat := [2, 3, 2, 2, 4, 1, 2, 7]
def baseStart_1184004 : Nat := 118140960795 + 1184004 * 2 ^ 59
def prefixEnd_1184004 : Nat := 4983230072969 + 3 ^ 40 * 1184004 * 2
def baseEnd_1184004 : Nat := 22517153660966326392773

theorem tailTrace_1184004 : CollatzResearch.WordTrace tailWord_1184004 prefixEnd_1184004 22517153660966326392773 := by
  unfold tailWord_1184004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21592086801281597314703533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28789449068375463086271377 21592086801281597314703533)
  ·
    refine ⟨8097032550480598993013825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21592086801281597314703533 8097032550480598993013825)
    ·
      refine ⟨6072774412860449244760369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8097032550480598993013825 6072774412860449244760369)
      ·
        refine ⟨4554580809645336933570277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6072774412860449244760369 4554580809645336933570277)
        ·
          refine ⟨853983901808500675044427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4554580809645336933570277 853983901808500675044427)
          ·
            refine ⟨1280975852712751012566641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853983901808500675044427 1280975852712751012566641)
            ·
              refine ⟨960731889534563259424981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280975852712751012566641 960731889534563259424981)
              ·
                refine ⟨22517153660966326392773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 960731889534563259424981 22517153660966326392773)
                ·
                  rfl

theorem cell23_1184004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 7].length) (baseStart_1184004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184004 prefixEnd_1184004 := by exact prefixLift 1184004
  have htrace : WordTrace (prefixWord ++ tailWord_1184004) baseStart_1184004 baseEnd_1184004 := by
    simpa [prefixWord, tailWord_1184004, baseEnd_1184004] using wordTrace_append hprefix tailTrace_1184004
  have hstable : (prefixWord ++ tailWord_1184004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184004).length < 2 ^ (prefixWord ++ tailWord_1184004).sum := by decide
  have hdescent : baseEnd_1184004 < baseStart_1184004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184100 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1184100 : Nat := 118140960795 + 1184100 * 2 ^ 59
def prefixEnd_1184100 : Nat := 4983230072969 + 3 ^ 40 * 1184100 * 2
def baseEnd_1184100 : Nat := 608012442988922437004429

theorem tailTrace_1184100 : CollatzResearch.WordTrace tailWord_1184100 prefixEnd_1184100 608012442988922437004429 := by
  unfold tailWord_1184100
  simp only [CollatzResearch.WordTrace]
  refine ⟨21593837505107701512450877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28791783340143602016601169 21593837505107701512450877)
  ·
    refine ⟨8097689064415388067169079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21593837505107701512450877 8097689064415388067169079)
    ·
      refine ⟨12146533596623082100753619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8097689064415388067169079 12146533596623082100753619)
      ·
        refine ⟨18219800394934623151130429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12146533596623082100753619 18219800394934623151130429)
        ·
          refine ⟨6832425148100483681673911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18219800394934623151130429 6832425148100483681673911)
          ·
            refine ⟨10248637722150725522510867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6832425148100483681673911 10248637722150725522510867)
            ·
              refine ⟨15372956583226088283766301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10248637722150725522510867 15372956583226088283766301)
              ·
                refine ⟨5764858718709783106412363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15372956583226088283766301 5764858718709783106412363)
                ·
                  refine ⟨8647288078064674659618545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764858718709783106412363 8647288078064674659618545)
                  ·
                    refine ⟨6485466058548505994713909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8647288078064674659618545 6485466058548505994713909)
                    ·
                      refine ⟨608012442988922437004429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6485466058548505994713909 608012442988922437004429)
                      ·
                        rfl

theorem cell23_1184100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1184100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184100 prefixEnd_1184100 := by exact prefixLift 1184100
  have htrace : WordTrace (prefixWord ++ tailWord_1184100) baseStart_1184100 baseEnd_1184100 := by
    simpa [prefixWord, tailWord_1184100, baseEnd_1184100] using wordTrace_append hprefix tailTrace_1184100
  have hstable : (prefixWord ++ tailWord_1184100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184100).length < 2 ^ (prefixWord ++ tailWord_1184100).sum := by decide
  have hdescent : baseEnd_1184100 < baseStart_1184100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184140 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1184140 : Nat := 118140960795 + 1184140 * 2 ^ 59
def prefixEnd_1184140 : Nat := 4983230072969 + 3 ^ 40 * 1184140 * 2
def baseEnd_1184140 : Nat := 608032982215102280504245

theorem tailTrace_1184140 : CollatzResearch.WordTrace tailWord_1184140 prefixEnd_1184140 608032982215102280504245 := by
  unfold tailWord_1184140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21594566965035244928178937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28792755953380326570905249 21594566965035244928178937)
  ·
    refine ⟨16195925223776433696134203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21594566965035244928178937 16195925223776433696134203)
    ·
      refine ⟨24293887835664650544201305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16195925223776433696134203 24293887835664650544201305)
      ·
        refine ⟨18220415876748487908150979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24293887835664650544201305 18220415876748487908150979)
        ·
          refine ⟨27330623815122731862226469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18220415876748487908150979 27330623815122731862226469)
          ·
            refine ⟨5124491965335512224167463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27330623815122731862226469 5124491965335512224167463)
            ·
              refine ⟨7686737948003268336251195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124491965335512224167463 7686737948003268336251195)
              ·
                refine ⟨11530106922004902504376793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7686737948003268336251195 11530106922004902504376793)
                ·
                  refine ⟨8647580191503676878282595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11530106922004902504376793 8647580191503676878282595)
                  ·
                    refine ⟨12971370287255515317423893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8647580191503676878282595 12971370287255515317423893)
                    ·
                      refine ⟨608032982215102280504245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12971370287255515317423893 608032982215102280504245)
                      ·
                        rfl

theorem cell23_1184140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1184140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184140 prefixEnd_1184140 := by exact prefixLift 1184140
  have htrace : WordTrace (prefixWord ++ tailWord_1184140) baseStart_1184140 baseEnd_1184140 := by
    simpa [prefixWord, tailWord_1184140, baseEnd_1184140] using wordTrace_append hprefix tailTrace_1184140
  have hstable : (prefixWord ++ tailWord_1184140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184140).length < 2 ^ (prefixWord ++ tailWord_1184140).sum := by decide
  have hdescent : baseEnd_1184140 < baseStart_1184140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184154 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_1184154 : Nat := 118140960795 + 1184154 * 2 ^ 59
def prefixEnd_1184154 : Nat := 4983230072969 + 3 ^ 40 * 1184154 * 2
def baseEnd_1184154 : Nat := 202680056981421741909727

theorem tailTrace_1184154 : CollatzResearch.WordTrace tailWord_1184154 prefixEnd_1184154 202680056981421741909727 := by
  unfold tailWord_1184154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10797411138004942561841879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28793096368013180164911677 10797411138004942561841879)
  ·
    refine ⟨16196116707007413842762819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10797411138004942561841879 16196116707007413842762819)
    ·
      refine ⟨24294175060511120764144229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16196116707007413842762819 24294175060511120764144229)
      ·
        refine ⟨4555157823845835143277043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24294175060511120764144229 4555157823845835143277043)
        ·
          refine ⟨6832736735768752714915565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555157823845835143277043 6832736735768752714915565)
          ·
            refine ⟨2562276275913282268093337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6832736735768752714915565 2562276275913282268093337)
            ·
              refine ⟨1921707206934961701070003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2562276275913282268093337 1921707206934961701070003)
              ·
                refine ⟨2882560810402442551605005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921707206934961701070003 2882560810402442551605005)
                ·
                  refine ⟨1080960303900915956851877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2882560810402442551605005 1080960303900915956851877)
                  ·
                    refine ⟨202680056981421741909727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1080960303900915956851877 202680056981421741909727)
                    ·
                      rfl

theorem cell23_1184154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_1184154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184154 prefixEnd_1184154 := by exact prefixLift 1184154
  have htrace : WordTrace (prefixWord ++ tailWord_1184154) baseStart_1184154 baseEnd_1184154 := by
    simpa [prefixWord, tailWord_1184154, baseEnd_1184154] using wordTrace_append hprefix tailTrace_1184154
  have hstable : (prefixWord ++ tailWord_1184154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184154).length < 2 ^ (prefixWord ++ tailWord_1184154).sum := by decide
  have hdescent : baseEnd_1184154 < baseStart_1184154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184188 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_1184188 : Nat := 118140960795 + 1184188 * 2 ^ 59
def prefixEnd_1184188 : Nat := 4983230072969 + 3 ^ 40 * 1184188 * 2
def baseEnd_1184188 : Nat := 202685876428839364234675

theorem tailTrace_1184188 : CollatzResearch.WordTrace tailWord_1184188 prefixEnd_1184188 202685876428839364234675 := by
  unfold tailWord_1184188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21595442316948297027052609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28793923089264396036070145 21595442316948297027052609)
  ·
    refine ⟨16196581737711222770289457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21595442316948297027052609 16196581737711222770289457)
    ·
      refine ⟨12147436303283417077717093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16196581737711222770289457 12147436303283417077717093)
      ·
        refine ⟨2277644306865640702071955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12147436303283417077717093 2277644306865640702071955)
        ·
          refine ⟨3416466460298461053107933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277644306865640702071955 3416466460298461053107933)
          ·
            refine ⟨1281174922611922894915475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3416466460298461053107933 1281174922611922894915475)
            ·
              refine ⟨1921762383917884342373213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281174922611922894915475 1921762383917884342373213)
              ·
                refine ⟨720660893969206628389955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1921762383917884342373213 720660893969206628389955)
                ·
                  refine ⟨1080991340953809942584933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720660893969206628389955 1080991340953809942584933)
                  ·
                    refine ⟨202685876428839364234675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1080991340953809942584933 202685876428839364234675)
                    ·
                      rfl

theorem cell23_1184188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_1184188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184188 prefixEnd_1184188 := by exact prefixLift 1184188
  have htrace : WordTrace (prefixWord ++ tailWord_1184188) baseStart_1184188 baseEnd_1184188 := by
    simpa [prefixWord, tailWord_1184188, baseEnd_1184188] using wordTrace_append hprefix tailTrace_1184188
  have hstable : (prefixWord ++ tailWord_1184188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184188).length < 2 ^ (prefixWord ++ tailWord_1184188).sum := by decide
  have hdescent : baseEnd_1184188 < baseStart_1184188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184214 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1184214 : Nat := 118140960795 + 1184214 * 2 ^ 59
def prefixEnd_1184214 : Nat := 4983230072969 + 3 ^ 40 * 1184214 * 2
def baseEnd_1184214 : Nat := 202690326594511663659635

theorem tailTrace_1184214 : CollatzResearch.WordTrace tailWord_1184214 prefixEnd_1184214 202690326594511663659635 := by
  unfold tailWord_1184214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699489558237650030909481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28794555287868266996367797 2699489558237650030909481)
  ·
    refine ⟨2024617168678237523182111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2699489558237650030909481 2024617168678237523182111)
    ·
      refine ⟨3036925753017356284773167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024617168678237523182111 3036925753017356284773167)
      ·
        refine ⟨4555388629526034427159751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036925753017356284773167 4555388629526034427159751)
        ·
          refine ⟨6833082944289051640739627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555388629526034427159751 6833082944289051640739627)
          ·
            refine ⟨10249624416433577461109441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833082944289051640739627 10249624416433577461109441)
            ·
              refine ⟨7687218312325183095832081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10249624416433577461109441 7687218312325183095832081)
              ·
                refine ⟨5765413734243887321874061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7687218312325183095832081 5765413734243887321874061)
                ·
                  refine ⟨2162030150341457745702773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5765413734243887321874061 2162030150341457745702773)
                  ·
                    refine ⟨202690326594511663659635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2162030150341457745702773 202690326594511663659635)
                    ·
                      rfl

theorem cell23_1184214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1184214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184214 prefixEnd_1184214 := by exact prefixLift 1184214
  have htrace : WordTrace (prefixWord ++ tailWord_1184214) baseStart_1184214 baseEnd_1184214 := by
    simpa [prefixWord, tailWord_1184214, baseEnd_1184214] using wordTrace_append hprefix tailTrace_1184214
  have hstable : (prefixWord ++ tailWord_1184214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184214).length < 2 ^ (prefixWord ++ tailWord_1184214).sum := by decide
  have hdescent : baseEnd_1184214 < baseStart_1184214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184217 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_1184217 : Nat := 118140960795 + 1184217 * 2 ^ 59
def prefixEnd_1184217 : Nat := 4983230072969 + 3 ^ 40 * 1184217 * 2
def baseEnd_1184217 : Nat := 608072520225498479241391

theorem tailTrace_1184217 : CollatzResearch.WordTrace tailWord_1184217 prefixEnd_1184217 608072520225498479241391 := by
  unfold tailWord_1184217
  simp only [CollatzResearch.WordTrace]
  refine ⟨43191942350791532006910905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28794628233861021337940603 43191942350791532006910905)
  ·
    refine ⟨32393956763093649005183179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43191942350791532006910905 32393956763093649005183179)
    ·
      refine ⟨48590935144640473507774769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32393956763093649005183179 48590935144640473507774769)
      ·
        refine ⟨36443201358480355130831077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48590935144640473507774769 36443201358480355130831077)
        ·
          refine ⟨6833100254715066587030827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36443201358480355130831077 6833100254715066587030827)
          ·
            refine ⟨10249650382072599880546241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833100254715066587030827 10249650382072599880546241)
            ·
              refine ⟨7687237786554449910409681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10249650382072599880546241 7687237786554449910409681)
              ·
                refine ⟨5765428339915837432807261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7687237786554449910409681 5765428339915837432807261)
                ·
                  refine ⟨2162035627468439037302723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5765428339915837432807261 2162035627468439037302723)
                  ·
                    refine ⟨3243053441202658555954085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2162035627468439037302723 3243053441202658555954085)
                    ·
                      refine ⟨608072520225498479241391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3243053441202658555954085 608072520225498479241391)
                      ·
                        rfl

theorem cell23_1184217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_1184217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184217 prefixEnd_1184217 := by exact prefixLift 1184217
  have htrace : WordTrace (prefixWord ++ tailWord_1184217) baseStart_1184217 baseEnd_1184217 := by
    simpa [prefixWord, tailWord_1184217, baseEnd_1184217] using wordTrace_append hprefix tailTrace_1184217
  have hstable : (prefixWord ++ tailWord_1184217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184217).length < 2 ^ (prefixWord ++ tailWord_1184217).sum := by decide
  have hdescent : baseEnd_1184217 < baseStart_1184217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184234 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1184234 : Nat := 118140960795 + 1184234 * 2 ^ 59
def prefixEnd_1184234 : Nat := 4983230072969 + 3 ^ 40 * 1184234 * 2
def baseEnd_1184234 : Nat := 608081249396624912728813

theorem tailTrace_1184234 : CollatzResearch.WordTrace tailWord_1184234 prefixEnd_1184234 608081249396624912728813 := by
  unfold tailWord_1184234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10798140597932485977569939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28795041594486629273519837 10798140597932485977569939)
  ·
    refine ⟨16197210896898728966354909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10798140597932485977569939 16197210896898728966354909)
    ·
      refine ⟨6073954086337023362383091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16197210896898728966354909 6073954086337023362383091)
      ·
        refine ⟨9110931129505535043574637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073954086337023362383091 9110931129505535043574637)
        ·
          refine ⟨3416599173564575641340489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9110931129505535043574637 3416599173564575641340489)
          ·
            refine ⟨2562449380173431731005367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416599173564575641340489 2562449380173431731005367)
            ·
              refine ⟨3843674070260147596508051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562449380173431731005367 3843674070260147596508051)
              ·
                refine ⟨5765511105390221394762077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3843674070260147596508051 5765511105390221394762077)
                ·
                  refine ⟨2162066664521333023035779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5765511105390221394762077 2162066664521333023035779)
                  ·
                    refine ⟨3243099996781999534553669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2162066664521333023035779 3243099996781999534553669)
                    ·
                      refine ⟨608081249396624912728813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3243099996781999534553669 608081249396624912728813)
                      ·
                        rfl

theorem cell23_1184234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1184234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184234 prefixEnd_1184234 := by exact prefixLift 1184234
  have htrace : WordTrace (prefixWord ++ tailWord_1184234) baseStart_1184234 baseEnd_1184234 := by
    simpa [prefixWord, tailWord_1184234, baseEnd_1184234] using wordTrace_append hprefix tailTrace_1184234
  have hstable : (prefixWord ++ tailWord_1184234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184234).length < 2 ^ (prefixWord ++ tailWord_1184234).sum := by decide
  have hdescent : baseEnd_1184234 < baseStart_1184234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184240 : List Nat := [2, 1, 1, 1, 3, 3, 1, 11]
def baseStart_1184240 : Nat := 118140960795 + 1184240 * 2 ^ 59
def prefixEnd_1184240 : Nat := 4983230072969 + 3 ^ 40 * 1184240 * 2
def baseEnd_1184240 : Nat := 22521641862242662564955

theorem tailTrace_1184240 : CollatzResearch.WordTrace tailWord_1184240 prefixEnd_1184240 22521641862242662564955 := by
  unfold tailWord_1184240
  simp only [CollatzResearch.WordTrace]
  refine ⟨21596390614854103467499087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28795187486472137956665449 21596390614854103467499087)
  ·
    refine ⟨32394585922281155201248631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21596390614854103467499087 32394585922281155201248631)
    ·
      refine ⟨48591878883421732801872947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32394585922281155201248631 48591878883421732801872947)
      ·
        refine ⟨72887818325132599202809421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48591878883421732801872947 72887818325132599202809421)
        ·
          refine ⟨27332931871924724701053533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72887818325132599202809421 27332931871924724701053533)
          ·
            refine ⟨10249849451971771762895075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27332931871924724701053533 10249849451971771762895075)
            ·
              refine ⟨15374774177957657644342613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10249849451971771762895075 15374774177957657644342613)
              ·
                refine ⟨22521641862242662564955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 15374774177957657644342613 22521641862242662564955)
                ·
                  rfl

theorem cell23_1184240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 11].length) (baseStart_1184240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184240 prefixEnd_1184240 := by exact prefixLift 1184240
  have htrace : WordTrace (prefixWord ++ tailWord_1184240) baseStart_1184240 baseEnd_1184240 := by
    simpa [prefixWord, tailWord_1184240, baseEnd_1184240] using wordTrace_append hprefix tailTrace_1184240
  have hstable : (prefixWord ++ tailWord_1184240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184240).length < 2 ^ (prefixWord ++ tailWord_1184240).sum := by decide
  have hdescent : baseEnd_1184240 < baseStart_1184240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184284 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1184284 : Nat := 118140960795 + 1184284 * 2 ^ 59
def prefixEnd_1184284 : Nat := 4983230072969 + 3 ^ 40 * 1184284 * 2
def baseEnd_1184284 : Nat := 608106923429349717103583

theorem tailTrace_1184284 : CollatzResearch.WordTrace tailWord_1184284 prefixEnd_1184284 608106923429349717103583 := by
  unfold tailWord_1184284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21597193020774401224799953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28796257361032534966399937 21597193020774401224799953)
  ·
    refine ⟨16197894765580800918599965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21597193020774401224799953 16197894765580800918599965)
    ·
      refine ⟨6074210537092800344474987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16197894765580800918599965 6074210537092800344474987)
      ·
        refine ⟨9111315805639200516712481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6074210537092800344474987 9111315805639200516712481)
        ·
          refine ⟨6833486854229400387534361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9111315805639200516712481 6833486854229400387534361)
          ·
            refine ⟨5125115140672050290650771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6833486854229400387534361 5125115140672050290650771)
            ·
              refine ⟨7687672711008075435976157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125115140672050290650771 7687672711008075435976157)
              ·
                refine ⟨2882877266628028288491059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7687672711008075435976157 2882877266628028288491059)
                ·
                  refine ⟨4324315899942042432736589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882877266628028288491059 4324315899942042432736589)
                  ·
                    refine ⟨1621618462478265912276221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4324315899942042432736589 1621618462478265912276221)
                    ·
                      refine ⟨608106923429349717103583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621618462478265912276221 608106923429349717103583)
                      ·
                        rfl

theorem cell23_1184284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1184284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184284 prefixEnd_1184284 := by exact prefixLift 1184284
  have htrace : WordTrace (prefixWord ++ tailWord_1184284) baseStart_1184284 baseEnd_1184284 := by
    simpa [prefixWord, tailWord_1184284, baseEnd_1184284] using wordTrace_append hprefix tailTrace_1184284
  have hstable : (prefixWord ++ tailWord_1184284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184284).length < 2 ^ (prefixWord ++ tailWord_1184284).sum := by decide
  have hdescent : baseEnd_1184284 < baseStart_1184284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184302 : List Nat := [4, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_1184302 : Nat := 118140960795 + 1184302 * 2 ^ 59
def prefixEnd_1184302 : Nat := 4983230072969 + 3 ^ 40 * 1184302 * 2
def baseEnd_1184302 : Nat := 608116166081130646678501

theorem tailTrace_1184302 : CollatzResearch.WordTrace tailWord_1184302 prefixEnd_1184302 608116166081130646678501 := by
  unfold tailWord_1184302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399380319435448940469395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28796695036989061015836773 5399380319435448940469395)
  ·
    refine ⟨8099070479153173410704093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5399380319435448940469395 8099070479153173410704093)
    ·
      refine ⟨3037151429682440029014035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8099070479153173410704093 3037151429682440029014035)
      ·
        refine ⟨4555727144523660043521053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037151429682440029014035 4555727144523660043521053)
        ·
          refine ⟨1708397679196372516320395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4555727144523660043521053 1708397679196372516320395)
          ·
            refine ⟨2562596518794558774480593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708397679196372516320395 2562596518794558774480593)
            ·
              refine ⟨1921947389095919080860445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2562596518794558774480593 1921947389095919080860445)
              ·
                refine ⟨720730270910969655322667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1921947389095919080860445 720730270910969655322667)
                ·
                  refine ⟨1081095406366454482984001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720730270910969655322667 1081095406366454482984001)
                  ·
                    refine ⟨810821554774840862238001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1081095406366454482984001 810821554774840862238001)
                    ·
                      refine ⟨608116166081130646678501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810821554774840862238001 608116166081130646678501)
                      ·
                        rfl

theorem cell23_1184302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_1184302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184302 prefixEnd_1184302 := by exact prefixLift 1184302
  have htrace : WordTrace (prefixWord ++ tailWord_1184302) baseStart_1184302 baseEnd_1184302 := by
    simpa [prefixWord, tailWord_1184302, baseEnd_1184302] using wordTrace_append hprefix tailTrace_1184302
  have hstable : (prefixWord ++ tailWord_1184302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184302).length < 2 ^ (prefixWord ++ tailWord_1184302).sum := by decide
  have hdescent : baseEnd_1184302 < baseStart_1184302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184311 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 1, 3, 2]
def baseStart_1184311 : Nat := 118140960795 + 1184311 * 2 ^ 59
def prefixEnd_1184311 : Nat := 4983230072969 + 3 ^ 40 * 1184311 * 2
def baseEnd_1184311 : Nat := 608120787407021111465959

theorem tailTrace_1184311 : CollatzResearch.WordTrace tailWord_1184311 prefixEnd_1184311 608120787407021111465959 := by
  unfold tailWord_1184311
  simp only [CollatzResearch.WordTrace]
  refine ⟨43195370812450986060832787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28796913874967324040555191 43195370812450986060832787)
  ·
    refine ⟨64793056218676479091249181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43195370812450986060832787 64793056218676479091249181)
    ·
      refine ⟨24297396082003679659218443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64793056218676479091249181 24297396082003679659218443)
      ·
        refine ⟨36446094123005519488827665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24297396082003679659218443 36446094123005519488827665)
        ·
          refine ⟨27334570592254139616620749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36446094123005519488827665 27334570592254139616620749)
          ·
            refine ⟨10250463972095302356232781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27334570592254139616620749 10250463972095302356232781)
            ·
              refine ⟨3843923989535738383587293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10250463972095302356232781 3843923989535738383587293)
              ·
                refine ⟨1441471496075901893845235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3843923989535738383587293 1441471496075901893845235)
                ·
                  refine ⟨2162207244113852840767853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441471496075901893845235 2162207244113852840767853)
                  ·
                    refine ⟨810827716542694815287945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162207244113852840767853 810827716542694815287945)
                    ·
                      refine ⟨608120787407021111465959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810827716542694815287945 608120787407021111465959)
                      ·
                        rfl

theorem cell23_1184311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_1184311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184311 prefixEnd_1184311 := by exact prefixLift 1184311
  have htrace : WordTrace (prefixWord ++ tailWord_1184311) baseStart_1184311 baseEnd_1184311 := by
    simpa [prefixWord, tailWord_1184311, baseEnd_1184311] using wordTrace_append hprefix tailTrace_1184311
  have hstable : (prefixWord ++ tailWord_1184311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184311).length < 2 ^ (prefixWord ++ tailWord_1184311).sum := by decide
  have hdescent : baseEnd_1184311 < baseStart_1184311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184341 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1184341 : Nat := 118140960795 + 1184341 * 2 ^ 59
def prefixEnd_1184341 : Nat := 4983230072969 + 3 ^ 40 * 1184341 * 2
def baseEnd_1184341 : Nat := 608136191826655994090821

theorem tailTrace_1184341 : CollatzResearch.WordTrace tailWord_1184341 prefixEnd_1184341 608136191826655994090821 := by
  unfold tailWord_1184341
  simp only [CollatzResearch.WordTrace]
  refine ⟨43196465002342301184424877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28797643334894867456283251 43196465002342301184424877)
  ·
    refine ⟨16198674375878362944159329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43196465002342301184424877 16198674375878362944159329)
    ·
      refine ⟨12149005781908772208119497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16198674375878362944159329 12149005781908772208119497)
      ·
        refine ⟨9111754336431579156089623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12149005781908772208119497 9111754336431579156089623)
        ·
          refine ⟨13667631504647368734134435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9111754336431579156089623 13667631504647368734134435)
          ·
            refine ⟨20501447256971053101201653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13667631504647368734134435 20501447256971053101201653)
            ·
              refine ⟨1922010680341036228237655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20501447256971053101201653 1922010680341036228237655)
              ·
                refine ⟨2883016020511554342356483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922010680341036228237655 2883016020511554342356483)
                ·
                  refine ⟨4324524030767331513534725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883016020511554342356483 4324524030767331513534725)
                  ·
                    refine ⟨810848255768874658787761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4324524030767331513534725 810848255768874658787761)
                    ·
                      refine ⟨608136191826655994090821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810848255768874658787761 608136191826655994090821)
                      ·
                        rfl

theorem cell23_1184341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1184341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184341 prefixEnd_1184341 := by exact prefixLift 1184341
  have htrace : WordTrace (prefixWord ++ tailWord_1184341) baseStart_1184341 baseEnd_1184341 := by
    simpa [prefixWord, tailWord_1184341, baseEnd_1184341] using wordTrace_append hprefix tailTrace_1184341
  have hstable : (prefixWord ++ tailWord_1184341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184341).length < 2 ^ (prefixWord ++ tailWord_1184341).sum := by decide
  have hdescent : baseEnd_1184341 < baseStart_1184341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184381 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 7]
def baseStart_1184381 : Nat := 118140960795 + 1184381 * 2 ^ 59
def prefixEnd_1184381 : Nat := 4983230072969 + 3 ^ 40 * 1184381 * 2
def baseEnd_1184381 : Nat := 67572970116981759732293

theorem tailTrace_1184381 : CollatzResearch.WordTrace tailWord_1184381 prefixEnd_1184381 67572970116981759732293 := by
  unfold tailWord_1184381
  simp only [CollatzResearch.WordTrace]
  refine ⟨43197923922197388015880997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28798615948131592010587331 43197923922197388015880997)
  ·
    refine ⟨8099610735412010252977687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43197923922197388015880997 8099610735412010252977687)
    ·
      refine ⟨12149416103118015379466531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099610735412010252977687 12149416103118015379466531)
      ·
        refine ⟨18224124154677023069199797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12149416103118015379466531 18224124154677023069199797)
        ·
          refine ⟨1708511639500970912737481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18224124154677023069199797 1708511639500970912737481)
          ·
            refine ⟨1281383729625728184553111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1708511639500970912737481 1281383729625728184553111)
            ·
              refine ⟨1922075594438592276829667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281383729625728184553111 1922075594438592276829667)
              ·
                refine ⟨2883113391657888415244501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922075594438592276829667 2883113391657888415244501)
                ·
                  refine ⟨67572970116981759732293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2883113391657888415244501 67572970116981759732293)
                  ·
                    rfl

theorem cell23_1184381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_1184381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184381 prefixEnd_1184381 := by exact prefixLift 1184381
  have htrace : WordTrace (prefixWord ++ tailWord_1184381) baseStart_1184381 baseEnd_1184381 := by
    simpa [prefixWord, tailWord_1184381, baseEnd_1184381] using wordTrace_append hprefix tailTrace_1184381
  have hstable : (prefixWord ++ tailWord_1184381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184381).length < 2 ^ (prefixWord ++ tailWord_1184381).sum := by decide
  have hdescent : baseEnd_1184381 < baseStart_1184381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184386 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1184386 : Nat := 118140960795 + 1184386 * 2 ^ 59
def prefixEnd_1184386 : Nat := 4983230072969 + 3 ^ 40 * 1184386 * 2
def baseEnd_1184386 : Nat := 608159298456108318028115

theorem tailTrace_1184386 : CollatzResearch.WordTrace tailWord_1184386 prefixEnd_1184386 608159298456108318028115 := by
  unfold tailWord_1184386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10799526571794818467453253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28798737524786182579875341 10799526571794818467453253)
  ·
    refine ⟨2024911232211528462647485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10799526571794818467453253 2024911232211528462647485)
    ·
      refine ⟨759341712079323173492807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2024911232211528462647485 759341712079323173492807)
      ·
        refine ⟨1139012568118984760239211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759341712079323173492807 1139012568118984760239211)
        ·
          refine ⟨1708518852178477140358817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139012568118984760239211 1708518852178477140358817)
          ·
            refine ⟨1281389139133857855269113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1708518852178477140358817 1281389139133857855269113)
            ·
              refine ⟨961041854350393391451835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281389139133857855269113 961041854350393391451835)
              ·
                refine ⟨1441562781525590087177753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961041854350393391451835 1441562781525590087177753)
                ·
                  refine ⟨1081172086144192565383315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441562781525590087177753 1081172086144192565383315)
                  ·
                    refine ⟨1621758129216288848074973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081172086144192565383315 1621758129216288848074973)
                    ·
                      refine ⟨608159298456108318028115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621758129216288848074973 608159298456108318028115)
                      ·
                        rfl

theorem cell23_1184386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1184386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184386 prefixEnd_1184386 := by exact prefixLift 1184386
  have htrace : WordTrace (prefixWord ++ tailWord_1184386) baseStart_1184386 baseEnd_1184386 := by
    simpa [prefixWord, tailWord_1184386, baseEnd_1184386] using wordTrace_append hprefix tailTrace_1184386
  have hstable : (prefixWord ++ tailWord_1184386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184386).length < 2 ^ (prefixWord ++ tailWord_1184386).sum := by decide
  have hdescent : baseEnd_1184386 < baseStart_1184386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184387 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_1184387 : Nat := 118140960795 + 1184387 * 2 ^ 59
def prefixEnd_1184387 : Nat := 4983230072969 + 3 ^ 40 * 1184387 * 2
def baseEnd_1184387 : Nat := 608159811936762814115609

theorem tailTrace_1184387 : CollatzResearch.WordTrace tailWord_1184387 prefixEnd_1184387 608159811936762814115609 := by
  unfold tailWord_1184387
  simp only [CollatzResearch.WordTrace]
  refine ⟨43198142760175651040599415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28798761840117100693732943 43198142760175651040599415)
  ·
    refine ⟨64797214140263476560899123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43198142760175651040599415 64797214140263476560899123)
    ·
      refine ⟨97195821210395214841348685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64797214140263476560899123 97195821210395214841348685)
      ·
        refine ⟨36448432953898205565505757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97195821210395214841348685 36448432953898205565505757)
        ·
          refine ⟨13668162357711827087064659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36448432953898205565505757 13668162357711827087064659)
          ·
            refine ⟨20502243536567740630596989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13668162357711827087064659 20502243536567740630596989)
            ·
              refine ⟨7688341326212902736473871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20502243536567740630596989 7688341326212902736473871)
              ·
                refine ⟨11532511989319354104710807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7688341326212902736473871 11532511989319354104710807)
                ·
                  refine ⟨17298767983979031157066211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11532511989319354104710807 17298767983979031157066211)
                  ·
                    refine ⟨25948151975968546735599317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17298767983979031157066211 25948151975968546735599317)
                    ·
                      refine ⟨608159811936762814115609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25948151975968546735599317 608159811936762814115609)
                      ·
                        rfl

theorem cell23_1184387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_1184387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184387 prefixEnd_1184387 := by exact prefixLift 1184387
  have htrace : WordTrace (prefixWord ++ tailWord_1184387) baseStart_1184387 baseEnd_1184387 := by
    simpa [prefixWord, tailWord_1184387, baseEnd_1184387] using wordTrace_append hprefix tailTrace_1184387
  have hstable : (prefixWord ++ tailWord_1184387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184387).length < 2 ^ (prefixWord ++ tailWord_1184387).sum := by decide
  have hdescent : baseEnd_1184387 < baseStart_1184387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184434 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1184434 : Nat := 118140960795 + 1184434 * 2 ^ 59
def prefixEnd_1184434 : Nat := 4983230072969 + 3 ^ 40 * 1184434 * 2
def baseEnd_1184434 : Nat := 608183945527524130227893

theorem tailTrace_1184434 : CollatzResearch.WordTrace tailWord_1184434 prefixEnd_1184434 608183945527524130227893 := by
  unfold tailWord_1184434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10799964247751344516890089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28799904660670252045040237 10799964247751344516890089)
  ·
    refine ⟨8099973185813508387667567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10799964247751344516890089 8099973185813508387667567)
    ·
      refine ⟨12149959778720262581501351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099973185813508387667567 12149959778720262581501351)
      ·
        refine ⟨18224939668080393872252027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12149959778720262581501351 18224939668080393872252027)
        ·
          refine ⟨27337409502120590808378041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18224939668080393872252027 27337409502120590808378041)
          ·
            refine ⟨20503057126590443106283531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27337409502120590808378041 20503057126590443106283531)
            ·
              refine ⟨30754585689885664659425297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20503057126590443106283531 30754585689885664659425297)
              ·
                refine ⟨23065939267414248494568973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30754585689885664659425297 23065939267414248494568973)
                ·
                  refine ⟨8649727225280343185463365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23065939267414248494568973 8649727225280343185463365)
                  ·
                    refine ⟨1621823854740064347274381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8649727225280343185463365 1621823854740064347274381)
                    ·
                      refine ⟨608183945527524130227893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621823854740064347274381 608183945527524130227893)
                      ·
                        rfl

theorem cell23_1184434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1184434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184434 prefixEnd_1184434 := by exact prefixLift 1184434
  have htrace : WordTrace (prefixWord ++ tailWord_1184434) baseStart_1184434 baseEnd_1184434 := by
    simpa [prefixWord, tailWord_1184434, baseEnd_1184434] using wordTrace_append hprefix tailTrace_1184434
  have hstable : (prefixWord ++ tailWord_1184434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184434).length < 2 ^ (prefixWord ++ tailWord_1184434).sum := by decide
  have hdescent : baseEnd_1184434 < baseStart_1184434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184468 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1184468 : Nat := 118140960795 + 1184468 * 2 ^ 59
def prefixEnd_1184468 : Nat := 4983230072969 + 3 ^ 40 * 1184468 * 2
def baseEnd_1184468 : Nat := 608201403869776997202737

theorem tailTrace_1184468 : CollatzResearch.WordTrace tailWord_1184468 prefixEnd_1184468 608201403869776997202737 := by
  unfold tailWord_1184468
  simp only [CollatzResearch.WordTrace]
  refine ⟨21600548536441100937149029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28800731381921467916198705 21600548536441100937149029)
  ·
    refine ⟨4050102850582706425715443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21600548536441100937149029 4050102850582706425715443)
    ·
      refine ⟨6075154275874059638573165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050102850582706425715443 6075154275874059638573165)
      ·
        refine ⟨2278182853452772364464937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6075154275874059638573165 2278182853452772364464937)
        ·
          refine ⟨1708637140089579273348703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2278182853452772364464937 1708637140089579273348703)
          ·
            refine ⟨2562955710134368910023055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708637140089579273348703 2562955710134368910023055)
            ·
              refine ⟨3844433565201553365034583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562955710134368910023055 3844433565201553365034583)
              ·
                refine ⟨5766650347802330047551875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844433565201553365034583 5766650347802330047551875)
                ·
                  refine ⟨8649975521703495071327813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766650347802330047551875 8649975521703495071327813)
                  ·
                    refine ⟨1621870410319405325873965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8649975521703495071327813 1621870410319405325873965)
                    ·
                      refine ⟨608201403869776997202737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621870410319405325873965 608201403869776997202737)
                      ·
                        rfl

theorem cell23_1184468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1184468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184468 prefixEnd_1184468 := by exact prefixLift 1184468
  have htrace : WordTrace (prefixWord ++ tailWord_1184468) baseStart_1184468 baseEnd_1184468 := by
    simpa [prefixWord, tailWord_1184468, baseEnd_1184468] using wordTrace_append hprefix tailTrace_1184468
  have hstable : (prefixWord ++ tailWord_1184468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184468).length < 2 ^ (prefixWord ++ tailWord_1184468).sum := by decide
  have hdescent : baseEnd_1184468 < baseStart_1184468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184488 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 6]
def baseStart_1184488 : Nat := 118140960795 + 1184488 * 2 ^ 59
def prefixEnd_1184488 : Nat := 4983230072969 + 3 ^ 40 * 1184488 * 2
def baseEnd_1184488 : Nat := 67579074831429657661405

theorem tailTrace_1184488 : CollatzResearch.WordTrace tailWord_1184488 prefixEnd_1184488 67579074831429657661405 := by
  unfold tailWord_1184488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21600913266404872645013059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28801217688539830193350745 21600913266404872645013059)
  ·
    refine ⟨32401369899607308967519589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21600913266404872645013059 32401369899607308967519589)
    ·
      refine ⟨6075256856176370431409923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32401369899607308967519589 6075256856176370431409923)
      ·
        refine ⟨9112885284264555647114885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075256856176370431409923 9112885284264555647114885)
        ·
          refine ⟨1708665990799604183834041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9112885284264555647114885 1708665990799604183834041)
          ·
            refine ⟨1281499493099703137875531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1708665990799604183834041 1281499493099703137875531)
            ·
              refine ⟨1922249239649554706813297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281499493099703137875531 1922249239649554706813297)
              ·
                refine ⟨1441686929737166030109973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922249239649554706813297 1441686929737166030109973)
                ·
                  refine ⟨67579074831429657661405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1441686929737166030109973 67579074831429657661405)
                  ·
                    rfl

theorem cell23_1184488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 6].length) (baseStart_1184488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184488 prefixEnd_1184488 := by exact prefixLift 1184488
  have htrace : WordTrace (prefixWord ++ tailWord_1184488) baseStart_1184488 baseEnd_1184488 := by
    simpa [prefixWord, tailWord_1184488, baseEnd_1184488] using wordTrace_append hprefix tailTrace_1184488
  have hstable : (prefixWord ++ tailWord_1184488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184488).length < 2 ^ (prefixWord ++ tailWord_1184488).sum := by decide
  have hdescent : baseEnd_1184488 < baseStart_1184488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184491 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 4, 3, 2]
def baseStart_1184491 : Nat := 118140960795 + 1184491 * 2 ^ 59
def prefixEnd_1184491 : Nat := 4983230072969 + 3 ^ 40 * 1184491 * 2
def baseEnd_1184491 : Nat := 608213213924830407215131

theorem tailTrace_1184491 : CollatzResearch.WordTrace tailWord_1184491 prefixEnd_1184491 608213213924830407215131 := by
  unfold tailWord_1184491
  simp only [CollatzResearch.WordTrace]
  refine ⟨43201935951798876802385327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28801290634532584534923551 43201935951798876802385327)
  ·
    refine ⟨64802903927698315203577991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43201935951798876802385327 64802903927698315203577991)
    ·
      refine ⟨97204355891547472805366987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64802903927698315203577991 97204355891547472805366987)
      ·
        refine ⟨145806533837321209208050481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97204355891547472805366987 145806533837321209208050481)
        ·
          refine ⟨109354900377990906906037861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145806533837321209208050481 109354900377990906906037861)
          ·
            refine ⟨20504043820873295044882099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109354900377990906906037861 20504043820873295044882099)
            ·
              refine ⟨30756065731309942567323149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20504043820873295044882099 30756065731309942567323149)
              ·
                refine ⟨11533524649241228462746181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30756065731309942567323149 11533524649241228462746181)
                ·
                  refine ⟨2162535871732730336764909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11533524649241228462746181 2162535871732730336764909)
                  ·
                    refine ⟨810950951899773876286841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2162535871732730336764909 810950951899773876286841)
                    ·
                      refine ⟨608213213924830407215131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810950951899773876286841 608213213924830407215131)
                      ·
                        rfl

theorem cell23_1184491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3, 2].length) (baseStart_1184491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184491 prefixEnd_1184491 := by exact prefixLift 1184491
  have htrace : WordTrace (prefixWord ++ tailWord_1184491) baseStart_1184491 baseEnd_1184491 := by
    simpa [prefixWord, tailWord_1184491, baseEnd_1184491] using wordTrace_append hprefix tailTrace_1184491
  have hstable : (prefixWord ++ tailWord_1184491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184491).length < 2 ^ (prefixWord ++ tailWord_1184491).sum := by decide
  have hdescent : baseEnd_1184491 < baseStart_1184491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184498 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1184498 : Nat := 118140960795 + 1184498 * 2 ^ 59
def prefixEnd_1184498 : Nat := 4983230072969 + 3 ^ 40 * 1184498 * 2
def baseEnd_1184498 : Nat := 608216808289411879827599

theorem tailTrace_1184498 : CollatzResearch.WordTrace tailWord_1184498 prefixEnd_1184498 608216808289411879827599 := by
  unfold tailWord_1184498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800547815693379249472537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28801460841849011331926765 10800547815693379249472537)
  ·
    refine ⟨8100410861770034437104403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10800547815693379249472537 8100410861770034437104403)
    ·
      refine ⟨12150616292655051655656605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8100410861770034437104403 12150616292655051655656605)
      ·
        refine ⟨4556481109745644370871227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12150616292655051655656605 4556481109745644370871227)
        ·
          refine ⟨6834721664618466556306841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556481109745644370871227 6834721664618466556306841)
          ·
            refine ⟨5126041248463849917230131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6834721664618466556306841 5126041248463849917230131)
            ·
              refine ⟨7689061872695774875845197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126041248463849917230131 7689061872695774875845197)
              ·
                refine ⟨2883398202260915578441949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7689061872695774875845197 2883398202260915578441949)
                ·
                  refine ⟨1081274325847843341915731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2883398202260915578441949 1081274325847843341915731)
                  ·
                    refine ⟨1621911488771765012873597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081274325847843341915731 1621911488771765012873597)
                    ·
                      refine ⟨608216808289411879827599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621911488771765012873597 608216808289411879827599)
                      ·
                        rfl

theorem cell23_1184498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1184498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184498 prefixEnd_1184498 := by exact prefixLift 1184498
  have htrace : WordTrace (prefixWord ++ tailWord_1184498) baseStart_1184498 baseEnd_1184498 := by
    simpa [prefixWord, tailWord_1184498, baseEnd_1184498] using wordTrace_append hprefix tailTrace_1184498
  have hstable : (prefixWord ++ tailWord_1184498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184498).length < 2 ^ (prefixWord ++ tailWord_1184498).sum := by decide
  have hdescent : baseEnd_1184498 < baseStart_1184498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184521 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 4]
def baseStart_1184521 : Nat := 118140960795 + 1184521 * 2 ^ 59
def prefixEnd_1184521 : Nat := 4983230072969 + 3 ^ 40 * 1184521 * 2
def baseEnd_1184521 : Nat := 608228618344465289839993

theorem tailTrace_1184521 : CollatzResearch.WordTrace tailWord_1184521 prefixEnd_1184521 608228618344465289839993 := by
  unfold tailWord_1184521
  simp only [CollatzResearch.WordTrace]
  refine ⟨43203030141690191925977417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28802020094460127950651611 43203030141690191925977417)
  ·
    refine ⟨32402272606267643944483063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43203030141690191925977417 32402272606267643944483063)
    ·
      refine ⟨48603408909401465916724595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32402272606267643944483063 48603408909401465916724595)
      ·
        refine ⟨72905113364102198875086893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48603408909401465916724595 72905113364102198875086893)
        ·
          refine ⟨27339417511538324578157585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72905113364102198875086893 27339417511538324578157585)
          ·
            refine ⟨20504563133653743433618189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27339417511538324578157585 20504563133653743433618189)
            ·
              refine ⟨7689211175120153787606821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20504563133653743433618189 7689211175120153787606821)
              ·
                refine ⟨1441727095335028835176279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7689211175120153787606821 1441727095335028835176279)
                ·
                  refine ⟨2162590643002543252764419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441727095335028835176279 2162590643002543252764419)
                  ·
                    refine ⟨3243885964503814879146629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2162590643002543252764419 3243885964503814879146629)
                    ·
                      refine ⟨608228618344465289839993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3243885964503814879146629 608228618344465289839993)
                      ·
                        rfl

theorem cell23_1184521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_1184521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184521 prefixEnd_1184521 := by exact prefixLift 1184521
  have htrace : WordTrace (prefixWord ++ tailWord_1184521) baseStart_1184521 baseEnd_1184521 := by
    simpa [prefixWord, tailWord_1184521, baseEnd_1184521] using wordTrace_append hprefix tailTrace_1184521
  have hstable : (prefixWord ++ tailWord_1184521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184521).length < 2 ^ (prefixWord ++ tailWord_1184521).sum := by decide
  have hdescent : baseEnd_1184521 < baseStart_1184521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184524 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1184524 : Nat := 118140960795 + 1184524 * 2 ^ 59
def prefixEnd_1184524 : Nat := 4983230072969 + 3 ^ 40 * 1184524 * 2
def baseEnd_1184524 : Nat := 608230158786428778102479

theorem tailTrace_1184524 : CollatzResearch.WordTrace tailWord_1184524 prefixEnd_1184524 608230158786428778102479 := by
  unfold tailWord_1184524
  simp only [CollatzResearch.WordTrace]
  refine ⟨21601569780339661719168313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28802093040452882292224417 21601569780339661719168313)
  ·
    refine ⟨16201177335254746289376235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21601569780339661719168313 16201177335254746289376235)
    ·
      refine ⟨24301766002882119434064353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16201177335254746289376235 24301766002882119434064353)
      ·
        refine ⟨18226324502161589575548265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24301766002882119434064353 18226324502161589575548265)
        ·
          refine ⟨13669743376621192181661199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18226324502161589575548265 13669743376621192181661199)
          ·
            refine ⟨20504615064931788272491799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13669743376621192181661199 20504615064931788272491799)
            ·
              refine ⟨30756922597397682408737699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20504615064931788272491799 30756922597397682408737699)
              ·
                refine ⟨46135383896096523613106549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30756922597397682408737699 46135383896096523613106549)
                ·
                  refine ⟨4325192240259049088728739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46135383896096523613106549 4325192240259049088728739)
                  ·
                    refine ⟨6487788360388573633093109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4325192240259049088728739 6487788360388573633093109)
                    ·
                      refine ⟨608230158786428778102479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6487788360388573633093109 608230158786428778102479)
                      ·
                        rfl

theorem cell23_1184524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1184524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184524 prefixEnd_1184524 := by exact prefixLift 1184524
  have htrace : WordTrace (prefixWord ++ tailWord_1184524) baseStart_1184524 baseEnd_1184524 := by
    simpa [prefixWord, tailWord_1184524, baseEnd_1184524] using wordTrace_append hprefix tailTrace_1184524
  have hstable : (prefixWord ++ tailWord_1184524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184524).length < 2 ^ (prefixWord ++ tailWord_1184524).sum := by decide
  have hdescent : baseEnd_1184524 < baseStart_1184524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184544 : List Nat := [2, 1, 1, 5, 1, 2, 11]
def baseStart_1184544 : Nat := 118140960795 + 1184544 * 2 ^ 59
def prefixEnd_1184544 : Nat := 4983230072969 + 3 ^ 40 * 1184544 * 2
def baseEnd_1184544 : Nat := 7509141091352082714227

theorem tailTrace_1184544 : CollatzResearch.WordTrace tailWord_1184544 prefixEnd_1184544 7509141091352082714227 := by
  unfold tailWord_1184544
  simp only [CollatzResearch.WordTrace]
  refine ⟨21601934510303433427032343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28802579347071244569376457 21601934510303433427032343)
  ·
    refine ⟨32402901765455150140548515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21601934510303433427032343 32402901765455150140548515)
    ·
      refine ⟨48604352648182725210822773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32402901765455150140548515 48604352648182725210822773)
      ·
        refine ⟨4556658060767130488514635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48604352648182725210822773 4556658060767130488514635)
        ·
          refine ⟨6834987091150695732771953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556658060767130488514635 6834987091150695732771953)
          ·
            refine ⟨5126240318363021799578965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6834987091150695732771953 5126240318363021799578965)
            ·
              refine ⟨7509141091352082714227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5126240318363021799578965 7509141091352082714227)
              ·
                rfl

theorem cell23_1184544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 11].length) (baseStart_1184544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184544 prefixEnd_1184544 := by exact prefixLift 1184544
  have htrace : WordTrace (prefixWord ++ tailWord_1184544) baseStart_1184544 baseEnd_1184544 := by
    simpa [prefixWord, tailWord_1184544, baseEnd_1184544] using wordTrace_append hprefix tailTrace_1184544
  have hstable : (prefixWord ++ tailWord_1184544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184544).length < 2 ^ (prefixWord ++ tailWord_1184544).sum := by decide
  have hdescent : baseEnd_1184544 < baseStart_1184544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184558 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1184558 : Nat := 118140960795 + 1184558 * 2 ^ 59
def prefixEnd_1184558 : Nat := 4983230072969 + 3 ^ 40 * 1184558 * 2
def baseEnd_1184558 : Nat := 608247617128681645077323

theorem tailTrace_1184558 : CollatzResearch.WordTrace tailWord_1184558 prefixEnd_1184558 608247617128681645077323 := by
  unfold tailWord_1184558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5400547455319518405634291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28802919761704098163382885 5400547455319518405634291)
  ·
    refine ⟨8100821182979277608451437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5400547455319518405634291 8100821182979277608451437)
    ·
      refine ⟨3037807943617229103169289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8100821182979277608451437 3037807943617229103169289)
      ·
        refine ⟨2278355957712921827376967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3037807943617229103169289 2278355957712921827376967)
        ·
          refine ⟨3417533936569382741065451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278355957712921827376967 3417533936569382741065451)
          ·
            refine ⟨5126300904854074111598177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417533936569382741065451 5126300904854074111598177)
            ·
              refine ⟨3844725678640555583698633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126300904854074111598177 3844725678640555583698633)
              ·
                refine ⟨2883544258980416687773975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844725678640555583698633 2883544258980416687773975)
                ·
                  refine ⟨4325316388470625031660963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883544258980416687773975 4325316388470625031660963)
                  ·
                    refine ⟨6487974582705937547491445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4325316388470625031660963 6487974582705937547491445)
                    ·
                      refine ⟨608247617128681645077323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6487974582705937547491445 608247617128681645077323)
                      ·
                        rfl

theorem cell23_1184558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1184558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184558 prefixEnd_1184558 := by exact prefixLift 1184558
  have htrace : WordTrace (prefixWord ++ tailWord_1184558) baseStart_1184558 baseEnd_1184558 := by
    simpa [prefixWord, tailWord_1184558, baseEnd_1184558] using wordTrace_append hprefix tailTrace_1184558
  have hstable : (prefixWord ++ tailWord_1184558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184558).length < 2 ^ (prefixWord ++ tailWord_1184558).sum := by decide
  have hdescent : baseEnd_1184558 < baseStart_1184558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184565 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1184565 : Nat := 118140960795 + 1184565 * 2 ^ 59
def prefixEnd_1184565 : Nat := 4983230072969 + 3 ^ 40 * 1184565 * 2
def baseEnd_1184565 : Nat := 202750403831087705896597

theorem tailTrace_1184565 : CollatzResearch.WordTrace tailWord_1184565 prefixEnd_1184565 202750403831087705896597 := by
  unfold tailWord_1184565
  simp only [CollatzResearch.WordTrace]
  refine ⟨43204634953530787440579149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28803089969020524960386099 43204634953530787440579149)
  ·
    refine ⟨16201738107574045290217181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43204634953530787440579149 16201738107574045290217181)
    ·
      refine ⟨6075651790340266983831443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16201738107574045290217181 6075651790340266983831443)
      ·
        refine ⟨9113477685510400475747165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075651790340266983831443 9113477685510400475747165)
        ·
          refine ⟨3417554132066400178405187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9113477685510400475747165 3417554132066400178405187)
          ·
            refine ⟨5126331198099600267607781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417554132066400178405187 5126331198099600267607781)
            ·
              refine ⟨961187099643675050176459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5126331198099600267607781 961187099643675050176459)
              ·
                refine ⟨1441780649465512575264689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961187099643675050176459 1441780649465512575264689)
                ·
                  refine ⟨1081335487099134431448517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1441780649465512575264689 1081335487099134431448517)
                  ·
                    refine ⟨202750403831087705896597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1081335487099134431448517 202750403831087705896597)
                    ·
                      rfl

theorem cell23_1184565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1184565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184565 prefixEnd_1184565 := by exact prefixLift 1184565
  have htrace : WordTrace (prefixWord ++ tailWord_1184565) baseStart_1184565 baseEnd_1184565 := by
    simpa [prefixWord, tailWord_1184565, baseEnd_1184565] using wordTrace_append hprefix tailTrace_1184565
  have hstable : (prefixWord ++ tailWord_1184565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184565).length < 2 ^ (prefixWord ++ tailWord_1184565).sum := by decide
  have hdescent : baseEnd_1184565 < baseStart_1184565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184575 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 3]
def baseStart_1184575 : Nat := 118140960795 + 1184575 * 2 ^ 59
def prefixEnd_1184575 : Nat := 4983230072969 + 3 ^ 40 * 1184575 * 2
def baseEnd_1184575 : Nat := 608256346299808078564745

theorem tailTrace_1184575 : CollatzResearch.WordTrace tailWord_1184575 prefixEnd_1184575 608256346299808078564745 := by
  unfold tailWord_1184575
  simp only [CollatzResearch.WordTrace]
  refine ⟨43204999683494559148443179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28803333122329706098962119 43204999683494559148443179)
  ·
    refine ⟨64807499525241838722664769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43204999683494559148443179 64807499525241838722664769)
    ·
      refine ⟨48605624643931379041998577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64807499525241838722664769 48605624643931379041998577)
      ·
        refine ⟨36454218482948534281498933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48605624643931379041998577 36454218482948534281498933)
        ·
          refine ⟨3417582982776425088890525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36454218482948534281498933 3417582982776425088890525)
          ·
            refine ⟨1281593618541159408333947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3417582982776425088890525 1281593618541159408333947)
            ·
              refine ⟨1922390427811739112500921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281593618541159408333947 1922390427811739112500921)
              ·
                refine ⟨1441792820858804334375691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922390427811739112500921 1441792820858804334375691)
                ·
                  refine ⟨2162689231288206501563537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441792820858804334375691 2162689231288206501563537)
                  ·
                    refine ⟨1622016923466154876172653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2162689231288206501563537 1622016923466154876172653)
                    ·
                      refine ⟨608256346299808078564745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1622016923466154876172653 608256346299808078564745)
                      ·
                        rfl

theorem cell23_1184575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_1184575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184575 prefixEnd_1184575 := by exact prefixLift 1184575
  have htrace : WordTrace (prefixWord ++ tailWord_1184575) baseStart_1184575 baseEnd_1184575 := by
    simpa [prefixWord, tailWord_1184575, baseEnd_1184575] using wordTrace_append hprefix tailTrace_1184575
  have hstable : (prefixWord ++ tailWord_1184575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184575).length < 2 ^ (prefixWord ++ tailWord_1184575).sum := by decide
  have hdescent : baseEnd_1184575 < baseStart_1184575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184588 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1184588 : Nat := 118140960795 + 1184588 * 2 ^ 59
def prefixEnd_1184588 : Nat := 4983230072969 + 3 ^ 40 * 1184588 * 2
def baseEnd_1184588 : Nat := 608263021548316527702185

theorem tailTrace_1184588 : CollatzResearch.WordTrace tailWord_1184588 prefixEnd_1184588 608263021548316527702185 := by
  unfold tailWord_1184588
  simp only [CollatzResearch.WordTrace]
  refine ⟨21602736916223731184333209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28803649221631641579110945 21602736916223731184333209)
  ·
    refine ⟨16202052687167798388249907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21602736916223731184333209 16202052687167798388249907)
    ·
      refine ⟨24303079030751697582374861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16202052687167798388249907 24303079030751697582374861)
      ·
        refine ⟨9113654636531886593390573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24303079030751697582374861 9113654636531886593390573)
        ·
          refine ⟨3417620488699457472521465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9113654636531886593390573 3417620488699457472521465)
          ·
            refine ⟨2563215366524593104391099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3417620488699457472521465 2563215366524593104391099)
            ·
              refine ⟨3844823049786889656586649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563215366524593104391099 3844823049786889656586649)
              ·
                refine ⟨2883617287340167242439987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844823049786889656586649 2883617287340167242439987)
                ·
                  refine ⟨4325425931010250863659981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883617287340167242439987 4325425931010250863659981)
                  ·
                    refine ⟨1622034724128844073872493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4325425931010250863659981 1622034724128844073872493)
                    ·
                      refine ⟨608263021548316527702185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1622034724128844073872493 608263021548316527702185)
                      ·
                        rfl

theorem cell23_1184588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1184588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184588 prefixEnd_1184588 := by exact prefixLift 1184588
  have htrace : WordTrace (prefixWord ++ tailWord_1184588) baseStart_1184588 baseEnd_1184588 := by
    simpa [prefixWord, tailWord_1184588, baseEnd_1184588] using wordTrace_append hprefix tailTrace_1184588
  have hstable : (prefixWord ++ tailWord_1184588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184588).length < 2 ^ (prefixWord ++ tailWord_1184588).sum := by decide
  have hdescent : baseEnd_1184588 < baseStart_1184588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184611 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1184611 : Nat := 118140960795 + 1184611 * 2 ^ 59
def prefixEnd_1184611 : Nat := 4983230072969 + 3 ^ 40 * 1184611 * 2
def baseEnd_1184611 : Nat := 608274831603369937714579

theorem tailTrace_1184611 : CollatzResearch.WordTrace tailWord_1184611 prefixEnd_1184611 608274831603369937714579 := by
  unfold tailWord_1184611
  simp only [CollatzResearch.WordTrace]
  refine ⟨43206312711364137296753687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28804208474242758197835791 43206312711364137296753687)
  ·
    refine ⟨64809469067046205945130531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43206312711364137296753687 64809469067046205945130531)
    ·
      refine ⟨97214203600569308917695797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64809469067046205945130531 97214203600569308917695797)
      ·
        refine ⟨9113831587553372711033981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97214203600569308917695797 9113831587553372711033981)
        ·
          refine ⟨3417686845332514766637743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9113831587553372711033981 3417686845332514766637743)
          ·
            refine ⟨5126530267998772149956615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417686845332514766637743 5126530267998772149956615)
            ·
              refine ⟨7689795401998158224934923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126530267998772149956615 7689795401998158224934923)
              ·
                refine ⟨11534693102997237337402385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7689795401998158224934923 11534693102997237337402385)
                ·
                  refine ⟨8651019827247928003051789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11534693102997237337402385 8651019827247928003051789)
                  ·
                    refine ⟨3244132435217973001144421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8651019827247928003051789 3244132435217973001144421)
                    ·
                      refine ⟨608274831603369937714579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3244132435217973001144421 608274831603369937714579)
                      ·
                        rfl

theorem cell23_1184611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1184611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184611 prefixEnd_1184611 := by exact prefixLift 1184611
  have htrace : WordTrace (prefixWord ++ tailWord_1184611) baseStart_1184611 baseEnd_1184611 := by
    simpa [prefixWord, tailWord_1184611, baseEnd_1184611] using wordTrace_append hprefix tailTrace_1184611
  have hstable : (prefixWord ++ tailWord_1184611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184611).length < 2 ^ (prefixWord ++ tailWord_1184611).sum := by decide
  have hdescent : baseEnd_1184611 < baseStart_1184611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184679 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_1184679 : Nat := 118140960795 + 1184679 * 2 ^ 59
def prefixEnd_1184679 : Nat := 4983230072969 + 3 ^ 40 * 1184679 * 2
def baseEnd_1184679 : Nat := 608309748287875671664267

theorem tailTrace_1184679 : CollatzResearch.WordTrace tailWord_1184679 prefixEnd_1184679 608309748287875671664267 := by
  unfold tailWord_1184679
  simp only [CollatzResearch.WordTrace]
  refine ⟨43208792875117784910229091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28805861916745189940152727 43208792875117784910229091)
  ·
    refine ⟨64813189312676677365343637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43208792875117784910229091 64813189312676677365343637)
    ·
      refine ⟨3038118249031719251500483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64813189312676677365343637 3038118249031719251500483)
      ·
        refine ⟨4557177373547578877250725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038118249031719251500483 4557177373547578877250725)
        ·
          refine ⟨854470757540171039484511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4557177373547578877250725 854470757540171039484511)
          ·
            refine ⟨1281706136310256559226767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854470757540171039484511 1281706136310256559226767)
            ·
              refine ⟨1922559204465384838840151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281706136310256559226767 1922559204465384838840151)
              ·
                refine ⟨2883838806698077258260227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922559204465384838840151 2883838806698077258260227)
                ·
                  refine ⟨4325758210047115887390341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883838806698077258260227 4325758210047115887390341)
                  ·
                    refine ⟨811079664383834228885689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4325758210047115887390341 811079664383834228885689)
                    ·
                      refine ⟨608309748287875671664267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811079664383834228885689 608309748287875671664267)
                      ·
                        rfl

theorem cell23_1184679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_1184679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184679 prefixEnd_1184679 := by exact prefixLift 1184679
  have htrace : WordTrace (prefixWord ++ tailWord_1184679) baseStart_1184679 baseEnd_1184679 := by
    simpa [prefixWord, tailWord_1184679, baseEnd_1184679] using wordTrace_append hprefix tailTrace_1184679
  have hstable : (prefixWord ++ tailWord_1184679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184679).length < 2 ^ (prefixWord ++ tailWord_1184679).sum := by decide
  have hdescent : baseEnd_1184679 < baseStart_1184679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184718 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_1184718 : Nat := 118140960795 + 1184718 * 2 ^ 59
def prefixEnd_1184718 : Nat := 4983230072969 + 3 ^ 40 * 1184718 * 2
def baseEnd_1184718 : Nat := 608329774033401019076587

theorem tailTrace_1184718 : CollatzResearch.WordTrace tailWord_1184718 prefixEnd_1184718 608329774033401019076587 := by
  unfold tailWord_1184718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401276915247061821362351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28806810214650996380599205 5401276915247061821362351)
  ·
    refine ⟨8101915372870592732043527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5401276915247061821362351 8101915372870592732043527)
    ·
      refine ⟨12152873059305889098065291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101915372870592732043527 12152873059305889098065291)
      ·
        refine ⟨18229309588958833647097937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12152873059305889098065291 18229309588958833647097937)
        ·
          refine ⟨13671982191719125235323453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18229309588958833647097937 13671982191719125235323453)
          ·
            refine ⟨5126993321894671963246295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13671982191719125235323453 5126993321894671963246295)
            ·
              refine ⟨7690489982842007944869443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126993321894671963246295 7690489982842007944869443)
              ·
                refine ⟨11535734974263011917304165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690489982842007944869443 11535734974263011917304165)
                ·
                  refine ⟨2162950307674314734494531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11535734974263011917304165 2162950307674314734494531)
                  ·
                    refine ⟨3244425461511472101741797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2162950307674314734494531 3244425461511472101741797)
                    ·
                      refine ⟨608329774033401019076587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3244425461511472101741797 608329774033401019076587)
                      ·
                        rfl

theorem cell23_1184718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_1184718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184718 prefixEnd_1184718 := by exact prefixLift 1184718
  have htrace : WordTrace (prefixWord ++ tailWord_1184718) baseStart_1184718 baseEnd_1184718 := by
    simpa [prefixWord, tailWord_1184718, baseEnd_1184718] using wordTrace_append hprefix tailTrace_1184718
  have hstable : (prefixWord ++ tailWord_1184718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184718).length < 2 ^ (prefixWord ++ tailWord_1184718).sum := by decide
  have hdescent : baseEnd_1184718 < baseStart_1184718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184779 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 1, 4]
def baseStart_1184779 : Nat := 118140960795 + 1184779 * 2 ^ 59
def prefixEnd_1184779 : Nat := 4983230072969 + 3 ^ 40 * 1184779 * 2
def baseEnd_1184779 : Nat := 202787032117775093471269

theorem tailTrace_1184779 : CollatzResearch.WordTrace tailWord_1184779 prefixEnd_1184779 202787032117775093471269 := by
  unfold tailWord_1184779
  simp only [CollatzResearch.WordTrace]
  refine ⟨43212440174755501988869391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28808293449837001325912927 43212440174755501988869391)
  ·
    refine ⟨64818660262133252983304087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43212440174755501988869391 64818660262133252983304087)
    ·
      refine ⟨97227990393199879474956131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64818660262133252983304087 97227990393199879474956131)
      ·
        refine ⟨145841985589799819212434197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97227990393199879474956131 145841985589799819212434197)
        ·
          refine ⟨6836343074521866525582853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145841985589799819212434197 6836343074521866525582853)
          ·
            refine ⟨1281814326472849973546785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6836343074521866525582853 1281814326472849973546785)
            ·
              refine ⟨961360744854637480160089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281814326472849973546785 961360744854637480160089)
              ·
                refine ⟨721020558640978110120067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961360744854637480160089 721020558640978110120067)
                ·
                  refine ⟨1081530837961467165180101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721020558640978110120067 1081530837961467165180101)
                  ·
                    refine ⟨202787032117775093471269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1081530837961467165180101 202787032117775093471269)
                    ·
                      rfl

theorem cell23_1184779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 1, 4].length) (baseStart_1184779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184779 prefixEnd_1184779 := by exact prefixLift 1184779
  have htrace : WordTrace (prefixWord ++ tailWord_1184779) baseStart_1184779 baseEnd_1184779 := by
    simpa [prefixWord, tailWord_1184779, baseEnd_1184779] using wordTrace_append hprefix tailTrace_1184779
  have hstable : (prefixWord ++ tailWord_1184779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184779).length < 2 ^ (prefixWord ++ tailWord_1184779).sum := by decide
  have hdescent : baseEnd_1184779 < baseStart_1184779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184786 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1184786 : Nat := 118140960795 + 1184786 * 2 ^ 59
def prefixEnd_1184786 : Nat := 4983230072969 + 3 ^ 40 * 1184786 * 2
def baseEnd_1184786 : Nat := 608364690717906753026275

theorem tailTrace_1184786 : CollatzResearch.WordTrace tailWord_1184786 prefixEnd_1184786 608364690717906753026275 := by
  unfold tailWord_1184786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803173871432535546093553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28808463657153428122916141 10803173871432535546093553)
  ·
    refine ⟨8102380403574401659570165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10803173871432535546093553 8102380403574401659570165)
    ·
      refine ⟨759598162835100155584703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8102380403574401659570165 759598162835100155584703)
      ·
        refine ⟨1139397244252650233377055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759598162835100155584703 1139397244252650233377055)
        ·
          refine ⟨1709095866378975350065583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139397244252650233377055 1709095866378975350065583)
          ·
            refine ⟨2563643799568463025098375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709095866378975350065583 2563643799568463025098375)
            ·
              refine ⟨3845465699352694537647563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563643799568463025098375 3845465699352694537647563)
              ·
                refine ⟨5768198549029041806471345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845465699352694537647563 5768198549029041806471345)
                ·
                  refine ⟨4326148911771781354853509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768198549029041806471345 4326148911771781354853509)
                  ·
                    refine ⟨811152920957209004035033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4326148911771781354853509 811152920957209004035033)
                    ·
                      refine ⟨608364690717906753026275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811152920957209004035033 608364690717906753026275)
                      ·
                        rfl

theorem cell23_1184786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1184786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184786 prefixEnd_1184786 := by exact prefixLift 1184786
  have htrace : WordTrace (prefixWord ++ tailWord_1184786) baseStart_1184786 baseEnd_1184786 := by
    simpa [prefixWord, tailWord_1184786, baseEnd_1184786] using wordTrace_append hprefix tailTrace_1184786
  have hstable : (prefixWord ++ tailWord_1184786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184786).length < 2 ^ (prefixWord ++ tailWord_1184786).sum := by decide
  have hdescent : baseEnd_1184786 < baseStart_1184786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184802 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1184802 : Nat := 118140960795 + 1184802 * 2 ^ 59
def prefixEnd_1184802 : Nat := 4983230072969 + 3 ^ 40 * 1184802 * 2
def baseEnd_1184802 : Nat := 608372906408378690426201

theorem tailTrace_1184802 : CollatzResearch.WordTrace tailWord_1184802 prefixEnd_1184802 608372906408378690426201 := by
  unfold tailWord_1184802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803319763418044229239165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28808852702448117944637773 10803319763418044229239165)
  ·
    refine ⟨4051244911281766585964687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10803319763418044229239165 4051244911281766585964687)
    ·
      refine ⟨6076867366922649878947031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051244911281766585964687 6076867366922649878947031)
      ·
        refine ⟨9115301050383974818420547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076867366922649878947031 9115301050383974818420547)
        ·
          refine ⟨13672951575575962227630821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9115301050383974818420547 13672951575575962227630821)
          ·
            refine ⟨2563678420420492917680779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13672951575575962227630821 2563678420420492917680779)
            ·
              refine ⟨3845517630630739376521169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563678420420492917680779 3845517630630739376521169)
              ·
                refine ⟨2884138222973054532390877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3845517630630739376521169 2884138222973054532390877)
                ·
                  refine ⟨1081551833614895449646579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2884138222973054532390877 1081551833614895449646579)
                  ·
                    refine ⟨1622327750422343174469869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081551833614895449646579 1622327750422343174469869)
                    ·
                      refine ⟨608372906408378690426201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1622327750422343174469869 608372906408378690426201)
                      ·
                        rfl

theorem cell23_1184802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1184802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184802 prefixEnd_1184802 := by exact prefixLift 1184802
  have htrace : WordTrace (prefixWord ++ tailWord_1184802) baseStart_1184802 baseEnd_1184802 := by
    simpa [prefixWord, tailWord_1184802, baseEnd_1184802] using wordTrace_append hprefix tailTrace_1184802
  have hstable : (prefixWord ++ tailWord_1184802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184802).length < 2 ^ (prefixWord ++ tailWord_1184802).sum := by decide
  have hdescent : baseEnd_1184802 < baseStart_1184802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184818 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_1184818 : Nat := 118140960795 + 1184818 * 2 ^ 59
def prefixEnd_1184818 : Nat := 4983230072969 + 3 ^ 40 * 1184818 * 2
def baseEnd_1184818 : Nat := 202793707366283542608709

theorem tailTrace_1184818 : CollatzResearch.WordTrace tailWord_1184818 prefixEnd_1184818 202793707366283542608709 := by
  unfold tailWord_1184818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803465655403552912384777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28809241747742807766359405 10803465655403552912384777)
  ·
    refine ⟨8102599241552664684288583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10803465655403552912384777 8102599241552664684288583)
    ·
      refine ⟨12153898862328997026432875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8102599241552664684288583 12153898862328997026432875)
      ·
        refine ⟨18230848293493495539649313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12153898862328997026432875 18230848293493495539649313)
        ·
          refine ⟨13673136220120121654736985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18230848293493495539649313 13673136220120121654736985)
          ·
            refine ⟨10254852165090091241052739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13673136220120121654736985 10254852165090091241052739)
            ·
              refine ⟨15382278247635136861579109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10254852165090091241052739 15382278247635136861579109)
              ·
                refine ⟨2884177171431588161546083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15382278247635136861579109 2884177171431588161546083)
                ·
                  refine ⟨4326265757147382242319125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884177171431588161546083 4326265757147382242319125)
                  ·
                    refine ⟨202793707366283542608709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4326265757147382242319125 202793707366283542608709)
                    ·
                      rfl

theorem cell23_1184818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_1184818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184818 prefixEnd_1184818 := by exact prefixLift 1184818
  have htrace : WordTrace (prefixWord ++ tailWord_1184818) baseStart_1184818 baseEnd_1184818 := by
    simpa [prefixWord, tailWord_1184818, baseEnd_1184818] using wordTrace_append hprefix tailTrace_1184818
  have hstable : (prefixWord ++ tailWord_1184818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184818).length < 2 ^ (prefixWord ++ tailWord_1184818).sum := by decide
  have hdescent : baseEnd_1184818 < baseStart_1184818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184822 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1184822 : Nat := 118140960795 + 1184822 * 2 ^ 59
def prefixEnd_1184822 : Nat := 4983230072969 + 3 ^ 40 * 1184822 * 2
def baseEnd_1184822 : Nat := 202794392007156204058703

theorem tailTrace_1184822 : CollatzResearch.WordTrace tailWord_1184822 prefixEnd_1184822 202794392007156204058703 := by
  unfold tailWord_1184822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700875532099982520792795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28809339009066480221789813 2700875532099982520792795)
  ·
    refine ⟨4051313298149973781189193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2700875532099982520792795 4051313298149973781189193)
    ·
      refine ⟨3038484973612480335891895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4051313298149973781189193 3038484973612480335891895)
      ·
        refine ⟨4557727460418720503837843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038484973612480335891895 4557727460418720503837843)
        ·
          refine ⟨6836591190628080755756765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557727460418720503837843 6836591190628080755756765)
          ·
            refine ⟨2563721696485530283408787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6836591190628080755756765 2563721696485530283408787)
            ·
              refine ⟨3845582544728295425113181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563721696485530283408787 3845582544728295425113181)
              ·
                refine ⟨1442093454273110784417443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3845582544728295425113181 1442093454273110784417443)
                ·
                  refine ⟨2163140181409666176626165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442093454273110784417443 2163140181409666176626165)
                  ·
                    refine ⟨202794392007156204058703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2163140181409666176626165 202794392007156204058703)
                    ·
                      rfl

theorem cell23_1184822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1184822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184822 prefixEnd_1184822 := by exact prefixLift 1184822
  have htrace : WordTrace (prefixWord ++ tailWord_1184822) baseStart_1184822 baseEnd_1184822 := by
    simpa [prefixWord, tailWord_1184822, baseEnd_1184822] using wordTrace_append hprefix tailTrace_1184822
  have hstable : (prefixWord ++ tailWord_1184822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184822).length < 2 ^ (prefixWord ++ tailWord_1184822).sum := by decide
  have hdescent : baseEnd_1184822 < baseStart_1184822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184842 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_1184842 : Nat := 118140960795 + 1184842 * 2 ^ 59
def prefixEnd_1184842 : Nat := 4983230072969 + 3 ^ 40 * 1184842 * 2
def baseEnd_1184842 : Nat := 608393445634558533926017

theorem tailTrace_1184842 : CollatzResearch.WordTrace tailWord_1184842 prefixEnd_1184842 608393445634558533926017 := by
  unfold tailWord_1184842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803684493381815937103195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28809825315684842498941853 10803684493381815937103195)
  ·
    refine ⟨16205526740072723905654793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10803684493381815937103195 16205526740072723905654793)
    ·
      refine ⟨12154145055054542929241095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16205526740072723905654793 12154145055054542929241095)
      ·
        refine ⟨18231217582581814393861643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12154145055054542929241095 18231217582581814393861643)
        ·
          refine ⟨27346826373872721590792465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18231217582581814393861643 27346826373872721590792465)
          ·
            refine ⟨20510119780404541193094349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27346826373872721590792465 20510119780404541193094349)
            ·
              refine ⟨7691294917651702947410381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20510119780404541193094349 7691294917651702947410381)
              ·
                refine ⟨2884235594119388605278893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7691294917651702947410381 2884235594119388605278893)
                ·
                  refine ⟨1081588347794770726979585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2884235594119388605278893 1081588347794770726979585)
                  ·
                    refine ⟨811191260846078045234689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1081588347794770726979585 811191260846078045234689)
                    ·
                      refine ⟨608393445634558533926017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811191260846078045234689 608393445634558533926017)
                      ·
                        rfl

theorem cell23_1184842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_1184842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184842 prefixEnd_1184842 := by exact prefixLift 1184842
  have htrace : WordTrace (prefixWord ++ tailWord_1184842) baseStart_1184842 baseEnd_1184842 := by
    simpa [prefixWord, tailWord_1184842, baseEnd_1184842] using wordTrace_append hprefix tailTrace_1184842
  have hstable : (prefixWord ++ tailWord_1184842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184842).length < 2 ^ (prefixWord ++ tailWord_1184842).sum := by decide
  have hdescent : baseEnd_1184842 < baseStart_1184842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184845 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1184845 : Nat := 118140960795 + 1184845 * 2 ^ 59
def prefixEnd_1184845 : Nat := 4983230072969 + 3 ^ 40 * 1184845 * 2
def baseEnd_1184845 : Nat := 608394986076522022188503

theorem tailTrace_1184845 : CollatzResearch.WordTrace tailWord_1184845 prefixEnd_1184845 608394986076522022188503 := by
  unfold tailWord_1184845
  simp only [CollatzResearch.WordTrace]
  refine ⟨43214847392516395260771989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28809898261677596840514659 43214847392516395260771989)
  ·
    refine ⟨2025695971524206027848687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43214847392516395260771989 2025695971524206027848687)
    ·
      refine ⟨3038543957286309041773031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2025695971524206027848687 3038543957286309041773031)
      ·
        refine ⟨4557815935929463562659547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038543957286309041773031 4557815935929463562659547)
        ·
          refine ⟨6836723903894195343989321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557815935929463562659547 6836723903894195343989321)
          ·
            refine ⟨5127542927920646507991991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6836723903894195343989321 5127542927920646507991991)
            ·
              refine ⟨7691314391880969761987987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127542927920646507991991 7691314391880969761987987)
              ·
                refine ⟨11536971587821454642981981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7691314391880969761987987 11536971587821454642981981)
                ·
                  refine ⟨4326364345433045491118243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11536971587821454642981981 4326364345433045491118243)
                  ·
                    refine ⟨6489546518149568236677365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4326364345433045491118243 6489546518149568236677365)
                    ·
                      refine ⟨608394986076522022188503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6489546518149568236677365 608394986076522022188503)
                      ·
                        rfl

theorem cell23_1184845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1184845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184845 prefixEnd_1184845 := by exact prefixLift 1184845
  have htrace : WordTrace (prefixWord ++ tailWord_1184845) baseStart_1184845 baseEnd_1184845 := by
    simpa [prefixWord, tailWord_1184845, baseEnd_1184845] using wordTrace_append hprefix tailTrace_1184845
  have hstable : (prefixWord ++ tailWord_1184845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184845).length < 2 ^ (prefixWord ++ tailWord_1184845).sum := by decide
  have hdescent : baseEnd_1184845 < baseStart_1184845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184892 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_1184892 : Nat := 118140960795 + 1184892 * 2 ^ 59
def prefixEnd_1184892 : Nat := 4983230072969 + 3 ^ 40 * 1184892 * 2
def baseEnd_1184892 : Nat := 608419119667283338300787

theorem tailTrace_1184892 : CollatzResearch.WordTrace tailWord_1184892 prefixEnd_1184892 608419119667283338300787 := by
  unfold tailWord_1184892
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608280811673061143866465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28811041082230748191821953 21608280811673061143866465)
  ·
    refine ⟨16206210608754795857899849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21608280811673061143866465 16206210608754795857899849)
    ·
      refine ⟨12154657956566096893424887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16206210608754795857899849 12154657956566096893424887)
      ·
        refine ⟨18231986934849145340137331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12154657956566096893424887 18231986934849145340137331)
        ·
          refine ⟨27347980402273718010205997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18231986934849145340137331 27347980402273718010205997)
          ·
            refine ⟨10255492650852644253827249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27347980402273718010205997 10255492650852644253827249)
            ·
              refine ⟨7691619488139483190370437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10255492650852644253827249 7691619488139483190370437)
              ·
                refine ⟨1442178654026153098194457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7691619488139483190370437 1442178654026153098194457)
                ·
                  refine ⟨1081633990519614823645843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1442178654026153098194457 1081633990519614823645843)
                  ·
                    refine ⟨1622450985779422235468765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081633990519614823645843 1622450985779422235468765)
                    ·
                      refine ⟨608419119667283338300787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1622450985779422235468765 608419119667283338300787)
                      ·
                        rfl

theorem cell23_1184892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_1184892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184892 prefixEnd_1184892 := by exact prefixLift 1184892
  have htrace : WordTrace (prefixWord ++ tailWord_1184892) baseStart_1184892 baseEnd_1184892 := by
    simpa [prefixWord, tailWord_1184892, baseEnd_1184892] using wordTrace_append hprefix tailTrace_1184892
  have hstable : (prefixWord ++ tailWord_1184892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184892).length < 2 ^ (prefixWord ++ tailWord_1184892).sum := by decide
  have hdescent : baseEnd_1184892 < baseStart_1184892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184908 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_1184908 : Nat := 118140960795 + 1184908 * 2 ^ 59
def prefixEnd_1184908 : Nat := 4983230072969 + 3 ^ 40 * 1184908 * 2
def baseEnd_1184908 : Nat := 202809111785918425233571

theorem tailTrace_1184908 : CollatzResearch.WordTrace tailWord_1184908 prefixEnd_1184908 202809111785918425233571 := by
  unfold tailWord_1184908
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608572595644078510157689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28811430127525438013543585 21608572595644078510157689)
  ·
    refine ⟨16206429446733058882618267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21608572595644078510157689 16206429446733058882618267)
    ·
      refine ⟨24309644170099588323927401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16206429446733058882618267 24309644170099588323927401)
      ·
        refine ⟨18232233127574691242945551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24309644170099588323927401 18232233127574691242945551)
        ·
          refine ⟨27348349691362036864418327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18232233127574691242945551 27348349691362036864418327)
          ·
            refine ⟨41022524537043055296627491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27348349691362036864418327 41022524537043055296627491)
            ·
              refine ⟨61533786805564582944941237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41022524537043055296627491 61533786805564582944941237)
              ·
                refine ⟨5768792513021679651088241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61533786805564582944941237 5768792513021679651088241)
                ·
                  refine ⟨4326594384766259738316181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768792513021679651088241 4326594384766259738316181)
                  ·
                    refine ⟨202809111785918425233571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4326594384766259738316181 202809111785918425233571)
                    ·
                      rfl

theorem cell23_1184908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_1184908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184908 prefixEnd_1184908 := by exact prefixLift 1184908
  have htrace : WordTrace (prefixWord ++ tailWord_1184908) baseStart_1184908 baseEnd_1184908 := by
    simpa [prefixWord, tailWord_1184908, baseEnd_1184908] using wordTrace_append hprefix tailTrace_1184908
  have hstable : (prefixWord ++ tailWord_1184908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184908).length < 2 ^ (prefixWord ++ tailWord_1184908).sum := by decide
  have hdescent : baseEnd_1184908 < baseStart_1184908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184919 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 1, 3, 2]
def baseStart_1184919 : Nat := 118140960795 + 1184919 * 2 ^ 59
def prefixEnd_1184919 : Nat := 4983230072969 + 3 ^ 40 * 1184919 * 2
def baseEnd_1184919 : Nat := 608432983644954732663163

theorem tailTrace_1184919 : CollatzResearch.WordTrace tailWord_1184919 prefixEnd_1184919 608432983644954732663163 := by
  unfold tailWord_1184919
  simp only [CollatzResearch.WordTrace]
  refine ⟨43217546394248305898965811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28811697596165537265977207 43217546394248305898965811)
  ·
    refine ⟨64826319591372458848448717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43217546394248305898965811 64826319591372458848448717)
    ·
      refine ⟨24309869846764672068168269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64826319591372458848448717 24309869846764672068168269)
      ·
        refine ⟨9116201192536752025563101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24309869846764672068168269 9116201192536752025563101)
        ·
          refine ⟨3418575447201282009586163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9116201192536752025563101 3418575447201282009586163)
          ·
            refine ⟨5127863170801923014379245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418575447201282009586163 5127863170801923014379245)
            ·
              refine ⟨1922948689050721130392217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5127863170801923014379245 1922948689050721130392217)
              ·
                refine ⟨1442211516788040847794163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922948689050721130392217 1442211516788040847794163)
                ·
                  refine ⟨2163317275182061271691245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442211516788040847794163 2163317275182061271691245)
                  ·
                    refine ⟨811243978193272976884217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163317275182061271691245 811243978193272976884217)
                    ·
                      refine ⟨608432983644954732663163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811243978193272976884217 608432983644954732663163)
                      ·
                        rfl

theorem cell23_1184919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_1184919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184919 prefixEnd_1184919 := by exact prefixLift 1184919
  have htrace : WordTrace (prefixWord ++ tailWord_1184919) baseStart_1184919 baseEnd_1184919 := by
    simpa [prefixWord, tailWord_1184919, baseEnd_1184919] using wordTrace_append hprefix tailTrace_1184919
  have hstable : (prefixWord ++ tailWord_1184919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184919).length < 2 ^ (prefixWord ++ tailWord_1184919).sum := by decide
  have hdescent : baseEnd_1184919 < baseStart_1184919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184932 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_1184932 : Nat := 118140960795 + 1184932 * 2 ^ 59
def prefixEnd_1184932 : Nat := 4983230072969 + 3 ^ 40 * 1184932 * 2
def baseEnd_1184932 : Nat := 608439658893463181800603

theorem tailTrace_1184932 : CollatzResearch.WordTrace tailWord_1184932 prefixEnd_1184932 608439658893463181800603 := by
  unfold tailWord_1184932
  simp only [CollatzResearch.WordTrace]
  refine ⟨21609010271600604559594525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28812013695467472746126033 21609010271600604559594525)
  ·
    refine ⟨8103378851850226709847947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21609010271600604559594525 8103378851850226709847947)
    ·
      refine ⟨12155068277775340064771921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8103378851850226709847947 12155068277775340064771921)
      ·
        refine ⟨9116301208331505048578941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12155068277775340064771921 9116301208331505048578941)
        ·
          refine ⟨3418612953124314393217103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9116301208331505048578941 3418612953124314393217103)
          ·
            refine ⟨5127919429686471589825655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418612953124314393217103 5127919429686471589825655)
            ·
              refine ⟨7691879144529707384738483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127919429686471589825655 7691879144529707384738483)
              ·
                refine ⟨11537818716794561077107725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7691879144529707384738483 11537818716794561077107725)
                ·
                  refine ⟨4326682018797960403915397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11537818716794561077107725 4326682018797960403915397)
                  ·
                    refine ⟨811252878524617575734137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4326682018797960403915397 811252878524617575734137)
                    ·
                      refine ⟨608439658893463181800603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811252878524617575734137 608439658893463181800603)
                      ·
                        rfl

theorem cell23_1184932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_1184932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1184932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1184932 prefixEnd_1184932 := by exact prefixLift 1184932
  have htrace : WordTrace (prefixWord ++ tailWord_1184932) baseStart_1184932 baseEnd_1184932 := by
    simpa [prefixWord, tailWord_1184932, baseEnd_1184932] using wordTrace_append hprefix tailTrace_1184932
  have hstable : (prefixWord ++ tailWord_1184932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184932).length < 2 ^ (prefixWord ++ tailWord_1184932).sum := by decide
  have hdescent : baseEnd_1184932 < baseStart_1184932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185015 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 7, 4]
def baseStart_1185015 : Nat := 118140960795 + 1185015 * 2 ^ 59
def prefixEnd_1185015 : Nat := 4983230072969 + 3 ^ 40 * 1185015 * 2
def baseEnd_1185015 : Nat := 202827425929262119020907

theorem tailTrace_1185015 : CollatzResearch.WordTrace tailWord_1185015 prefixEnd_1185015 202827425929262119020907 := by
  unfold tailWord_1185015
  simp only [CollatzResearch.WordTrace]
  refine ⟨43221047801900514294460499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28814031867933676196306999 43221047801900514294460499)
  ·
    refine ⟨64831571702850771441690749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43221047801900514294460499 64831571702850771441690749)
    ·
      refine ⟨24311839388569039290634031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64831571702850771441690749 24311839388569039290634031)
      ·
        refine ⟨36467759082853558935951047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24311839388569039290634031 36467759082853558935951047)
        ·
          refine ⟨54701638624280338403926571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36467759082853558935951047 54701638624280338403926571)
          ·
            refine ⟨82052457936420507605889857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54701638624280338403926571 82052457936420507605889857)
            ·
              refine ⟨61539343452315380704417393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82052457936420507605889857 61539343452315380704417393)
              ·
                refine ⟨46154507589236535528313045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61539343452315380704417393 46154507589236535528313045)
                ·
                  refine ⟨1081746271622731301444837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 46154507589236535528313045 1081746271622731301444837)
                  ·
                    refine ⟨202827425929262119020907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1081746271622731301444837 202827425929262119020907)
                    ·
                      rfl

theorem cell23_1185015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_1185015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185015 prefixEnd_1185015 := by exact prefixLift 1185015
  have htrace : WordTrace (prefixWord ++ tailWord_1185015) baseStart_1185015 baseEnd_1185015 := by
    simpa [prefixWord, tailWord_1185015, baseEnd_1185015] using wordTrace_append hprefix tailTrace_1185015
  have hstable : (prefixWord ++ tailWord_1185015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185015).length < 2 ^ (prefixWord ++ tailWord_1185015).sum := by decide
  have hdescent : baseEnd_1185015 < baseStart_1185015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185022 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1185022 : Nat := 118140960795 + 1185022 * 2 ^ 59
def prefixEnd_1185022 : Nat := 4983230072969 + 3 ^ 40 * 1185022 * 2
def baseEnd_1185022 : Nat := 608485872152367829675189

theorem tailTrace_1185022 : CollatzResearch.WordTrace tailWord_1185022 prefixEnd_1185022 608485872152367829675189 := by
  unfold tailWord_1185022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402662889109394311245665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28814202075250102993310213 5402662889109394311245665)
  ·
    refine ⟨4051997166832045733434249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5402662889109394311245665 4051997166832045733434249)
    ·
      refine ⟨3038997875124034300075687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4051997166832045733434249 3038997875124034300075687)
      ·
        refine ⟨4558496812686051450113531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038997875124034300075687 4558496812686051450113531)
        ·
          refine ⟨6837745219029077175170297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558496812686051450113531 6837745219029077175170297)
          ·
            refine ⟨5128308914271807881377723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6837745219029077175170297 5128308914271807881377723)
            ·
              refine ⟨7692463371407711822066585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5128308914271807881377723 7692463371407711822066585)
              ·
                refine ⟨5769347528555783866549939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7692463371407711822066585 5769347528555783866549939)
                ·
                  refine ⟨8654021292833675799824909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5769347528555783866549939 8654021292833675799824909)
                  ·
                    refine ⟨3245257984812628424934341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8654021292833675799824909 3245257984812628424934341)
                    ·
                      refine ⟨608485872152367829675189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3245257984812628424934341 608485872152367829675189)
                      ·
                        rfl

theorem cell23_1185022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1185022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185022 prefixEnd_1185022 := by exact prefixLift 1185022
  have htrace : WordTrace (prefixWord ++ tailWord_1185022) baseStart_1185022 baseEnd_1185022 := by
    simpa [prefixWord, tailWord_1185022, baseEnd_1185022] using wordTrace_append hprefix tailTrace_1185022
  have hstable : (prefixWord ++ tailWord_1185022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185022).length < 2 ^ (prefixWord ++ tailWord_1185022).sum := by decide
  have hdescent : baseEnd_1185022 < baseStart_1185022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185066 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1185066 : Nat := 118140960795 + 1185066 * 2 ^ 59
def prefixEnd_1185066 : Nat := 4983230072969 + 3 ^ 40 * 1185066 * 2
def baseEnd_1185066 : Nat := 202836155100388552508329

theorem tailTrace_1185066 : CollatzResearch.WordTrace tailWord_1185066 prefixEnd_1185066 202836155100388552508329 := by
  unfold tailWord_1185066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10805726981178937501141763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28815271949810500003044701 10805726981178937501141763)
  ·
    refine ⟨16208590471768406251712645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10805726981178937501141763 16208590471768406251712645)
    ·
      refine ⟨3039110713456576172196121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16208590471768406251712645 3039110713456576172196121)
      ·
        refine ⟨2279333035092432129147091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3039110713456576172196121 2279333035092432129147091)
        ·
          refine ⟨3418999552638648193720637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279333035092432129147091 3418999552638648193720637)
          ·
            refine ⟨1282124832239493072645239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418999552638648193720637 1282124832239493072645239)
            ·
              refine ⟨1923187248359239608967859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282124832239493072645239 1923187248359239608967859)
              ·
                refine ⟨2884780872538859413451789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923187248359239608967859 2884780872538859413451789)
                ·
                  refine ⟨1081792827202072280044421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2884780872538859413451789 1081792827202072280044421)
                  ·
                    refine ⟨202836155100388552508329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1081792827202072280044421 202836155100388552508329)
                    ·
                      rfl

theorem cell23_1185066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1185066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185066 prefixEnd_1185066 := by exact prefixLift 1185066
  have htrace : WordTrace (prefixWord ++ tailWord_1185066) baseStart_1185066 baseEnd_1185066 := by
    simpa [prefixWord, tailWord_1185066, baseEnd_1185066] using wordTrace_append hprefix tailTrace_1185066
  have hstable : (prefixWord ++ tailWord_1185066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185066).length < 2 ^ (prefixWord ++ tailWord_1185066).sum := by decide
  have hdescent : baseEnd_1185066 < baseStart_1185066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185106 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_1185106 : Nat := 118140960795 + 1185106 * 2 ^ 59
def prefixEnd_1185106 : Nat := 4983230072969 + 3 ^ 40 * 1185106 * 2
def baseEnd_1185106 : Nat := 608529004527345501024803

theorem tailTrace_1185106 : CollatzResearch.WordTrace tailWord_1185106 prefixEnd_1185106 608529004527345501024803 := by
  unfold tailWord_1185106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806091711142709209005793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28816244563047224557348781 10806091711142709209005793)
  ·
    refine ⟨8104568783357031906754345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10806091711142709209005793 8104568783357031906754345)
    ·
      refine ⟨6078426587517773930065759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8104568783357031906754345 6078426587517773930065759)
      ·
        refine ⟨9117639881276660895098639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6078426587517773930065759 9117639881276660895098639)
        ·
          refine ⟨13676459821914991342647959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117639881276660895098639 13676459821914991342647959)
          ·
            refine ⟨20514689732872487013971939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13676459821914991342647959 20514689732872487013971939)
            ·
              refine ⟨30772034599308730520957909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20514689732872487013971939 30772034599308730520957909)
              ·
                refine ⟨721219560921298371584951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30772034599308730520957909 721219560921298371584951)
                ·
                  refine ⟨1081829341381947557377427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721219560921298371584951 1081829341381947557377427)
                  ·
                    refine ⟨1622744012072921336066141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081829341381947557377427 1622744012072921336066141)
                    ·
                      refine ⟨608529004527345501024803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1622744012072921336066141 608529004527345501024803)
                      ·
                        rfl

theorem cell23_1185106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_1185106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185106 prefixEnd_1185106 := by exact prefixLift 1185106
  have htrace : WordTrace (prefixWord ++ tailWord_1185106) baseStart_1185106 baseEnd_1185106 := by
    simpa [prefixWord, tailWord_1185106, baseEnd_1185106] using wordTrace_append hprefix tailTrace_1185106
  have hstable : (prefixWord ++ tailWord_1185106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185106).length < 2 ^ (prefixWord ++ tailWord_1185106).sum := by decide
  have hdescent : baseEnd_1185106 < baseStart_1185106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185122 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1185122 : Nat := 118140960795 + 1185122 * 2 ^ 59
def prefixEnd_1185122 : Nat := 4983230072969 + 3 ^ 40 * 1185122 * 2
def baseEnd_1185122 : Nat := 202845740072605812808243

theorem tailTrace_1185122 : CollatzResearch.WordTrace tailWord_1185122 prefixEnd_1185122 202845740072605812808243 := by
  unfold tailWord_1185122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806237603128217892151405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28816633608341914379070413 10806237603128217892151405)
  ·
    refine ⟨4052339101173081709556777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10806237603128217892151405 4052339101173081709556777)
    ·
      refine ⟨3039254325879811282167583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4052339101173081709556777 3039254325879811282167583)
      ·
        refine ⟨4558881488819716923251375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039254325879811282167583 4558881488819716923251375)
        ·
          refine ⟨6838322233229575384877063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558881488819716923251375 6838322233229575384877063)
          ·
            refine ⟨10257483349844363077315595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838322233229575384877063 10257483349844363077315595)
            ·
              refine ⟨15386225024766544615973393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10257483349844363077315595 15386225024766544615973393)
              ·
                refine ⟨11539668768574908461980045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15386225024766544615973393 11539668768574908461980045)
                ·
                  refine ⟨4327375788215590673242517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11539668768574908461980045 4327375788215590673242517)
                  ·
                    refine ⟨202845740072605812808243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4327375788215590673242517 202845740072605812808243)
                    ·
                      rfl

theorem cell23_1185122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1185122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185122 prefixEnd_1185122 := by exact prefixLift 1185122
  have htrace : WordTrace (prefixWord ++ tailWord_1185122) baseStart_1185122 baseEnd_1185122 := by
    simpa [prefixWord, tailWord_1185122, baseEnd_1185122] using wordTrace_append hprefix tailTrace_1185122
  have hstable : (prefixWord ++ tailWord_1185122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185122).length < 2 ^ (prefixWord ++ tailWord_1185122).sum := by decide
  have hdescent : baseEnd_1185122 < baseStart_1185122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185123 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 1, 1, 3]
def baseStart_1185123 : Nat := 118140960795 + 1185123 * 2 ^ 59
def prefixEnd_1185123 : Nat := 4983230072969 + 3 ^ 40 * 1185123 * 2
def baseEnd_1185123 : Nat := 608537733698471934512225

theorem tailTrace_1185123 : CollatzResearch.WordTrace tailWord_1185123 prefixEnd_1185123 608537733698471934512225 := by
  unfold tailWord_1185123
  simp only [CollatzResearch.WordTrace]
  refine ⟨43224986885509248739392023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28816657923672832492928015 43224986885509248739392023)
  ·
    refine ⟨64837480328263873109088035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43224986885509248739392023 64837480328263873109088035)
    ·
      refine ⟨97256220492395809663632053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64837480328263873109088035 97256220492395809663632053)
      ·
        refine ⟨9117770671162107155965505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97256220492395809663632053 9117770671162107155965505)
        ·
          refine ⟨6838328003371580366974129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9117770671162107155965505 6838328003371580366974129)
          ·
            refine ⟨5128746002528685275230597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6838328003371580366974129 5128746002528685275230597)
            ·
              refine ⟨961639875474128489105737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5128746002528685275230597 961639875474128489105737)
              ·
                refine ⟨721229906605596366829303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961639875474128489105737 721229906605596366829303)
                ·
                  refine ⟨1081844859908394550243955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721229906605596366829303 1081844859908394550243955)
                  ·
                    refine ⟨1622767289862591825365933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081844859908394550243955 1622767289862591825365933)
                    ·
                      refine ⟨608537733698471934512225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1622767289862591825365933 608537733698471934512225)
                      ·
                        rfl

theorem cell23_1185123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_1185123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185123 prefixEnd_1185123 := by exact prefixLift 1185123
  have htrace : WordTrace (prefixWord ++ tailWord_1185123) baseStart_1185123 baseEnd_1185123 := by
    simpa [prefixWord, tailWord_1185123, baseEnd_1185123] using wordTrace_append hprefix tailTrace_1185123
  have hstable : (prefixWord ++ tailWord_1185123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185123).length < 2 ^ (prefixWord ++ tailWord_1185123).sum := by decide
  have hdescent : baseEnd_1185123 < baseStart_1185123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185149 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_1185149 : Nat := 118140960795 + 1185149 * 2 ^ 59
def prefixEnd_1185149 : Nat := 4983230072969 + 3 ^ 40 * 1185149 * 2
def baseEnd_1185149 : Nat := 608551084195488832787105

theorem tailTrace_1185149 : CollatzResearch.WordTrace tailWord_1185149 prefixEnd_1185149 608551084195488832787105 := by
  unfold tailWord_1185149
  simp only [CollatzResearch.WordTrace]
  refine ⟨43225935183415055179838501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28817290122276703453225667 43225935183415055179838501)
  ·
    refine ⟨8104862846890322846219719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43225935183415055179838501 8104862846890322846219719)
    ·
      refine ⟨12157294270335484269329579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8104862846890322846219719 12157294270335484269329579)
      ·
        refine ⟨18235941405503226403994369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12157294270335484269329579 18235941405503226403994369)
        ·
          refine ⟨13676956054127419802995777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18235941405503226403994369 13676956054127419802995777)
          ·
            refine ⟨10257717040595564852246833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13676956054127419802995777 10257717040595564852246833)
            ·
              refine ⟨7693287780446673639185125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10257717040595564852246833 7693287780446673639185125)
              ·
                refine ⟨1442491458833751307347211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7693287780446673639185125 1442491458833751307347211)
                ·
                  refine ⟨2163737188250626961020817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442491458833751307347211 2163737188250626961020817)
                  ·
                    refine ⟨1622802891187970220765613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2163737188250626961020817 1622802891187970220765613)
                    ·
                      refine ⟨608551084195488832787105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1622802891187970220765613 608551084195488832787105)
                      ·
                        rfl

theorem cell23_1185149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_1185149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185149 prefixEnd_1185149 := by exact prefixLift 1185149
  have htrace : WordTrace (prefixWord ++ tailWord_1185149) baseStart_1185149 baseEnd_1185149 := by
    simpa [prefixWord, tailWord_1185149, baseEnd_1185149] using wordTrace_append hprefix tailTrace_1185149
  have hstable : (prefixWord ++ tailWord_1185149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185149).length < 2 ^ (prefixWord ++ tailWord_1185149).sum := by decide
  have hdescent : baseEnd_1185149 < baseStart_1185149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185163 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 1, 2, 2]
def baseStart_1185163 : Nat := 118140960795 + 1185163 * 2 ^ 59
def prefixEnd_1185163 : Nat := 4983230072969 + 3 ^ 40 * 1185163 * 2
def baseEnd_1185163 : Nat := 608558272924651778012041

theorem tailTrace_1185163 : CollatzResearch.WordTrace tailWord_1185163 prefixEnd_1185163 608558272924651778012041 := by
  unfold tailWord_1185163
  simp only [CollatzResearch.WordTrace]
  refine ⟨43226445805364335570848143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28817630536909557047232095 43226445805364335570848143)
  ·
    refine ⟨64839668708046503356272215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43226445805364335570848143 64839668708046503356272215)
    ·
      refine ⟨97259503062069755034408323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64839668708046503356272215 97259503062069755034408323)
      ·
        refine ⟨145889254593104632551612485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97259503062069755034408323 145889254593104632551612485)
        ·
          refine ⟨27354235236207118603427341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145889254593104632551612485 27354235236207118603427341)
          ·
            refine ⟨10257838213577669476285253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27354235236207118603427341 10257838213577669476285253)
            ·
              refine ⟨1923344665045813026803485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10257838213577669476285253 1923344665045813026803485)
              ·
                refine ⟨721254249392179885051307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1923344665045813026803485 721254249392179885051307)
                ·
                  refine ⟨1081881374088269827576961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721254249392179885051307 1081881374088269827576961)
                  ·
                    refine ⟨811411030566202370682721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1081881374088269827576961 811411030566202370682721)
                    ·
                      refine ⟨608558272924651778012041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811411030566202370682721 608558272924651778012041)
                      ·
                        rfl

theorem cell23_1185163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 1, 2, 2].length) (baseStart_1185163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185163 prefixEnd_1185163 := by exact prefixLift 1185163
  have htrace : WordTrace (prefixWord ++ tailWord_1185163) baseStart_1185163 baseEnd_1185163 := by
    simpa [prefixWord, tailWord_1185163, baseEnd_1185163] using wordTrace_append hprefix tailTrace_1185163
  have hstable : (prefixWord ++ tailWord_1185163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185163).length < 2 ^ (prefixWord ++ tailWord_1185163).sum := by decide
  have hdescent : baseEnd_1185163 < baseStart_1185163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185180 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1185180 : Nat := 118140960795 + 1185180 * 2 ^ 59
def prefixEnd_1185180 : Nat := 4983230072969 + 3 ^ 40 * 1185180 * 2
def baseEnd_1185180 : Nat := 608567002095778211499463

theorem tailTrace_1185180 : CollatzResearch.WordTrace tailWord_1185180 prefixEnd_1185180 608567002095778211499463 := by
  unfold tailWord_1185180
  simp only [CollatzResearch.WordTrace]
  refine ⟨21613532923151373737108497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28818043897535164982811329 21613532923151373737108497)
  ·
    refine ⟨16210149692363530302831373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21613532923151373737108497 16210149692363530302831373)
    ·
      refine ⟨6078806134636323863561765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16210149692363530302831373 6078806134636323863561765)
      ·
        refine ⟨1139776150244310724417831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6078806134636323863561765 1139776150244310724417831)
        ·
          refine ⟨1709664225366466086626747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139776150244310724417831 1709664225366466086626747)
          ·
            refine ⟨2564496338049699129940121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709664225366466086626747 2564496338049699129940121)
            ·
              refine ⟨1923372253537274347455091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564496338049699129940121 1923372253537274347455091)
              ·
                refine ⟨2885058380305911521182637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923372253537274347455091 2885058380305911521182637)
                ·
                  refine ⟨1081896892614716820443489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2885058380305911521182637 1081896892614716820443489)
                  ·
                    refine ⟨811422669461037615332617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1081896892614716820443489 811422669461037615332617)
                    ·
                      refine ⟨608567002095778211499463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811422669461037615332617 608567002095778211499463)
                      ·
                        rfl

theorem cell23_1185180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1185180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185180 prefixEnd_1185180 := by exact prefixLift 1185180
  have htrace : WordTrace (prefixWord ++ tailWord_1185180) baseStart_1185180 baseEnd_1185180 := by
    simpa [prefixWord, tailWord_1185180, baseEnd_1185180] using wordTrace_append hprefix tailTrace_1185180
  have hstable : (prefixWord ++ tailWord_1185180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185180).length < 2 ^ (prefixWord ++ tailWord_1185180).sum := by decide
  have hdescent : baseEnd_1185180 < baseStart_1185180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185189 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 3, 3, 2]
def baseStart_1185189 : Nat := 118140960795 + 1185189 * 2 ^ 59
def prefixEnd_1185189 : Nat := 4983230072969 + 3 ^ 40 * 1185189 * 2
def baseEnd_1185189 : Nat := 608571623421668676286921

theorem tailTrace_1185189 : CollatzResearch.WordTrace tailWord_1185189 prefixEnd_1185189 608571623421668676286921 := by
  unfold tailWord_1185189
  simp only [CollatzResearch.WordTrace]
  refine ⟨43227394103270142011294621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28818262735513428007529747 43227394103270142011294621)
  ·
    refine ⟨16210272788726303254235483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43227394103270142011294621 16210272788726303254235483)
    ·
      refine ⟨24315409183089454881353225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16210272788726303254235483 24315409183089454881353225)
      ·
        refine ⟨18236556887317091161014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24315409183089454881353225 18236556887317091161014919)
        ·
          refine ⟨27354835330975636741522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18236556887317091161014919 27354835330975636741522379)
          ·
            refine ⟨41032252996463455112283569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27354835330975636741522379 41032252996463455112283569)
            ·
              refine ⟨30774189747347591334212677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41032252996463455112283569 30774189747347591334212677)
              ·
                refine ⟨5770160577627673375164877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30774189747347591334212677 5770160577627673375164877)
                ·
                  refine ⟨2163810216610377515686829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5770160577627673375164877 2163810216610377515686829)
                  ·
                    refine ⟨811428831228891568382561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2163810216610377515686829 811428831228891568382561)
                    ·
                      refine ⟨608571623421668676286921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811428831228891568382561 608571623421668676286921)
                      ·
                        rfl

theorem cell23_1185189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_1185189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185189 prefixEnd_1185189 := by exact prefixLift 1185189
  have htrace : WordTrace (prefixWord ++ tailWord_1185189) baseStart_1185189 baseEnd_1185189 := by
    simpa [prefixWord, tailWord_1185189, baseEnd_1185189] using wordTrace_append hprefix tailTrace_1185189
  have hstable : (prefixWord ++ tailWord_1185189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185189).length < 2 ^ (prefixWord ++ tailWord_1185189).sum := by decide
  have hdescent : baseEnd_1185189 < baseStart_1185189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185195 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 8]
def baseStart_1185195 : Nat := 118140960795 + 1185195 * 2 ^ 59
def prefixEnd_1185195 : Nat := 4983230072969 + 3 ^ 40 * 1185195 * 2
def baseEnd_1185195 : Nat := 202858234768531884270631

theorem tailTrace_1185195 : CollatzResearch.WordTrace tailWord_1185195 prefixEnd_1185195 202858234768531884270631 := by
  unfold tailWord_1185195
  simp only [CollatzResearch.WordTrace]
  refine ⟨43227612941248405036013039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28818408627498936690675359 43227612941248405036013039)
  ·
    refine ⟨64841419411872607554019559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43227612941248405036013039 64841419411872607554019559)
    ·
      refine ⟨97262129117808911331029339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64841419411872607554019559 97262129117808911331029339)
      ·
        refine ⟨145893193676713366996544009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97262129117808911331029339 145893193676713366996544009)
        ·
          refine ⟨109419895257535025247408007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145893193676713366996544009 109419895257535025247408007)
          ·
            refine ⟨164129842886302537871112011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109419895257535025247408007 164129842886302537871112011)
            ·
              refine ⟨246194764329453806806668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164129842886302537871112011 246194764329453806806668017)
              ·
                refine ⟨184646073247090355105001013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246194764329453806806668017 184646073247090355105001013)
                ·
                  refine ⟨17310569366914720791093845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184646073247090355105001013 17310569366914720791093845)
                  ·
                    refine ⟨202858234768531884270631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17310569366914720791093845 202858234768531884270631)
                    ·
                      rfl

theorem cell23_1185195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 8].length) (baseStart_1185195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185195 prefixEnd_1185195 := by exact prefixLift 1185195
  have htrace : WordTrace (prefixWord ++ tailWord_1185195) baseStart_1185195 baseEnd_1185195 := by
    simpa [prefixWord, tailWord_1185195, baseEnd_1185195] using wordTrace_append hprefix tailTrace_1185195
  have hstable : (prefixWord ++ tailWord_1185195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185195).length < 2 ^ (prefixWord ++ tailWord_1185195).sum := by decide
  have hdescent : baseEnd_1185195 < baseStart_1185195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185219 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 1, 4, 2]
def baseStart_1185219 : Nat := 118140960795 + 1185219 * 2 ^ 59
def prefixEnd_1185219 : Nat := 4983230072969 + 3 ^ 40 * 1185219 * 2
def baseEnd_1185219 : Nat := 608587027841303558911783

theorem tailTrace_1185219 : CollatzResearch.WordTrace tailWord_1185219 prefixEnd_1185219 608587027841303558911783 := by
  unfold tailWord_1185219
  simp only [CollatzResearch.WordTrace]
  refine ⟨43228488293161457134886711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28818992195440971423257807 43228488293161457134886711)
  ·
    refine ⟨64842732439742185702330067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43228488293161457134886711 64842732439742185702330067)
    ·
      refine ⟨97264098659613278553495101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64842732439742185702330067 97264098659613278553495101)
      ·
        refine ⟨36474036997354979457560663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97264098659613278553495101 36474036997354979457560663)
        ·
          refine ⟨54711055496032469186340995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36474036997354979457560663 54711055496032469186340995)
          ·
            refine ⟨82066583244048703779511493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54711055496032469186340995 82066583244048703779511493)
            ·
              refine ⟨15387484358259131958658405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82066583244048703779511493 15387484358259131958658405)
              ·
                refine ⟨2885153317173587242248451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15387484358259131958658405 2885153317173587242248451)
                ·
                  refine ⟨4327729975760380863372677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885153317173587242248451 4327729975760380863372677)
                  ·
                    refine ⟨811449370455071411882377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4327729975760380863372677 811449370455071411882377)
                    ·
                      refine ⟨608587027841303558911783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811449370455071411882377 608587027841303558911783)
                      ·
                        rfl

theorem cell23_1185219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_1185219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185219 prefixEnd_1185219 := by exact prefixLift 1185219
  have htrace : WordTrace (prefixWord ++ tailWord_1185219) baseStart_1185219 baseEnd_1185219 := by
    simpa [prefixWord, tailWord_1185219, baseEnd_1185219] using wordTrace_append hprefix tailTrace_1185219
  have hstable : (prefixWord ++ tailWord_1185219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185219).length < 2 ^ (prefixWord ++ tailWord_1185219).sum := by decide
  have hdescent : baseEnd_1185219 < baseStart_1185219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185309 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1185309 : Nat := 118140960795 + 1185309 * 2 ^ 59
def prefixEnd_1185309 : Nat := 4983230072969 + 3 ^ 40 * 1185309 * 2
def baseEnd_1185309 : Nat := 608633241100208206786369

theorem tailTrace_1185309 : CollatzResearch.WordTrace tailWord_1185309 prefixEnd_1185309 608633241100208206786369 := by
  unfold tailWord_1185309
  simp only [CollatzResearch.WordTrace]
  refine ⟨43231770862835402505662981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28821180575223601670441987 43231770862835402505662981)
  ·
    refine ⟨8105957036781637969811809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43231770862835402505662981 8105957036781637969811809)
    ·
      refine ⟨6079467777586228477358857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8105957036781637969811809 6079467777586228477358857)
      ·
        refine ⟨4559600833189671358019143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6079467777586228477358857 4559600833189671358019143)
        ·
          refine ⟨6839401249784507037028715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559600833189671358019143 6839401249784507037028715)
          ·
            refine ⟨10259101874676760555543073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6839401249784507037028715 10259101874676760555543073)
            ·
              refine ⟨7694326406007570416657305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10259101874676760555543073 7694326406007570416657305)
              ·
                refine ⟨5770744804505677812492979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7694326406007570416657305 5770744804505677812492979)
                ·
                  refine ⟨8656117206758516718739469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770744804505677812492979 8656117206758516718739469)
                  ·
                    refine ⟨3246043952534443769527301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8656117206758516718739469 3246043952534443769527301)
                    ·
                      refine ⟨608633241100208206786369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3246043952534443769527301 608633241100208206786369)
                      ·
                        rfl

theorem cell23_1185309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1185309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185309 prefixEnd_1185309 := by exact prefixLift 1185309
  have htrace : WordTrace (prefixWord ++ tailWord_1185309) baseStart_1185309 baseEnd_1185309 := by
    simpa [prefixWord, tailWord_1185309, baseEnd_1185309] using wordTrace_append hprefix tailTrace_1185309
  have hstable : (prefixWord ++ tailWord_1185309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185309).length < 2 ^ (prefixWord ++ tailWord_1185309).sum := by decide
  have hdescent : baseEnd_1185309 < baseStart_1185309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185310 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1185310 : Nat := 118140960795 + 1185310 * 2 ^ 59
def prefixEnd_1185310 : Nat := 4983230072969 + 3 ^ 40 * 1185310 * 2
def baseEnd_1185310 : Nat := 67625972731206966985985

theorem tailTrace_1185310 : CollatzResearch.WordTrace tailWord_1185310 prefixEnd_1185310 67625972731206966985985 := by
  unfold tailWord_1185310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403975916978972459556173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28821204890554519784299589 5403975916978972459556173)
  ·
    refine ⟨2026490968867114672333565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5403975916978972459556173 2026490968867114672333565)
    ·
      refine ⟨759934113325168002125087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2026490968867114672333565 759934113325168002125087)
      ·
        refine ⟨1139901169987752003187631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759934113325168002125087 1139901169987752003187631)
        ·
          refine ⟨1709851754981628004781447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139901169987752003187631 1709851754981628004781447)
          ·
            refine ⟨2564777632472442007172171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709851754981628004781447 2564777632472442007172171)
            ·
              refine ⟨3847166448708663010758257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564777632472442007172171 3847166448708663010758257)
              ·
                refine ⟨2885374836531497258068693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847166448708663010758257 2885374836531497258068693)
                ·
                  refine ⟨67625972731206966985985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2885374836531497258068693 67625972731206966985985)
                  ·
                    rfl

theorem cell23_1185310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1185310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185310 prefixEnd_1185310 := by exact prefixLift 1185310
  have htrace : WordTrace (prefixWord ++ tailWord_1185310) baseStart_1185310 baseEnd_1185310 := by
    simpa [prefixWord, tailWord_1185310, baseEnd_1185310] using wordTrace_append hprefix tailTrace_1185310
  have hstable : (prefixWord ++ tailWord_1185310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185310).length < 2 ^ (prefixWord ++ tailWord_1185310).sum := by decide
  have hdescent : baseEnd_1185310 < baseStart_1185310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185326 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1185326 : Nat := 118140960795 + 1185326 * 2 ^ 59
def prefixEnd_1185326 : Nat := 4983230072969 + 3 ^ 40 * 1185326 * 2
def baseEnd_1185326 : Nat := 608641970271334640273791

theorem tailTrace_1185326 : CollatzResearch.WordTrace tailWord_1185326 prefixEnd_1185326 608641970271334640273791 := by
  unfold tailWord_1185326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5404048862971726801128979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28821593935849209606021221 5404048862971726801128979)
  ·
    refine ⟨8106073294457590201693469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5404048862971726801128979 8106073294457590201693469)
    ·
      refine ⟨3039777485421596325635051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8106073294457590201693469 3039777485421596325635051)
      ·
        refine ⟨4559666228132394488452577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039777485421596325635051 4559666228132394488452577)
        ·
          refine ⟨3419749671099295866339433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4559666228132394488452577 3419749671099295866339433)
          ·
            refine ⟨2564812253324471899754575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419749671099295866339433 2564812253324471899754575)
            ·
              refine ⟨3847218379986707849631863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564812253324471899754575 3847218379986707849631863)
              ·
                refine ⟨5770827569980061774447795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847218379986707849631863 5770827569980061774447795)
                ·
                  refine ⟨8656241354970092661671693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770827569980061774447795 8656241354970092661671693)
                  ·
                    refine ⟨3246090508113784748126885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8656241354970092661671693 3246090508113784748126885)
                    ·
                      refine ⟨608641970271334640273791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3246090508113784748126885 608641970271334640273791)
                      ·
                        rfl

theorem cell23_1185326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1185326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185326 prefixEnd_1185326 := by exact prefixLift 1185326
  have htrace : WordTrace (prefixWord ++ tailWord_1185326) baseStart_1185326 baseEnd_1185326 := by
    simpa [prefixWord, tailWord_1185326, baseEnd_1185326] using wordTrace_append hprefix tailTrace_1185326
  have hstable : (prefixWord ++ tailWord_1185326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185326).length < 2 ^ (prefixWord ++ tailWord_1185326).sum := by decide
  have hdescent : baseEnd_1185326 < baseStart_1185326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185399 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_1185399 : Nat := 118140960795 + 1185399 * 2 ^ 59
def prefixEnd_1185399 : Nat := 4983230072969 + 3 ^ 40 * 1185399 * 2
def baseEnd_1185399 : Nat := 608679454359112854660955

theorem tailTrace_1185399 : CollatzResearch.WordTrace tailWord_1185399 prefixEnd_1185399 608679454359112854660955 := by
  unfold tailWord_1185399
  simp only [CollatzResearch.WordTrace]
  refine ⟨43235053432509347876439251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28823368955006231917626167 43235053432509347876439251)
  ·
    refine ⟨64852580148764021814658877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43235053432509347876439251 64852580148764021814658877)
    ·
      refine ⟨24319717555786508180497079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64852580148764021814658877 24319717555786508180497079)
      ·
        refine ⟨36479576333679762270745619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24319717555786508180497079 36479576333679762270745619)
        ·
          refine ⟨54719364500519643406118429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36479576333679762270745619 54719364500519643406118429)
          ·
            refine ⟨20519761687694866277294411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54719364500519643406118429 20519761687694866277294411)
            ·
              refine ⟨30779642531542299415941617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20519761687694866277294411 30779642531542299415941617)
              ·
                refine ⟨23084731898656724561956213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30779642531542299415941617 23084731898656724561956213)
                ·
                  refine ⟨2164193615499067927683395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23084731898656724561956213 2164193615499067927683395)
                  ·
                    refine ⟨3246290423248601891525093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2164193615499067927683395 3246290423248601891525093)
                    ·
                      refine ⟨608679454359112854660955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3246290423248601891525093 608679454359112854660955)
                      ·
                        rfl

theorem cell23_1185399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_1185399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185399 prefixEnd_1185399 := by exact prefixLift 1185399
  have htrace : WordTrace (prefixWord ++ tailWord_1185399) baseStart_1185399 baseEnd_1185399 := by
    simpa [prefixWord, tailWord_1185399, baseEnd_1185399] using wordTrace_append hprefix tailTrace_1185399
  have hstable : (prefixWord ++ tailWord_1185399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185399).length < 2 ^ (prefixWord ++ tailWord_1185399).sum := by decide
  have hdescent : baseEnd_1185399 < baseStart_1185399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185419 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5]
def baseStart_1185419 : Nat := 118140960795 + 1185419 * 2 ^ 59
def prefixEnd_1185419 : Nat := 4983230072969 + 3 ^ 40 * 1185419 * 2
def baseEnd_1185419 : Nat := 608689723972202776410863

theorem tailTrace_1185419 : CollatzResearch.WordTrace tailWord_1185419 prefixEnd_1185419 608689723972202776410863 := by
  unfold tailWord_1185419
  simp only [CollatzResearch.WordTrace]
  refine ⟨43235782892436891292167311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28823855261624594194778207 43235782892436891292167311)
  ·
    refine ⟨64853674338655336938250967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43235782892436891292167311 64853674338655336938250967)
    ·
      refine ⟨97280511507983005407376451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64853674338655336938250967 97280511507983005407376451)
      ·
        refine ⟨145920767261974508111064677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97280511507983005407376451 145920767261974508111064677)
        ·
          refine ⟨27360143861620220270824627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145920767261974508111064677 27360143861620220270824627)
          ·
            refine ⟨41040215792430330406236941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27360143861620220270824627 41040215792430330406236941)
            ·
              refine ⟨15390080922161373902338853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41040215792430330406236941 15390080922161373902338853)
              ·
                refine ⟨2885640172905257606688535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15390080922161373902338853 2885640172905257606688535)
                ·
                  refine ⟨4328460259357886410032803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885640172905257606688535 4328460259357886410032803)
                  ·
                    refine ⟨6492690389036829615049205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4328460259357886410032803 6492690389036829615049205)
                    ·
                      refine ⟨608689723972202776410863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6492690389036829615049205 608689723972202776410863)
                      ·
                        rfl

theorem cell23_1185419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 5].length) (baseStart_1185419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185419 prefixEnd_1185419 := by exact prefixLift 1185419
  have htrace : WordTrace (prefixWord ++ tailWord_1185419) baseStart_1185419 baseEnd_1185419 := by
    simpa [prefixWord, tailWord_1185419, baseEnd_1185419] using wordTrace_append hprefix tailTrace_1185419
  have hstable : (prefixWord ++ tailWord_1185419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185419).length < 2 ^ (prefixWord ++ tailWord_1185419).sum := by decide
  have hdescent : baseEnd_1185419 < baseStart_1185419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185429 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1185429 : Nat := 118140960795 + 1185429 * 2 ^ 59
def prefixEnd_1185429 : Nat := 4983230072969 + 3 ^ 40 * 1185429 * 2
def baseEnd_1185429 : Nat := 608694858778747737285817

theorem tailTrace_1185429 : CollatzResearch.WordTrace tailWord_1185429 prefixEnd_1185429 608694858778747737285817 := by
  unfold tailWord_1185429
  simp only [CollatzResearch.WordTrace]
  refine ⟨43236147622400663000031341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28824098414933775333354227 43236147622400663000031341)
  ·
    refine ⟨16213555358400248625011753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43236147622400663000031341 16213555358400248625011753)
    ·
      refine ⟨12160166518800186468758815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16213555358400248625011753 12160166518800186468758815)
      ·
        refine ⟨18240249778200279703138223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12160166518800186468758815 18240249778200279703138223)
        ·
          refine ⟨27360374667300419554707335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18240249778200279703138223 27360374667300419554707335)
          ·
            refine ⟨41040562000950629332061003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27360374667300419554707335 41040562000950629332061003)
            ·
              refine ⟨61560843001425943998091505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41040562000950629332061003 61560843001425943998091505)
              ·
                refine ⟨46170632251069457998568629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61560843001425943998091505 46170632251069457998568629)
                ·
                  refine ⟨4328496773537761687365809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46170632251069457998568629 4328496773537761687365809)
                  ·
                    refine ⟨3246372580153321265524357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4328496773537761687365809 3246372580153321265524357)
                    ·
                      refine ⟨608694858778747737285817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3246372580153321265524357 608694858778747737285817)
                      ·
                        rfl

theorem cell23_1185429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1185429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185429 prefixEnd_1185429 := by exact prefixLift 1185429
  have htrace : WordTrace (prefixWord ++ tailWord_1185429) baseStart_1185429 baseEnd_1185429 := by
    simpa [prefixWord, tailWord_1185429, baseEnd_1185429] using wordTrace_append hprefix tailTrace_1185429
  have hstable : (prefixWord ++ tailWord_1185429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185429).length < 2 ^ (prefixWord ++ tailWord_1185429).sum := by decide
  have hdescent : baseEnd_1185429 < baseStart_1185429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185449 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_1185449 : Nat := 118140960795 + 1185449 * 2 ^ 59
def prefixEnd_1185449 : Nat := 4983230072969 + 3 ^ 40 * 1185449 * 2
def baseEnd_1185449 : Nat := 608705128391837659035725

theorem tailTrace_1185449 : CollatzResearch.WordTrace tailWord_1185449 prefixEnd_1185449 608705128391837659035725 := by
  unfold tailWord_1185449
  simp only [CollatzResearch.WordTrace]
  refine ⟨43236877082328206415759401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28824584721552137610506267 43236877082328206415759401)
  ·
    refine ⟨32427657811746154811819551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43236877082328206415759401 32427657811746154811819551)
    ·
      refine ⟨48641486717619232217729327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32427657811746154811819551 48641486717619232217729327)
      ·
        refine ⟨72962230076428848326593991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48641486717619232217729327 72962230076428848326593991)
        ·
          refine ⟨109443345114643272489890987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72962230076428848326593991 109443345114643272489890987)
          ·
            refine ⟨164165017671964908734836481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109443345114643272489890987 164165017671964908734836481)
            ·
              refine ⟨123123763253973681551127361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164165017671964908734836481 123123763253973681551127361)
              ·
                refine ⟨92342822440480261163345521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123123763253973681551127361 92342822440480261163345521)
                ·
                  refine ⟨69257116830360195872509141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92342822440480261163345521 69257116830360195872509141)
                  ·
                    refine ⟨1623213675711567090761933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 69257116830360195872509141 1623213675711567090761933)
                    ·
                      refine ⟨608705128391837659035725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623213675711567090761933 608705128391837659035725)
                      ·
                        rfl

theorem cell23_1185449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_1185449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185449 prefixEnd_1185449 := by exact prefixLift 1185449
  have htrace : WordTrace (prefixWord ++ tailWord_1185449) baseStart_1185449 baseEnd_1185449 := by
    simpa [prefixWord, tailWord_1185449, baseEnd_1185449] using wordTrace_append hprefix tailTrace_1185449
  have hstable : (prefixWord ++ tailWord_1185449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185449).length < 2 ^ (prefixWord ++ tailWord_1185449).sum := by decide
  have hdescent : baseEnd_1185449 < baseStart_1185449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185461 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_1185461 : Nat := 118140960795 + 1185461 * 2 ^ 59
def prefixEnd_1185461 : Nat := 4983230072969 + 3 ^ 40 * 1185461 * 2
def baseEnd_1185461 : Nat := 608711290159691612085671

theorem tailTrace_1185461 : CollatzResearch.WordTrace tailWord_1185461 prefixEnd_1185461 608711290159691612085671 := by
  unfold tailWord_1185461
  simp only [CollatzResearch.WordTrace]
  refine ⟨43237314758284732465196237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28824876505523154976797491 43237314758284732465196237)
  ·
    refine ⟨16213993034356774674448589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43237314758284732465196237 16213993034356774674448589)
    ·
      refine ⟨6080247387883790502918221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16213993034356774674448589 6080247387883790502918221)
      ·
        refine ⟨2280092770456421438594333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6080247387883790502918221 2280092770456421438594333)
        ·
          refine ⟨855034788921158039472875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2280092770456421438594333 855034788921158039472875)
          ·
            refine ⟨1282552183381737059209313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855034788921158039472875 1282552183381737059209313)
            ·
              refine ⟨961914137536302794406985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282552183381737059209313 961914137536302794406985)
              ·
                refine ⟨721435603152227095805239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961914137536302794406985 721435603152227095805239)
                ·
                  refine ⟨1082153404728340643707859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721435603152227095805239 1082153404728340643707859)
                  ·
                    refine ⟨1623230107092510965561789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1082153404728340643707859 1623230107092510965561789)
                    ·
                      refine ⟨608711290159691612085671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623230107092510965561789 608711290159691612085671)
                      ·
                        rfl

theorem cell23_1185461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_1185461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185461 prefixEnd_1185461 := by exact prefixLift 1185461
  have htrace : WordTrace (prefixWord ++ tailWord_1185461) baseStart_1185461 baseEnd_1185461 := by
    simpa [prefixWord, tailWord_1185461, baseEnd_1185461] using wordTrace_append hprefix tailTrace_1185461
  have hstable : (prefixWord ++ tailWord_1185461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185461).length < 2 ^ (prefixWord ++ tailWord_1185461).sum := by decide
  have hdescent : baseEnd_1185461 < baseStart_1185461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185469 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1185469 : Nat := 118140960795 + 1185469 * 2 ^ 59
def prefixEnd_1185469 : Nat := 4983230072969 + 3 ^ 40 * 1185469 * 2
def baseEnd_1185469 : Nat := 202905132668309193595211

theorem tailTrace_1185469 : CollatzResearch.WordTrace tailWord_1185469 prefixEnd_1185469 202905132668309193595211 := by
  unfold tailWord_1185469
  simp only [CollatzResearch.WordTrace]
  refine ⟨43237606542255749831487461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28825071028170499887658307 43237606542255749831487461)
  ·
    refine ⟨8107051226672953093403899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43237606542255749831487461 8107051226672953093403899)
    ·
      refine ⟨12160576840009429640105849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8107051226672953093403899 12160576840009429640105849)
      ·
        refine ⟨9120432630007072230079387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12160576840009429640105849 9120432630007072230079387)
        ·
          refine ⟨13680648945010608345119081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9120432630007072230079387 13680648945010608345119081)
          ·
            refine ⟨10260486708757956258839311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13680648945010608345119081 10260486708757956258839311)
            ·
              refine ⟨15390730063136934388258967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10260486708757956258839311 15390730063136934388258967)
              ·
                refine ⟨23086095094705401582388451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15390730063136934388258967 23086095094705401582388451)
                ·
                  refine ⟨34629142642058102373582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23086095094705401582388451 34629142642058102373582677)
                  ·
                    refine ⟨202905132668309193595211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34629142642058102373582677 202905132668309193595211)
                    ·
                      rfl

theorem cell23_1185469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1185469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185469 prefixEnd_1185469 := by exact prefixLift 1185469
  have htrace : WordTrace (prefixWord ++ tailWord_1185469) baseStart_1185469 baseEnd_1185469 := by
    simpa [prefixWord, tailWord_1185469, baseEnd_1185469] using wordTrace_append hprefix tailTrace_1185469
  have hstable : (prefixWord ++ tailWord_1185469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185469).length < 2 ^ (prefixWord ++ tailWord_1185469).sum := by decide
  have hdescent : baseEnd_1185469 < baseStart_1185469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185501 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1185501 : Nat := 118140960795 + 1185501 * 2 ^ 59
def prefixEnd_1185501 : Nat := 4983230072969 + 3 ^ 40 * 1185501 * 2
def baseEnd_1185501 : Nat := 608731829385871455585487

theorem tailTrace_1185501 : CollatzResearch.WordTrace tailWord_1185501 prefixEnd_1185501 608731829385871455585487 := by
  unfold tailWord_1185501
  simp only [CollatzResearch.WordTrace]
  refine ⟨43238773678139819296652357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28825849118759879531101571 43238773678139819296652357)
  ·
    refine ⟨8107270064651216118122317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43238773678139819296652357 8107270064651216118122317)
    ·
      refine ⟨3040226274244206044295869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8107270064651216118122317 3040226274244206044295869)
      ·
        refine ⟨1140084852841577266610951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3040226274244206044295869 1140084852841577266610951)
        ·
          refine ⟨1710127279262365899916427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140084852841577266610951 1710127279262365899916427)
          ·
            refine ⟨2565190918893548849874641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710127279262365899916427 2565190918893548849874641)
            ·
              refine ⟨1923893189170161637405981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2565190918893548849874641 1923893189170161637405981)
              ·
                refine ⟨721459945938810614027243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1923893189170161637405981 721459945938810614027243)
                ·
                  refine ⟨1082189918908215921040865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721459945938810614027243 1082189918908215921040865)
                  ·
                    refine ⟨811642439181161940780649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1082189918908215921040865 811642439181161940780649)
                    ·
                      refine ⟨608731829385871455585487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811642439181161940780649 608731829385871455585487)
                      ·
                        rfl

theorem cell23_1185501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1185501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185501 prefixEnd_1185501 := by exact prefixLift 1185501
  have htrace : WordTrace (prefixWord ++ tailWord_1185501) baseStart_1185501 baseEnd_1185501 := by
    simpa [prefixWord, tailWord_1185501, baseEnd_1185501] using wordTrace_append hprefix tailTrace_1185501
  have hstable : (prefixWord ++ tailWord_1185501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185501).length < 2 ^ (prefixWord ++ tailWord_1185501).sum := by decide
  have hdescent : baseEnd_1185501 < baseStart_1185501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185517 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1185517 : Nat := 118140960795 + 1185517 * 2 ^ 59
def prefixEnd_1185517 : Nat := 4983230072969 + 3 ^ 40 * 1185517 * 2
def baseEnd_1185517 : Nat := 608740045076343392985413

theorem tailTrace_1185517 : CollatzResearch.WordTrace tailWord_1185517 prefixEnd_1185517 608740045076343392985413 := by
  unfold tailWord_1185517
  simp only [CollatzResearch.WordTrace]
  refine ⟨43239357246081854029234805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28826238164054569352823203 43239357246081854029234805)
  ·
    refine ⟨4053689741820173815240763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43239357246081854029234805 4053689741820173815240763)
    ·
      refine ⟨6080534612730260722861145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4053689741820173815240763 6080534612730260722861145)
      ·
        refine ⟨4560400959547695542145859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6080534612730260722861145 4560400959547695542145859)
        ·
          refine ⟨6840601439321543313218789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560400959547695542145859 6840601439321543313218789)
          ·
            refine ⟨1282612769872789371228523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6840601439321543313218789 1282612769872789371228523)
            ·
              refine ⟨1923919154809184056842785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282612769872789371228523 1923919154809184056842785)
              ·
                refine ⟨1442939366106888042632089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923919154809184056842785 1442939366106888042632089)
                ·
                  refine ⟨1082204524580166031974067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1442939366106888042632089 1082204524580166031974067)
                  ·
                    refine ⟨1623306786870249047961101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1082204524580166031974067 1623306786870249047961101)
                    ·
                      refine ⟨608740045076343392985413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623306786870249047961101 608740045076343392985413)
                      ·
                        rfl

theorem cell23_1185517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1185517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185517 prefixEnd_1185517 := by exact prefixLift 1185517
  have htrace : WordTrace (prefixWord ++ tailWord_1185517) baseStart_1185517 baseEnd_1185517 := by
    simpa [prefixWord, tailWord_1185517, baseEnd_1185517] using wordTrace_append hprefix tailTrace_1185517
  have hstable : (prefixWord ++ tailWord_1185517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185517).length < 2 ^ (prefixWord ++ tailWord_1185517).sum := by decide
  have hdescent : baseEnd_1185517 < baseStart_1185517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185534 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_1185534 : Nat := 118140960795 + 1185534 * 2 ^ 59
def prefixEnd_1185534 : Nat := 4983230072969 + 3 ^ 40 * 1185534 * 2
def baseEnd_1185534 : Nat := 608748774247469826472835

theorem tailTrace_1185534 : CollatzResearch.WordTrace tailWord_1185534 prefixEnd_1185534 608748774247469826472835 := by
  unfold tailWord_1185534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5404997160877533241575457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28826651524680177288402437 5404997160877533241575457)
  ·
    refine ⟨4053747870658149931181593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5404997160877533241575457 4053747870658149931181593)
    ·
      refine ⟨3040310902993612448386195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4053747870658149931181593 3040310902993612448386195)
      ·
        refine ⟨4560466354490418672579293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040310902993612448386195 4560466354490418672579293)
        ·
          refine ⟨1710174882933907002217235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4560466354490418672579293 1710174882933907002217235)
          ·
            refine ⟨2565262324400860503325853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710174882933907002217235 2565262324400860503325853)
            ·
              refine ⟨961973371650322688747195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565262324400860503325853 961973371650322688747195)
              ·
                refine ⟨1442960057475484033120793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961973371650322688747195 1442960057475484033120793)
                ·
                  refine ⟨1082220043106613024840595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1442960057475484033120793 1082220043106613024840595)
                  ·
                    refine ⟨1623330064659919537260893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1082220043106613024840595 1623330064659919537260893)
                    ·
                      refine ⟨608748774247469826472835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623330064659919537260893 608748774247469826472835)
                      ·
                        rfl

theorem cell23_1185534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_1185534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185534 prefixEnd_1185534 := by exact prefixLift 1185534
  have htrace : WordTrace (prefixWord ++ tailWord_1185534) baseStart_1185534 baseEnd_1185534 := by
    simpa [prefixWord, tailWord_1185534, baseEnd_1185534] using wordTrace_append hprefix tailTrace_1185534
  have hstable : (prefixWord ++ tailWord_1185534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185534).length < 2 ^ (prefixWord ++ tailWord_1185534).sum := by decide
  have hdescent : baseEnd_1185534 < baseStart_1185534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185540 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_1185540 : Nat := 118140960795 + 1185540 * 2 ^ 59
def prefixEnd_1185540 : Nat := 4983230072969 + 3 ^ 40 * 1185540 * 2
def baseEnd_1185540 : Nat := 608751855131396802997807

theorem tailTrace_1185540 : CollatzResearch.WordTrace tailWord_1185540 prefixEnd_1185540 608751855131396802997807 := by
  unfold tailWord_1185540
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620098062499264478661037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28826797416665685971548049 21620098062499264478661037)
  ·
    refine ⟨8107536773437224179497889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21620098062499264478661037 8107536773437224179497889)
    ·
      refine ⟨6080652580077918134623417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8107536773437224179497889 6080652580077918134623417)
      ·
        refine ⟨4560489435058438600967563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6080652580077918134623417 4560489435058438600967563)
        ·
          refine ⟨6840734152587657901451345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560489435058438600967563 6840734152587657901451345)
          ·
            refine ⟨5130550614440743426088509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6840734152587657901451345 5130550614440743426088509)
            ·
              refine ⟨1923956480415278784783191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5130550614440743426088509 1923956480415278784783191)
              ·
                refine ⟨2885934720622918177174787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923956480415278784783191 2885934720622918177174787)
                ·
                  refine ⟨4328902080934377265762181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885934720622918177174787 4328902080934377265762181)
                  ·
                    refine ⟨811669140175195737330409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4328902080934377265762181 811669140175195737330409)
                    ·
                      refine ⟨608751855131396802997807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811669140175195737330409 608751855131396802997807)
                      ·
                        rfl

theorem cell23_1185540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_1185540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185540 prefixEnd_1185540 := by exact prefixLift 1185540
  have htrace : WordTrace (prefixWord ++ tailWord_1185540) baseStart_1185540 baseEnd_1185540 := by
    simpa [prefixWord, tailWord_1185540, baseEnd_1185540] using wordTrace_append hprefix tailTrace_1185540
  have hstable : (prefixWord ++ tailWord_1185540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185540).length < 2 ^ (prefixWord ++ tailWord_1185540).sum := by decide
  have hdescent : baseEnd_1185540 < baseStart_1185540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185546 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_1185546 : Nat := 118140960795 + 1185546 * 2 ^ 59
def prefixEnd_1185546 : Nat := 4983230072969 + 3 ^ 40 * 1185546 * 2
def baseEnd_1185546 : Nat := 67639437335035975502531

theorem tailTrace_1185546 : CollatzResearch.WordTrace tailWord_1185546 prefixEnd_1185546 67639437335035975502531 := by
  unfold tailWord_1185546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810103740744197995510123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28826943308651194654693661 10810103740744197995510123)
  ·
    refine ⟨16215155611116296993265185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10810103740744197995510123 16215155611116296993265185)
    ·
      refine ⟨12161366708337222744948889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16215155611116296993265185 12161366708337222744948889)
      ·
        refine ⟨9121025031252917058711667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12161366708337222744948889 9121025031252917058711667)
        ·
          refine ⟨13681537546879375588067501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9121025031252917058711667 13681537546879375588067501)
          ·
            refine ⟨5130576580079765845525313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13681537546879375588067501 5130576580079765845525313)
            ·
              refine ⟨3847932435059824384143985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5130576580079765845525313 3847932435059824384143985)
              ·
                refine ⟨2885949326294868288107989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847932435059824384143985 2885949326294868288107989)
                ·
                  refine ⟨67639437335035975502531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2885949326294868288107989 67639437335035975502531)
                  ·
                    rfl

theorem cell23_1185546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_1185546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185546 prefixEnd_1185546 := by exact prefixLift 1185546
  have htrace : WordTrace (prefixWord ++ tailWord_1185546) baseStart_1185546 baseEnd_1185546 := by
    simpa [prefixWord, tailWord_1185546, baseEnd_1185546] using wordTrace_append hprefix tailTrace_1185546
  have hstable : (prefixWord ++ tailWord_1185546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185546).length < 2 ^ (prefixWord ++ tailWord_1185546).sum := by decide
  have hdescent : baseEnd_1185546 < baseStart_1185546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185580 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 5]
def baseStart_1185580 : Nat := 118140960795 + 1185580 * 2 ^ 59
def prefixEnd_1185580 : Nat := 4983230072969 + 3 ^ 40 * 1185580 * 2
def baseEnd_1185580 : Nat := 67641377150841849610847

theorem tailTrace_1185580 : CollatzResearch.WordTrace tailWord_1185580 prefixEnd_1185580 67641377150841849610847 := by
  unfold tailWord_1185580
  simp only [CollatzResearch.WordTrace]
  refine ⟨21620827522426807894389097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28827770029902410525852129 21620827522426807894389097)
  ·
    refine ⟨16215620641820105920791823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21620827522426807894389097 16215620641820105920791823)
    ·
      refine ⟨24323430962730158881187735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16215620641820105920791823 24323430962730158881187735)
      ·
        refine ⟨36485146444095238321781603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24323430962730158881187735 36485146444095238321781603)
        ·
          refine ⟨54727719666142857482672405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36485146444095238321781603 54727719666142857482672405)
          ·
            refine ⟨2565361859350446444500269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54727719666142857482672405 2565361859350446444500269)
            ·
              refine ⟨962010697256417416687601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565361859350446444500269 962010697256417416687601)
              ·
                refine ⟨721508022942313062515701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962010697256417416687601 721508022942313062515701)
                ·
                  refine ⟨67641377150841849610847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 721508022942313062515701 67641377150841849610847)
                  ·
                    rfl

theorem cell23_1185580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_1185580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185580 prefixEnd_1185580 := by exact prefixLift 1185580
  have htrace : WordTrace (prefixWord ++ tailWord_1185580) baseStart_1185580 baseEnd_1185580 := by
    simpa [prefixWord, tailWord_1185580, baseEnd_1185580] using wordTrace_append hprefix tailTrace_1185580
  have hstable : (prefixWord ++ tailWord_1185580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185580).length < 2 ^ (prefixWord ++ tailWord_1185580).sum := by decide
  have hdescent : baseEnd_1185580 < baseStart_1185580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185586 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1185586 : Nat := 118140960795 + 1185586 * 2 ^ 59
def prefixEnd_1185586 : Nat := 4983230072969 + 3 ^ 40 * 1185586 * 2
def baseEnd_1185586 : Nat := 608775475241503623022595

theorem tailTrace_1185586 : CollatzResearch.WordTrace tailWord_1185586 prefixEnd_1185586 608775475241503623022595 := by
  unfold tailWord_1185586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810468470707969703374153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28827915921887919208997741 10810468470707969703374153)
  ·
    refine ⟨8107851353030977277530615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10810468470707969703374153 8107851353030977277530615)
    ·
      refine ⟨12161777029546465916295923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8107851353030977277530615 12161777029546465916295923)
      ·
        refine ⟨18242665544319698874443885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161777029546465916295923 18242665544319698874443885)
        ·
          refine ⟨6840999579119887077916457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18242665544319698874443885 6840999579119887077916457)
          ·
            refine ⟨5130749684339915308437343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6840999579119887077916457 5130749684339915308437343)
            ·
              refine ⟨7696124526509872962656015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130749684339915308437343 7696124526509872962656015)
              ·
                refine ⟨11544186789764809443984023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696124526509872962656015 11544186789764809443984023)
                ·
                  refine ⟨17316280184647214165976035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11544186789764809443984023 17316280184647214165976035)
                  ·
                    refine ⟨25974420276970821248964053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17316280184647214165976035 25974420276970821248964053)
                    ·
                      refine ⟨608775475241503623022595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25974420276970821248964053 608775475241503623022595)
                      ·
                        rfl

theorem cell23_1185586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1185586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185586 prefixEnd_1185586 := by exact prefixLift 1185586
  have htrace : WordTrace (prefixWord ++ tailWord_1185586) baseStart_1185586 baseEnd_1185586 := by
    simpa [prefixWord, tailWord_1185586, baseEnd_1185586] using wordTrace_append hprefix tailTrace_1185586
  have hstable : (prefixWord ++ tailWord_1185586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185586).length < 2 ^ (prefixWord ++ tailWord_1185586).sum := by decide
  have hdescent : baseEnd_1185586 < baseStart_1185586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185596 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1185596 : Nat := 118140960795 + 1185596 * 2 ^ 59
def prefixEnd_1185596 : Nat := 4983230072969 + 3 ^ 40 * 1185596 * 2
def baseEnd_1185596 : Nat := 608780610048048583897549

theorem tailTrace_1185596 : CollatzResearch.WordTrace tailWord_1185596 prefixEnd_1185596 608780610048048583897549 := by
  unfold tailWord_1185596
  simp only [CollatzResearch.WordTrace]
  refine ⟨21621119306397825260680321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28828159075197100347573761 21621119306397825260680321)
  ·
    refine ⟨16215839479798368945510241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21621119306397825260680321 16215839479798368945510241)
    ·
      refine ⟨12161879609848776709132681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16215839479798368945510241 12161879609848776709132681)
      ·
        refine ⟨9121409707386582531849511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12161879609848776709132681 9121409707386582531849511)
        ·
          refine ⟨13682114561079873797774267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9121409707386582531849511 13682114561079873797774267)
          ·
            refine ⟨20523171841619810696661401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13682114561079873797774267 20523171841619810696661401)
            ·
              refine ⟨15392378881214858022496051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20523171841619810696661401 15392378881214858022496051)
              ·
                refine ⟨23088568321822287033744077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15392378881214858022496051 23088568321822287033744077)
                ·
                  refine ⟨8658213120683357637654029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23088568321822287033744077 8658213120683357637654029)
                  ·
                    refine ⟨3246829920256259114120261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8658213120683357637654029 3246829920256259114120261)
                    ·
                      refine ⟨608780610048048583897549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3246829920256259114120261 608780610048048583897549)
                      ·
                        rfl

theorem cell23_1185596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1185596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185596 prefixEnd_1185596 := by exact prefixLift 1185596
  have htrace : WordTrace (prefixWord ++ tailWord_1185596) baseStart_1185596 baseEnd_1185596 := by
    simpa [prefixWord, tailWord_1185596, baseEnd_1185596] using wordTrace_append hprefix tailTrace_1185596
  have hstable : (prefixWord ++ tailWord_1185596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185596).length < 2 ^ (prefixWord ++ tailWord_1185596).sum := by decide
  have hdescent : baseEnd_1185596 < baseStart_1185596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185626 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1185626 : Nat := 118140960795 + 1185626 * 2 ^ 59
def prefixEnd_1185626 : Nat := 4983230072969 + 3 ^ 40 * 1185626 * 2
def baseEnd_1185626 : Nat := 608796014467683466522411

theorem tailTrace_1185626 : CollatzResearch.WordTrace tailWord_1185626 prefixEnd_1185626 608796014467683466522411 := by
  unfold tailWord_1185626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810833200671741411238183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28828888535124643763301821 10810833200671741411238183)
  ·
    refine ⟨16216249801007612116857275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10810833200671741411238183 16216249801007612116857275)
    ·
      refine ⟨24324374701511418175285913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216249801007612116857275 24324374701511418175285913)
      ·
        refine ⟨18243281026133563631464435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24324374701511418175285913 18243281026133563631464435)
        ·
          refine ⟨27364921539200345447196653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243281026133563631464435 27364921539200345447196653)
          ·
            refine ⟨10261845577200129542698745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27364921539200345447196653 10261845577200129542698745)
            ·
              refine ⟨7696384182900097157024059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10261845577200129542698745 7696384182900097157024059)
              ·
                refine ⟨11544576274350145735536089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7696384182900097157024059 11544576274350145735536089)
                ·
                  refine ⟨8658432205762609301652067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11544576274350145735536089 8658432205762609301652067)
                  ·
                    refine ⟨12987648308643913952478101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8658432205762609301652067 12987648308643913952478101)
                    ·
                      refine ⟨608796014467683466522411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12987648308643913952478101 608796014467683466522411)
                      ·
                        rfl

theorem cell23_1185626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1185626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185626 prefixEnd_1185626 := by exact prefixLift 1185626
  have htrace : WordTrace (prefixWord ++ tailWord_1185626) baseStart_1185626 baseEnd_1185626 := by
    simpa [prefixWord, tailWord_1185626, baseEnd_1185626] using wordTrace_append hprefix tailTrace_1185626
  have hstable : (prefixWord ++ tailWord_1185626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185626).length < 2 ^ (prefixWord ++ tailWord_1185626).sum := by decide
  have hdescent : baseEnd_1185626 < baseStart_1185626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185633 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1185633 : Nat := 118140960795 + 1185633 * 2 ^ 59
def prefixEnd_1185633 : Nat := 4983230072969 + 3 ^ 40 * 1185633 * 2
def baseEnd_1185633 : Nat := 608799608832264939134879

theorem tailTrace_1185633 : CollatzResearch.WordTrace tailWord_1185633 prefixEnd_1185633 608799608832264939134879 := by
  unfold tailWord_1185633
  simp only [CollatzResearch.WordTrace]
  refine ⟨43243588113661605840457553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28829058742441070560305035 43243588113661605840457553)
  ·
    refine ⟨32432691085246204380343165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43243588113661605840457553 32432691085246204380343165)
    ·
      refine ⟨12162259156967326642628687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32432691085246204380343165 12162259156967326642628687)
      ·
        refine ⟨18243388735450989963943031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12162259156967326642628687 18243388735450989963943031)
        ·
          refine ⟨27365083103176484945914547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243388735450989963943031 27365083103176484945914547)
          ·
            refine ⟨41047624654764727418871821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27365083103176484945914547 41047624654764727418871821)
            ·
              refine ⟨15392859245536772782076933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41047624654764727418871821 15392859245536772782076933)
              ·
                refine ⟨2886161108538144896639425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15392859245536772782076933 2886161108538144896639425)
                ·
                  refine ⟨2164620831403608672479569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886161108538144896639425 2164620831403608672479569)
                  ·
                    refine ⟨1623465623552706504359677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2164620831403608672479569 1623465623552706504359677)
                    ·
                      refine ⟨608799608832264939134879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623465623552706504359677 608799608832264939134879)
                      ·
                        rfl

theorem cell23_1185633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1185633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185633 prefixEnd_1185633 := by exact prefixLift 1185633
  have htrace : WordTrace (prefixWord ++ tailWord_1185633) baseStart_1185633 baseEnd_1185633 := by
    simpa [prefixWord, tailWord_1185633, baseEnd_1185633] using wordTrace_append hprefix tailTrace_1185633
  have hstable : (prefixWord ++ tailWord_1185633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185633).length < 2 ^ (prefixWord ++ tailWord_1185633).sum := by decide
  have hdescent : baseEnd_1185633 < baseStart_1185633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185653 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 6]
def baseStart_1185653 : Nat := 118140960795 + 1185653 * 2 ^ 59
def prefixEnd_1185653 : Nat := 4983230072969 + 3 ^ 40 * 1185653 * 2
def baseEnd_1185653 : Nat := 67645542049483873431643

theorem tailTrace_1185653 : CollatzResearch.WordTrace tailWord_1185653 prefixEnd_1185653 67645542049483873431643 := by
  unfold tailWord_1185653
  simp only [CollatzResearch.WordTrace]
  refine ⟨43244317573589149256185613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28829545049059432837457075 43244317573589149256185613)
  ·
    refine ⟨16216619090095930971069605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43244317573589149256185613 16216619090095930971069605)
    ·
      refine ⟨3040616079392987057075551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16216619090095930971069605 3040616079392987057075551)
      ·
        refine ⟨4560924119089480585613327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040616079392987057075551 4560924119089480585613327)
        ·
          refine ⟨6841386178634220878419991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560924119089480585613327 6841386178634220878419991)
          ·
            refine ⟨10262079267951331317629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6841386178634220878419991 10262079267951331317629987)
            ·
              refine ⟨15393118901926996976444981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10262079267951331317629987 15393118901926996976444981)
              ·
                refine ⟨1443104897055655966541717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15393118901926996976444981 1443104897055655966541717)
                ·
                  refine ⟨67645542049483873431643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1443104897055655966541717 67645542049483873431643)
                  ·
                    rfl

theorem cell23_1185653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_1185653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185653 prefixEnd_1185653 := by exact prefixLift 1185653
  have htrace : WordTrace (prefixWord ++ tailWord_1185653) baseStart_1185653 baseEnd_1185653 := by
    simpa [prefixWord, tailWord_1185653, baseEnd_1185653] using wordTrace_append hprefix tailTrace_1185653
  have hstable : (prefixWord ++ tailWord_1185653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185653).length < 2 ^ (prefixWord ++ tailWord_1185653).sum := by decide
  have hdescent : baseEnd_1185653 < baseStart_1185653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185674 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_1185674 : Nat := 118140960795 + 1185674 * 2 ^ 59
def prefixEnd_1185674 : Nat := 4983230072969 + 3 ^ 40 * 1185674 * 2
def baseEnd_1185674 : Nat := 202940220513033092907397

theorem tailTrace_1185674 : CollatzResearch.WordTrace tailWord_1185674 prefixEnd_1185674 202940220513033092907397 := by
  unfold tailWord_1185674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811270876628267460675019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28830055671008713228466717 10811270876628267460675019)
  ·
    refine ⟨16216906314942401191012529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811270876628267460675019 16216906314942401191012529)
    ·
      refine ⟨12162679736206800893259397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16216906314942401191012529 12162679736206800893259397)
      ·
        refine ⟨2280502450538775167486137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12162679736206800893259397 2280502450538775167486137)
        ·
          refine ⟨1710376837904081375614603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2280502450538775167486137 1710376837904081375614603)
          ·
            refine ⟨2565565256856122063421905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710376837904081375614603 2565565256856122063421905)
            ·
              refine ⟨1924173942642091547566429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2565565256856122063421905 1924173942642091547566429)
              ·
                refine ⟨721565228490784330337411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1924173942642091547566429 721565228490784330337411)
                ·
                  refine ⟨1082347842736176495506117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721565228490784330337411 1082347842736176495506117)
                  ·
                    refine ⟨202940220513033092907397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082347842736176495506117 202940220513033092907397)
                    ·
                      rfl

theorem cell23_1185674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_1185674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185674 prefixEnd_1185674 := by exact prefixLift 1185674
  have htrace : WordTrace (prefixWord ++ tailWord_1185674) baseStart_1185674 baseEnd_1185674 := by
    simpa [prefixWord, tailWord_1185674, baseEnd_1185674] using wordTrace_append hprefix tailTrace_1185674
  have hstable : (prefixWord ++ tailWord_1185674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185674).length < 2 ^ (prefixWord ++ tailWord_1185674).sum := by decide
  have hdescent : baseEnd_1185674 < baseStart_1185674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185676 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1185676 : Nat := 118140960795 + 1185676 * 2 ^ 59
def prefixEnd_1185676 : Nat := 4983230072969 + 3 ^ 40 * 1185676 * 2
def baseEnd_1185676 : Nat := 608821688500408270897181

theorem tailTrace_1185676 : CollatzResearch.WordTrace tailWord_1185676 prefixEnd_1185676 608821688500408270897181 := by
  unfold tailWord_1185676
  simp only [CollatzResearch.WordTrace]
  refine ⟨21622578226252912092136441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28830104301670549456181921 21622578226252912092136441)
  ·
    refine ⟨16216933669689684069102331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21622578226252912092136441 16216933669689684069102331)
    ·
      refine ⟨24325400504534526103653497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216933669689684069102331 24325400504534526103653497)
      ·
        refine ⟨18244050378400894577740123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24325400504534526103653497 18244050378400894577740123)
        ·
          refine ⟨27366075567601341866610185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18244050378400894577740123 27366075567601341866610185)
          ·
            refine ⟨20524556675701006399957639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27366075567601341866610185 20524556675701006399957639)
            ·
              refine ⟨30786835013551509599936459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20524556675701006399957639 30786835013551509599936459)
              ·
                refine ⟨46180252520327264399904689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30786835013551509599936459 46180252520327264399904689)
                ·
                  refine ⟨34635189390245448299928517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46180252520327264399904689 34635189390245448299928517)
                  ·
                    refine ⟨6494098010671021556236597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34635189390245448299928517 6494098010671021556236597)
                    ·
                      refine ⟨608821688500408270897181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6494098010671021556236597 608821688500408270897181)
                      ·
                        rfl

theorem cell23_1185676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1185676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185676 prefixEnd_1185676 := by exact prefixLift 1185676
  have htrace : WordTrace (prefixWord ++ tailWord_1185676) baseStart_1185676 baseEnd_1185676 := by
    simpa [prefixWord, tailWord_1185676, baseEnd_1185676] using wordTrace_append hprefix tailTrace_1185676
  have hstable : (prefixWord ++ tailWord_1185676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185676).length < 2 ^ (prefixWord ++ tailWord_1185676).sum := by decide
  have hdescent : baseEnd_1185676 < baseStart_1185676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185704 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 6]
def baseStart_1185704 : Nat := 118140960795 + 1185704 * 2 ^ 59
def prefixEnd_1185704 : Nat := 4983230072969 + 3 ^ 40 * 1185704 * 2
def baseEnd_1185704 : Nat := 67648451773192684594117

theorem tailTrace_1185704 : CollatzResearch.WordTrace tailWord_1185704 prefixEnd_1185704 67648451773192684594117 := by
  unfold tailWord_1185704
  simp only [CollatzResearch.WordTrace]
  refine ⟨21623088848202192483146083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28830785130936256644194777 21623088848202192483146083)
  ·
    refine ⟨32434633272303288724719125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21623088848202192483146083 32434633272303288724719125)
    ·
      refine ⟨1520373434639216658971209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32434633272303288724719125 1520373434639216658971209)
      ·
        refine ⟨1140280075979412494228407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520373434639216658971209 1140280075979412494228407)
        ·
          refine ⟨1710420113969118741342611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140280075979412494228407 1710420113969118741342611)
          ·
            refine ⟨2565630170953678112013917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710420113969118741342611 2565630170953678112013917)
            ·
              refine ⟨962111314107629292005219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565630170953678112013917 962111314107629292005219)
              ·
                refine ⟨1443166971161443938007829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962111314107629292005219 1443166971161443938007829)
                ·
                  refine ⟨67648451773192684594117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1443166971161443938007829 67648451773192684594117)
                  ·
                    rfl

theorem cell23_1185704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 6].length) (baseStart_1185704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185704 prefixEnd_1185704 := by exact prefixLift 1185704
  have htrace : WordTrace (prefixWord ++ tailWord_1185704) baseStart_1185704 baseEnd_1185704 := by
    simpa [prefixWord, tailWord_1185704, baseEnd_1185704] using wordTrace_append hprefix tailTrace_1185704
  have hstable : (prefixWord ++ tailWord_1185704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185704).length < 2 ^ (prefixWord ++ tailWord_1185704).sum := by decide
  have hdescent : baseEnd_1185704 < baseStart_1185704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185720 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_1185720 : Nat := 118140960795 + 1185720 * 2 ^ 59
def prefixEnd_1185720 : Nat := 4983230072969 + 3 ^ 40 * 1185720 * 2
def baseEnd_1185720 : Nat := 608844281649206098746979

theorem tailTrace_1185720 : CollatzResearch.WordTrace tailWord_1185720 prefixEnd_1185720 608844281649206098746979 := by
  unfold tailWord_1185720
  simp only [CollatzResearch.WordTrace]
  refine ⟨21623380632173209849437307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28831174176230946465916409 21623380632173209849437307)
  ·
    refine ⟨32435070948259814774155961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21623380632173209849437307 32435070948259814774155961)
    ·
      refine ⟨24326303211194861080616971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32435070948259814774155961 24326303211194861080616971)
      ·
        refine ⟨36489454816792291620925457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24326303211194861080616971 36489454816792291620925457)
        ·
          refine ⟨27367091112594218715694093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36489454816792291620925457 27367091112594218715694093)
          ·
            refine ⟨10262659167222832018385285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27367091112594218715694093 10262659167222832018385285)
            ·
              refine ⟨1924248593854281003447241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10262659167222832018385285 1924248593854281003447241)
              ·
                refine ⟨1443186445390710752585431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924248593854281003447241 1443186445390710752585431)
                ·
                  refine ⟨2164779668086066128878147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443186445390710752585431 2164779668086066128878147)
                  ·
                    refine ⟨3247169502129099193317221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2164779668086066128878147 3247169502129099193317221)
                    ·
                      refine ⟨608844281649206098746979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3247169502129099193317221 608844281649206098746979)
                      ·
                        rfl

theorem cell23_1185720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_1185720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185720 prefixEnd_1185720 := by exact prefixLift 1185720
  have htrace : WordTrace (prefixWord ++ tailWord_1185720) baseStart_1185720 baseEnd_1185720 := by
    simpa [prefixWord, tailWord_1185720, baseEnd_1185720] using wordTrace_append hprefix tailTrace_1185720
  have hstable : (prefixWord ++ tailWord_1185720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185720).length < 2 ^ (prefixWord ++ tailWord_1185720).sum := by decide
  have hdescent : baseEnd_1185720 < baseStart_1185720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185740 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1185740 : Nat := 118140960795 + 1185740 * 2 ^ 59
def prefixEnd_1185740 : Nat := 4983230072969 + 3 ^ 40 * 1185740 * 2
def baseEnd_1185740 : Nat := 608854551262296020496887

theorem tailTrace_1185740 : CollatzResearch.WordTrace tailWord_1185740 prefixEnd_1185740 608854551262296020496887 := by
  unfold tailWord_1185740
  simp only [CollatzResearch.WordTrace]
  refine ⟨21623745362136981557301337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28831660482849308743068449 21623745362136981557301337)
  ·
    refine ⟨16217809021602736167976003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21623745362136981557301337 16217809021602736167976003)
    ·
      refine ⟨24326713532404104251964005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16217809021602736167976003 24326713532404104251964005)
      ·
        refine ⟨4561258787325769547243251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24326713532404104251964005 4561258787325769547243251)
        ·
          refine ⟨6841888180988654320864877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561258787325769547243251 6841888180988654320864877)
          ·
            refine ⟨2565708067870745370324329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6841888180988654320864877 2565708067870745370324329)
            ·
              refine ⟨1924281050903059027743247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2565708067870745370324329 1924281050903059027743247)
              ·
                refine ⟨2886421576354588541614871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924281050903059027743247 2886421576354588541614871)
                ·
                  refine ⟨4329632364531882812422307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886421576354588541614871 4329632364531882812422307)
                  ·
                    refine ⟨6494448546797824218633461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4329632364531882812422307 6494448546797824218633461)
                    ·
                      refine ⟨608854551262296020496887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6494448546797824218633461 608854551262296020496887)
                      ·
                        rfl

theorem cell23_1185740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1185740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185740 prefixEnd_1185740 := by exact prefixLift 1185740
  have htrace : WordTrace (prefixWord ++ tailWord_1185740) baseStart_1185740 baseEnd_1185740 := by
    simpa [prefixWord, tailWord_1185740, baseEnd_1185740] using wordTrace_append hprefix tailTrace_1185740
  have hstable : (prefixWord ++ tailWord_1185740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185740).length < 2 ^ (prefixWord ++ tailWord_1185740).sum := by decide
  have hdescent : baseEnd_1185740 < baseStart_1185740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185770 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1185770 : Nat := 118140960795 + 1185770 * 2 ^ 59
def prefixEnd_1185770 : Nat := 4983230072969 + 3 ^ 40 * 1185770 * 2
def baseEnd_1185770 : Nat := 608869955681930903121749

theorem tailTrace_1185770 : CollatzResearch.WordTrace tailWord_1185770 prefixEnd_1185770 608869955681930903121749 := by
  unfold tailWord_1185770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10812146228541319559548691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28832389942776852158796509 10812146228541319559548691)
  ·
    refine ⟨16218219342811979339323037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10812146228541319559548691 16218219342811979339323037)
    ·
      refine ⟨6081832253554492252246139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16218219342811979339323037 6081832253554492252246139)
      ·
        refine ⟨9122748380331738378369209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081832253554492252246139 9122748380331738378369209)
        ·
          refine ⟨6842061285248803783776907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9122748380331738378369209 6842061285248803783776907)
          ·
            refine ⟨10263091927873205675665361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842061285248803783776907 10263091927873205675665361)
            ·
              refine ⟨7697318945904904256749021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10263091927873205675665361 7697318945904904256749021)
              ·
                refine ⟨2886494604714339096280883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7697318945904904256749021 2886494604714339096280883)
                ·
                  refine ⟨4329741907071508644421325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886494604714339096280883 4329741907071508644421325)
                  ·
                    refine ⟨1623653215151815741657997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4329741907071508644421325 1623653215151815741657997)
                    ·
                      refine ⟨608869955681930903121749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623653215151815741657997 608869955681930903121749)
                      ·
                        rfl

theorem cell23_1185770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1185770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185770 prefixEnd_1185770 := by exact prefixLift 1185770
  have htrace : WordTrace (prefixWord ++ tailWord_1185770) baseStart_1185770 baseEnd_1185770 := by
    simpa [prefixWord, tailWord_1185770, baseEnd_1185770] using wordTrace_append hprefix tailTrace_1185770
  have hstable : (prefixWord ++ tailWord_1185770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185770).length < 2 ^ (prefixWord ++ tailWord_1185770).sum := by decide
  have hdescent : baseEnd_1185770 < baseStart_1185770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185774 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1185774 : Nat := 118140960795 + 1185774 * 2 ^ 59
def prefixEnd_1185774 : Nat := 4983230072969 + 3 ^ 40 * 1185774 * 2
def baseEnd_1185774 : Nat := 608872009604548887471731

theorem tailTrace_1185774 : CollatzResearch.WordTrace tailWord_1185774 prefixEnd_1185774 608872009604548887471731 := by
  unfold tailWord_1185774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406091350768848365167547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28832487204100524614226917 5406091350768848365167547)
  ·
    refine ⟨8109137026153272547751321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5406091350768848365167547 8109137026153272547751321)
    ·
      refine ⟨6081852769614954410813491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8109137026153272547751321 6081852769614954410813491)
      ·
        refine ⟨9122779154422431616220237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081852769614954410813491 9122779154422431616220237)
        ·
          refine ⟨3421042182908411856082589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9122779154422431616220237 3421042182908411856082589)
          ·
            refine ⟨1282890818590654446030971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3421042182908411856082589 1282890818590654446030971)
            ·
              refine ⟨1924336227885981669046457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282890818590654446030971 1924336227885981669046457)
              ·
                refine ⟨1443252170914486251784843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924336227885981669046457 1443252170914486251784843)
                ·
                  refine ⟨2164878256371729377677265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443252170914486251784843 2164878256371729377677265)
                  ·
                    refine ⟨1623658692278797033257949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2164878256371729377677265 1623658692278797033257949)
                    ·
                      refine ⟨608872009604548887471731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623658692278797033257949 608872009604548887471731)
                      ·
                        rfl

theorem cell23_1185774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1185774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185774 prefixEnd_1185774 := by exact prefixLift 1185774
  have htrace : WordTrace (prefixWord ++ tailWord_1185774) baseStart_1185774 baseEnd_1185774 := by
    simpa [prefixWord, tailWord_1185774, baseEnd_1185774] using wordTrace_append hprefix tailTrace_1185774
  have hstable : (prefixWord ++ tailWord_1185774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185774).length < 2 ^ (prefixWord ++ tailWord_1185774).sum := by decide
  have hdescent : baseEnd_1185774 < baseStart_1185774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185803 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 2, 6]
def baseStart_1185803 : Nat := 118140960795 + 1185803 * 2 ^ 59
def prefixEnd_1185803 : Nat := 4983230072969 + 3 ^ 40 * 1185803 * 2
def baseEnd_1185803 : Nat := 202962300181176424669699

theorem tailTrace_1185803 : CollatzResearch.WordTrace tailWord_1185803 prefixEnd_1185803 202962300181176424669699 := by
  unfold tailWord_1185803
  simp only [CollatzResearch.WordTrace]
  refine ⟨43249788523045724874146063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28833192348697149916097375 43249788523045724874146063)
  ·
    refine ⟨64874682784568587311219095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43249788523045724874146063 64874682784568587311219095)
    ·
      refine ⟨97312024176852880966828643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64874682784568587311219095 97312024176852880966828643)
      ·
        refine ⟨145968036265279321450242965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97312024176852880966828643 145968036265279321450242965)
        ·
          refine ⟨6842251699934968192980139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145968036265279321450242965 6842251699934968192980139)
          ·
            refine ⟨10263377549902452289470209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842251699934968192980139 10263377549902452289470209)
            ·
              refine ⟨7697533162426839217102657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10263377549902452289470209 7697533162426839217102657)
              ·
                refine ⟨5773149871820129412826993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7697533162426839217102657 5773149871820129412826993)
                ·
                  refine ⟨4329862403865097059620245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5773149871820129412826993 4329862403865097059620245)
                  ·
                    refine ⟨202962300181176424669699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4329862403865097059620245 202962300181176424669699)
                    ·
                      rfl

theorem cell23_1185803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 6].length) (baseStart_1185803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185803 prefixEnd_1185803 := by exact prefixLift 1185803
  have htrace : WordTrace (prefixWord ++ tailWord_1185803) baseStart_1185803 baseEnd_1185803 := by
    simpa [prefixWord, tailWord_1185803, baseEnd_1185803] using wordTrace_append hprefix tailTrace_1185803
  have hstable : (prefixWord ++ tailWord_1185803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185803).length < 2 ^ (prefixWord ++ tailWord_1185803).sum := by decide
  have hdescent : baseEnd_1185803 < baseStart_1185803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185820 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1185820 : Nat := 118140960795 + 1185820 * 2 ^ 59
def prefixEnd_1185820 : Nat := 4983230072969 + 3 ^ 40 * 1185820 * 2
def baseEnd_1185820 : Nat := 202965209904885235832173

theorem tailTrace_1185820 : CollatzResearch.WordTrace tailWord_1185820 prefixEnd_1185820 202965209904885235832173 := by
  unfold tailWord_1185820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21625204281992068388757457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28833605709322757851676609 21625204281992068388757457)
  ·
    refine ⟨16218903211494051291568093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21625204281992068388757457 16218903211494051291568093)
    ·
      refine ⟨6082088704310269234338035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16218903211494051291568093 6082088704310269234338035)
      ·
        refine ⟨9123133056465403851507053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082088704310269234338035 9123133056465403851507053)
        ·
          refine ⟨3421174896174526444315145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9123133056465403851507053 3421174896174526444315145)
          ·
            refine ⟨2565881172130894833236359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3421174896174526444315145 2565881172130894833236359)
            ·
              refine ⟨3848821758196342249854539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565881172130894833236359 3848821758196342249854539)
              ·
                refine ⟨5773232637294513374781809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848821758196342249854539 5773232637294513374781809)
                ·
                  refine ⟨4329924477970885031086357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5773232637294513374781809 4329924477970885031086357)
                  ·
                    refine ⟨202965209904885235832173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4329924477970885031086357 202965209904885235832173)
                    ·
                      rfl

theorem cell23_1185820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1185820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185820 prefixEnd_1185820 := by exact prefixLift 1185820
  have htrace : WordTrace (prefixWord ++ tailWord_1185820) baseStart_1185820 baseEnd_1185820 := by
    simpa [prefixWord, tailWord_1185820, baseEnd_1185820] using wordTrace_append hprefix tailTrace_1185820
  have hstable : (prefixWord ++ tailWord_1185820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185820).length < 2 ^ (prefixWord ++ tailWord_1185820).sum := by decide
  have hdescent : baseEnd_1185820 < baseStart_1185820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185827 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 1, 4, 2]
def baseStart_1185827 : Nat := 118140960795 + 1185827 * 2 ^ 59
def prefixEnd_1185827 : Nat := 4983230072969 + 3 ^ 40 * 1185827 * 2
def baseEnd_1185827 : Nat := 608899224079237180108987

theorem tailTrace_1185827 : CollatzResearch.WordTrace tailWord_1185827 prefixEnd_1185827 608899224079237180108987 := by
  unfold tailWord_1185827
  simp only [CollatzResearch.WordTrace]
  refine ⟨43250663874958776973019735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28833775916639184648679823 43250663874958776973019735)
  ·
    refine ⟨64875995812438165459529603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43250663874958776973019735 64875995812438165459529603)
    ·
      refine ⟨97313993718657248189294405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64875995812438165459529603 97313993718657248189294405)
      ·
        refine ⟨18246373822248234035492701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97313993718657248189294405 18246373822248234035492701)
        ·
          refine ⟨6842390183343087763309763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18246373822248234035492701 6842390183343087763309763)
          ·
            refine ⟨10263585275014631644964645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842390183343087763309763 10263585275014631644964645)
            ·
              refine ⟨1924422239065243433430871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10263585275014631644964645 1924422239065243433430871)
              ·
                refine ⟨2886633358597865150146307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924422239065243433430871 2886633358597865150146307)
                ·
                  refine ⟨4329950037896797725219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886633358597865150146307 4329950037896797725219461)
                  ·
                    refine ⟨811865632105649573478649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4329950037896797725219461 811865632105649573478649)
                    ·
                      refine ⟨608899224079237180108987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811865632105649573478649 608899224079237180108987)
                      ·
                        rfl

theorem cell23_1185827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_1185827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185827 prefixEnd_1185827 := by exact prefixLift 1185827
  have htrace : WordTrace (prefixWord ++ tailWord_1185827) baseStart_1185827 baseEnd_1185827 := by
    simpa [prefixWord, tailWord_1185827, baseEnd_1185827] using wordTrace_append hprefix tailTrace_1185827
  have hstable : (prefixWord ++ tailWord_1185827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185827).length < 2 ^ (prefixWord ++ tailWord_1185827).sum := by decide
  have hdescent : baseEnd_1185827 < baseStart_1185827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185848 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 1, 3, 2]
def baseStart_1185848 : Nat := 118140960795 + 1185848 * 2 ^ 59
def prefixEnd_1185848 : Nat := 4983230072969 + 3 ^ 40 * 1185848 * 2
def baseEnd_1185848 : Nat := 608910007172981597946391

theorem tailTrace_1185848 : CollatzResearch.WordTrace tailWord_1185848 prefixEnd_1185848 608910007172981597946391 := by
  unfold tailWord_1185848
  simp only [CollatzResearch.WordTrace]
  refine ⟨21625714903941348779767099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28834286538588465039689465 21625714903941348779767099)
  ·
    refine ⟨32438572355912023169650649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21625714903941348779767099 32438572355912023169650649)
    ·
      refine ⟨24328929266934017377237987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32438572355912023169650649 24328929266934017377237987)
      ·
        refine ⟨36493393900401026065856981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24328929266934017377237987 36493393900401026065856981)
        ·
          refine ⟨855313919540649048418523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36493393900401026065856981 855313919540649048418523)
          ·
            refine ⟨1282970879310973572627785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855313919540649048418523 1282970879310973572627785)
            ·
              refine ⟨962228159483230179470839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282970879310973572627785 962228159483230179470839)
              ·
                refine ⟨1443342239224845269206259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962228159483230179470839 1443342239224845269206259)
                ·
                  refine ⟨2165013358837267903809389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443342239224845269206259 2165013358837267903809389)
                  ·
                    refine ⟨811880009563975463928521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2165013358837267903809389 811880009563975463928521)
                    ·
                      refine ⟨608910007172981597946391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811880009563975463928521 608910007172981597946391)
                      ·
                        rfl

theorem cell23_1185848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_1185848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185848 prefixEnd_1185848 := by exact prefixLift 1185848
  have htrace : WordTrace (prefixWord ++ tailWord_1185848) baseStart_1185848 baseEnd_1185848 := by
    simpa [prefixWord, tailWord_1185848, baseEnd_1185848] using wordTrace_append hprefix tailTrace_1185848
  have hstable : (prefixWord ++ tailWord_1185848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185848).length < 2 ^ (prefixWord ++ tailWord_1185848).sum := by decide
  have hdescent : baseEnd_1185848 < baseStart_1185848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185873 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_1185873 : Nat := 118140960795 + 1185873 * 2 ^ 59
def prefixEnd_1185873 : Nat := 4983230072969 + 3 ^ 40 * 1185873 * 2
def baseEnd_1185873 : Nat := 608922844189344000133775

theorem tailTrace_1185873 : CollatzResearch.WordTrace tailWord_1185873 prefixEnd_1185873 608922844189344000133775 := by
  unfold tailWord_1185873
  simp only [CollatzResearch.WordTrace]
  refine ⟨43252341632792126829194273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28834894421861417886129515 43252341632792126829194273)
  ·
    refine ⟨32439256224594095121895705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43252341632792126829194273 32439256224594095121895705)
    ·
      refine ⟨24329442168445571341421779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32439256224594095121895705 24329442168445571341421779)
      ·
        refine ⟨36494163252668357012132669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24329442168445571341421779 36494163252668357012132669)
        ·
          refine ⟨13685311219750633879549751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36494163252668357012132669 13685311219750633879549751)
          ·
            refine ⟨20527966829625950819324627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685311219750633879549751 20527966829625950819324627)
            ·
              refine ⟨30791950244438926228986941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20527966829625950819324627 30791950244438926228986941)
              ·
                refine ⟨11546981341664597335870103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30791950244438926228986941 11546981341664597335870103)
                ·
                  refine ⟨17320472012496896003805155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11546981341664597335870103 17320472012496896003805155)
                  ·
                    refine ⟨25980708018745344005707733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17320472012496896003805155 25980708018745344005707733)
                    ·
                      refine ⟨608922844189344000133775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25980708018745344005707733 608922844189344000133775)
                      ·
                        rfl

theorem cell23_1185873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_1185873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185873 prefixEnd_1185873 := by exact prefixLift 1185873
  have htrace : WordTrace (prefixWord ++ tailWord_1185873) baseStart_1185873 baseEnd_1185873 := by
    simpa [prefixWord, tailWord_1185873, baseEnd_1185873] using wordTrace_append hprefix tailTrace_1185873
  have hstable : (prefixWord ++ tailWord_1185873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185873).length < 2 ^ (prefixWord ++ tailWord_1185873).sum := by decide
  have hdescent : baseEnd_1185873 < baseStart_1185873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185878 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1185878 : Nat := 118140960795 + 1185878 * 2 ^ 59
def prefixEnd_1185878 : Nat := 4983230072969 + 3 ^ 40 * 1185878 * 2
def baseEnd_1185878 : Nat := 608925411592616480571253

theorem tailTrace_1185878 : CollatzResearch.WordTrace tailWord_1185878 prefixEnd_1185878 608925411592616480571253 := by
  unfold tailWord_1185878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703282749860875792695393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28835015998516008455417525 2703282749860875792695393)
  ·
    refine ⟨2027462062395656844521545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2703282749860875792695393 2027462062395656844521545)
    ·
      refine ⟨1520596546796742633391159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027462062395656844521545 1520596546796742633391159)
      ·
        refine ⟨2280894820195113950086739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520596546796742633391159 2280894820195113950086739)
        ·
          refine ⟨3421342230292670925130109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280894820195113950086739 3421342230292670925130109)
          ·
            refine ⟨1283003336359751596923791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3421342230292670925130109 1283003336359751596923791)
            ·
              refine ⟨1924505004539627395385687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283003336359751596923791 1924505004539627395385687)
              ·
                refine ⟨2886757506809441093078531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924505004539627395385687 2886757506809441093078531)
                ·
                  refine ⟨4330136260214161639617797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886757506809441093078531 4330136260214161639617797)
                  ·
                    refine ⟨811900548790155307428337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4330136260214161639617797 811900548790155307428337)
                    ·
                      refine ⟨608925411592616480571253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 811900548790155307428337 608925411592616480571253)
                      ·
                        rfl

theorem cell23_1185878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1185878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185878 prefixEnd_1185878 := by exact prefixLift 1185878
  have htrace : WordTrace (prefixWord ++ tailWord_1185878) baseStart_1185878 baseEnd_1185878 := by
    simpa [prefixWord, tailWord_1185878, baseEnd_1185878] using wordTrace_append hprefix tailTrace_1185878
  have hstable : (prefixWord ++ tailWord_1185878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185878).length < 2 ^ (prefixWord ++ tailWord_1185878).sum := by decide
  have hdescent : baseEnd_1185878 < baseStart_1185878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185900 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_1185900 : Nat := 118140960795 + 1185900 * 2 ^ 59
def prefixEnd_1185900 : Nat := 4983230072969 + 3 ^ 40 * 1185900 * 2
def baseEnd_1185900 : Nat := 608936708167015394496151

theorem tailTrace_1185900 : CollatzResearch.WordTrace tailWord_1185900 prefixEnd_1185900 608936708167015394496151 := by
  unfold tailWord_1185900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626663201847155220213577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28835550935796206960284769 21626663201847155220213577)
  ·
    refine ⟨16219997401385366415160183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21626663201847155220213577 16219997401385366415160183)
    ·
      refine ⟨24329996102078049622740275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16219997401385366415160183 24329996102078049622740275)
      ·
        refine ⟨36494994153117074434110413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24329996102078049622740275 36494994153117074434110413)
        ·
          refine ⟨13685622807418902912791405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36494994153117074434110413 13685622807418902912791405)
          ·
            refine ⟨5132108552782088592296777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13685622807418902912791405 5132108552782088592296777)
            ·
              refine ⟨3849081414586566444222583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132108552782088592296777 3849081414586566444222583)
              ·
                refine ⟨5773622121879849666333875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849081414586566444222583 5773622121879849666333875)
                ·
                  refine ⟨8660433182819774499500813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5773622121879849666333875 8660433182819774499500813)
                  ·
                    refine ⟨3247662443557415437312805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8660433182819774499500813 3247662443557415437312805)
                    ·
                      refine ⟨608936708167015394496151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3247662443557415437312805 608936708167015394496151)
                      ·
                        rfl

theorem cell23_1185900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_1185900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185900 prefixEnd_1185900 := by exact prefixLift 1185900
  have htrace : WordTrace (prefixWord ++ tailWord_1185900) baseStart_1185900 baseEnd_1185900 := by
    simpa [prefixWord, tailWord_1185900, baseEnd_1185900] using wordTrace_append hprefix tailTrace_1185900
  have hstable : (prefixWord ++ tailWord_1185900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185900).length < 2 ^ (prefixWord ++ tailWord_1185900).sum := by decide
  have hdescent : baseEnd_1185900 < baseStart_1185900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185917 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1185917 : Nat := 118140960795 + 1185917 * 2 ^ 59
def prefixEnd_1185917 : Nat := 4983230072969 + 3 ^ 40 * 1185917 * 2
def baseEnd_1185917 : Nat := 608945437338141827983573

theorem tailTrace_1185917 : CollatzResearch.WordTrace tailWord_1185917 prefixEnd_1185917 608945437338141827983573 := by
  unfold tailWord_1185917
  simp only [CollatzResearch.WordTrace]
  refine ⟨43253946444632722343796005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28835964296421814895864003 43253946444632722343796005)
  ·
    refine ⟨8110114958368635439461751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43253946444632722343796005 8110114958368635439461751)
    ·
      refine ⟨12165172437552953159192627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8110114958368635439461751 12165172437552953159192627)
      ·
        refine ⟨18247758656329429738788941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12165172437552953159192627 18247758656329429738788941)
        ·
          refine ⟨6842909496123536152045853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18247758656329429738788941 6842909496123536152045853)
          ·
            refine ⟨2566091061046326057017195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6842909496123536152045853 2566091061046326057017195)
            ·
              refine ⟨3849136591569489085525793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566091061046326057017195 3849136591569489085525793)
              ·
                refine ⟨2886852443677116814144345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3849136591569489085525793 2886852443677116814144345)
                ·
                  refine ⟨2165139332757837610608259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886852443677116814144345 2165139332757837610608259)
                  ·
                    refine ⟨3247708999136756415912389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165139332757837610608259 3247708999136756415912389)
                    ·
                      refine ⟨608945437338141827983573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3247708999136756415912389 608945437338141827983573)
                      ·
                        rfl

theorem cell23_1185917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1185917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185917 prefixEnd_1185917 := by exact prefixLift 1185917
  have htrace : WordTrace (prefixWord ++ tailWord_1185917) baseStart_1185917 baseEnd_1185917 := by
    simpa [prefixWord, tailWord_1185917, baseEnd_1185917] using wordTrace_append hprefix tailTrace_1185917
  have hstable : (prefixWord ++ tailWord_1185917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185917).length < 2 ^ (prefixWord ++ tailWord_1185917).sum := by decide
  have hdescent : baseEnd_1185917 < baseStart_1185917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185927 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 3, 4]
def baseStart_1185927 : Nat := 118140960795 + 1185927 * 2 ^ 59
def prefixEnd_1185927 : Nat := 4983230072969 + 3 ^ 40 * 1185927 * 2
def baseEnd_1185927 : Nat := 202983524048228929619509

theorem tailTrace_1185927 : CollatzResearch.WordTrace tailWord_1185927 prefixEnd_1185927 202983524048228929619509 := by
  unfold tailWord_1185927
  simp only [CollatzResearch.WordTrace]
  refine ⟨43254311174596494051660035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28836207449730996034440023 43254311174596494051660035)
  ·
    refine ⟨64881466761894741077490053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43254311174596494051660035 64881466761894741077490053)
    ·
      refine ⟨12165275017855263952029385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64881466761894741077490053 12165275017855263952029385)
      ·
        refine ⟨9123956263391447964022039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12165275017855263952029385 9123956263391447964022039)
        ·
          refine ⟨13685934395087171946033059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9123956263391447964022039 13685934395087171946033059)
          ·
            refine ⟨20528901592630757919049589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685934395087171946033059 20528901592630757919049589)
            ·
              refine ⟨1924584524309133554910899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20528901592630757919049589 1924584524309133554910899)
              ·
                refine ⟨2886876786463700332366349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924584524309133554910899 2886876786463700332366349)
                ·
                  refine ⟨1082578794923887624637381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2886876786463700332366349 1082578794923887624637381)
                  ·
                    refine ⟨202983524048228929619509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082578794923887624637381 202983524048228929619509)
                    ·
                      rfl

theorem cell23_1185927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_1185927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185927 prefixEnd_1185927 := by exact prefixLift 1185927
  have htrace : WordTrace (prefixWord ++ tailWord_1185927) baseStart_1185927 baseEnd_1185927 := by
    simpa [prefixWord, tailWord_1185927, baseEnd_1185927] using wordTrace_append hprefix tailTrace_1185927
  have hstable : (prefixWord ++ tailWord_1185927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185927).length < 2 ^ (prefixWord ++ tailWord_1185927).sum := by decide
  have hdescent : baseEnd_1185927 < baseStart_1185927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185954 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1185954 : Nat := 118140960795 + 1185954 * 2 ^ 59
def prefixEnd_1185954 : Nat := 4983230072969 + 3 ^ 40 * 1185954 * 2
def baseEnd_1185954 : Nat := 608964436122358183220903

theorem tailTrace_1185954 : CollatzResearch.WordTrace tailWord_1185954 prefixEnd_1185954 608964436122358183220903 := by
  unfold tailWord_1185954
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813823986374669415723229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28836863963665785108595277 10813823986374669415723229)
  ·
    refine ⟨4055183994890501030896211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10813823986374669415723229 4055183994890501030896211)
    ·
      refine ⟨6082775992335751546344317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055183994890501030896211 6082775992335751546344317)
      ·
        refine ⟨2281040997125906829879119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6082775992335751546344317 2281040997125906829879119)
        ·
          refine ⟨3421561495688860244818679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281040997125906829879119 3421561495688860244818679)
          ·
            refine ⟨5132342243533290367228019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421561495688860244818679 5132342243533290367228019)
            ·
              refine ⟨7698513365299935550842029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5132342243533290367228019 7698513365299935550842029)
              ·
                refine ⟨2886942511987475831565761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7698513365299935550842029 2886942511987475831565761)
                ·
                  refine ⟨2165206883990606873674321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2886942511987475831565761 2165206883990606873674321)
                  ·
                    refine ⟨1623905162992955155255741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2165206883990606873674321 1623905162992955155255741)
                    ·
                      refine ⟨608964436122358183220903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1623905162992955155255741 608964436122358183220903)
                      ·
                        rfl

theorem cell23_1185954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1185954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1185954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1185954 prefixEnd_1185954 := by exact prefixLift 1185954
  have htrace : WordTrace (prefixWord ++ tailWord_1185954) baseStart_1185954 baseEnd_1185954 := by
    simpa [prefixWord, tailWord_1185954, baseEnd_1185954] using wordTrace_append hprefix tailTrace_1185954
  have hstable : (prefixWord ++ tailWord_1185954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185954).length < 2 ^ (prefixWord ++ tailWord_1185954).sum := by decide
  have hdescent : baseEnd_1185954 < baseStart_1185954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186007 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_1186007 : Nat := 118140960795 + 1186007 * 2 ^ 59
def prefixEnd_1186007 : Nat := 4983230072969 + 3 ^ 40 * 1186007 * 2
def baseEnd_1186007 : Nat := 608991650597046475858159

theorem tailTrace_1186007 : CollatzResearch.WordTrace tailWord_1186007 prefixEnd_1186007 608991650597046475858159 := by
  unfold tailWord_1186007
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257229014306667714572275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28838152676204445143048183 43257229014306667714572275)
  ·
    refine ⟨64885843521460001571858413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43257229014306667714572275 64885843521460001571858413)
    ·
      refine ⟨24332191320547500589446905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64885843521460001571858413 24332191320547500589446905)
      ·
        refine ⟨18249143490410625442085179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24332191320547500589446905 18249143490410625442085179)
        ·
          refine ⟨27373715235615938163127769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18249143490410625442085179 27373715235615938163127769)
          ·
            refine ⟨20530286426711953622345827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27373715235615938163127769 20530286426711953622345827)
            ·
              refine ⟨30795429640067930433518741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20530286426711953622345827 30795429640067930433518741)
              ·
                refine ⟨1443535764378184239071191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30795429640067930433518741 1443535764378184239071191)
                ·
                  refine ⟨2165303646567276358606787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443535764378184239071191 2165303646567276358606787)
                  ·
                    refine ⟨3247955469850914537910181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165303646567276358606787 3247955469850914537910181)
                    ·
                      refine ⟨608991650597046475858159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3247955469850914537910181 608991650597046475858159)
                      ·
                        rfl

theorem cell23_1186007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_1186007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186007 prefixEnd_1186007 := by exact prefixLift 1186007
  have htrace : WordTrace (prefixWord ++ tailWord_1186007) baseStart_1186007 baseEnd_1186007 := by
    simpa [prefixWord, tailWord_1186007, baseEnd_1186007] using wordTrace_append hprefix tailTrace_1186007
  have hstable : (prefixWord ++ tailWord_1186007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186007).length < 2 ^ (prefixWord ++ tailWord_1186007).sum := by decide
  have hdescent : baseEnd_1186007 < baseStart_1186007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186017 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1186017 : Nat := 118140960795 + 1186017 * 2 ^ 59
def prefixEnd_1186017 : Nat := 4983230072969 + 3 ^ 40 * 1186017 * 2
def baseEnd_1186017 : Nat := 202998928467863812244371

theorem tailTrace_1186017 : CollatzResearch.WordTrace tailWord_1186017 prefixEnd_1186017 202998928467863812244371 := by
  unfold tailWord_1186017
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257593744270439422436305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28838395829513626281624203 43257593744270439422436305)
  ·
    refine ⟨32443195308202829566827229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43257593744270439422436305 32443195308202829566827229)
    ·
      refine ⟨12166198240576061087560211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32443195308202829566827229 12166198240576061087560211)
      ·
        refine ⟨18249297360864091631340317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12166198240576061087560211 18249297360864091631340317)
        ·
          refine ⟨6843486510324034361752619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18249297360864091631340317 6843486510324034361752619)
          ·
            refine ⟨10265229765486051542628929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6843486510324034361752619 10265229765486051542628929)
            ·
              refine ⟨7698922324114538656971697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10265229765486051542628929 7698922324114538656971697)
              ·
                refine ⟨5774191743085903992728773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7698922324114538656971697 5774191743085903992728773)
                ·
                  refine ⟨1082660951828606998636645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5774191743085903992728773 1082660951828606998636645)
                  ·
                    refine ⟨202998928467863812244371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082660951828606998636645 202998928467863812244371)
                    ·
                      rfl

theorem cell23_1186017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1186017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186017 prefixEnd_1186017 := by exact prefixLift 1186017
  have htrace : WordTrace (prefixWord ++ tailWord_1186017) baseStart_1186017 baseEnd_1186017 := by
    simpa [prefixWord, tailWord_1186017, baseEnd_1186017] using wordTrace_append hprefix tailTrace_1186017
  have hstable : (prefixWord ++ tailWord_1186017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186017).length < 2 ^ (prefixWord ++ tailWord_1186017).sum := by decide
  have hdescent : baseEnd_1186017 < baseStart_1186017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186020 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1186020 : Nat := 118140960795 + 1186020 * 2 ^ 59
def prefixEnd_1186020 : Nat := 4983230072969 + 3 ^ 40 * 1186020 * 2
def baseEnd_1186020 : Nat := 608998325845554924995599

theorem tailTrace_1186020 : CollatzResearch.WordTrace tailWord_1186020 prefixEnd_1186020 608998325845554924995599 := by
  unfold tailWord_1186020
  simp only [CollatzResearch.WordTrace]
  refine ⟨21628851581629785467397757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28838468775506380623197009 21628851581629785467397757)
  ·
    refine ⟨8110819343111169550274159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21628851581629785467397757 8110819343111169550274159)
    ·
      refine ⟨12166229014666754325411239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8110819343111169550274159 12166229014666754325411239)
      ·
        refine ⟨18249343522000131488116859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12166229014666754325411239 18249343522000131488116859)
        ·
          refine ⟨27374015283000197232175289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18249343522000131488116859 27374015283000197232175289)
          ·
            refine ⟨20530511462250147924131467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27374015283000197232175289 20530511462250147924131467)
            ·
              refine ⟨30795767193375221886197201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20530511462250147924131467 30795767193375221886197201)
              ·
                refine ⟨23096825395031416414647901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30795767193375221886197201 23096825395031416414647901)
                ·
                  refine ⟨8661309523136781155492963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23096825395031416414647901 8661309523136781155492963)
                  ·
                    refine ⟨12991964284705171733239445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8661309523136781155492963 12991964284705171733239445)
                    ·
                      refine ⟨608998325845554924995599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12991964284705171733239445 608998325845554924995599)
                      ·
                        rfl

theorem cell23_1186020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1186020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186020 prefixEnd_1186020 := by exact prefixLift 1186020
  have htrace : WordTrace (prefixWord ++ tailWord_1186020) baseStart_1186020 baseEnd_1186020 := by
    simpa [prefixWord, tailWord_1186020, baseEnd_1186020] using wordTrace_append hprefix tailTrace_1186020
  have hstable : (prefixWord ++ tailWord_1186020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186020).length < 2 ^ (prefixWord ++ tailWord_1186020).sum := by decide
  have hdescent : baseEnd_1186020 < baseStart_1186020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186021 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_1186021 : Nat := 118140960795 + 1186021 * 2 ^ 59
def prefixEnd_1186021 : Nat := 4983230072969 + 3 ^ 40 * 1186021 * 2
def baseEnd_1186021 : Nat := 202999613108736473694365

theorem tailTrace_1186021 : CollatzResearch.WordTrace tailWord_1186021 prefixEnd_1186021 202999613108736473694365 := by
  unfold tailWord_1186021
  simp only [CollatzResearch.WordTrace]
  refine ⟨43257739636255948105581917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28838493090837298737054611 43257739636255948105581917)
  ·
    refine ⟨16221652363595980539593219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43257739636255948105581917 16221652363595980539593219)
    ·
      refine ⟨24332478545393970809389829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16221652363595980539593219 24332478545393970809389829)
      ·
        refine ⟨4562339727261369526760593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24332478545393970809389829 4562339727261369526760593)
        ·
          refine ⟨3421754795446027145070445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4562339727261369526760593 3421754795446027145070445)
          ·
            refine ⟨1283158048292260179401417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3421754795446027145070445 1283158048292260179401417)
            ·
              refine ⟨962368536219195134551063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283158048292260179401417 962368536219195134551063)
              ·
                refine ⟨1443552804328792701826595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962368536219195134551063 1443552804328792701826595)
                ·
                  refine ⟨2165329206493189052739893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443552804328792701826595 2165329206493189052739893)
                  ·
                    refine ⟨202999613108736473694365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2165329206493189052739893 202999613108736473694365)
                    ·
                      rfl

theorem cell23_1186021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_1186021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186021 prefixEnd_1186021 := by exact prefixLift 1186021
  have htrace : WordTrace (prefixWord ++ tailWord_1186021) baseStart_1186021 baseEnd_1186021 := by
    simpa [prefixWord, tailWord_1186021, baseEnd_1186021] using wordTrace_append hprefix tailTrace_1186021
  have hstable : (prefixWord ++ tailWord_1186021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186021).length < 2 ^ (prefixWord ++ tailWord_1186021).sum := by decide
  have hdescent : baseEnd_1186021 < baseStart_1186021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186024 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1186024 : Nat := 118140960795 + 1186024 * 2 ^ 59
def prefixEnd_1186024 : Nat := 4983230072969 + 3 ^ 40 * 1186024 * 2
def baseEnd_1186024 : Nat := 609000379768172909345581

theorem tailTrace_1186024 : CollatzResearch.WordTrace tailWord_1186024 prefixEnd_1186024 609000379768172909345581 := by
  unfold tailWord_1186024
  simp only [CollatzResearch.WordTrace]
  refine ⟨21628924527622539808970563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28838566036830053078627417 21628924527622539808970563)
  ·
    refine ⟨32443386791433809713455845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21628924527622539808970563 32443386791433809713455845)
    ·
      refine ⟨6083135023393839321272971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32443386791433809713455845 6083135023393839321272971)
      ·
        refine ⟨9124702535090758981909457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6083135023393839321272971 9124702535090758981909457)
        ·
          refine ⟨6843526901318069236432093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9124702535090758981909457 6843526901318069236432093)
          ·
            refine ⟨2566322587994275963662035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6843526901318069236432093 2566322587994275963662035)
            ·
              refine ⟨3849483881991413945493053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566322587994275963662035 3849483881991413945493053)
              ·
                refine ⟨1443556455746780229559895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849483881991413945493053 1443556455746780229559895)
                ·
                  refine ⟨2165334683620170344339843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443556455746780229559895 2165334683620170344339843)
                  ·
                    refine ⟨3248002025430255516509765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2165334683620170344339843 3248002025430255516509765)
                    ·
                      refine ⟨609000379768172909345581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3248002025430255516509765 609000379768172909345581)
                      ·
                        rfl

theorem cell23_1186024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1186024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186024 prefixEnd_1186024 := by exact prefixLift 1186024
  have htrace : WordTrace (prefixWord ++ tailWord_1186024) baseStart_1186024 baseEnd_1186024 := by
    simpa [prefixWord, tailWord_1186024, baseEnd_1186024] using wordTrace_append hprefix tailTrace_1186024
  have hstable : (prefixWord ++ tailWord_1186024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186024).length < 2 ^ (prefixWord ++ tailWord_1186024).sum := by decide
  have hdescent : baseEnd_1186024 < baseStart_1186024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186034 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_1186034 : Nat := 118140960795 + 1186034 * 2 ^ 59
def prefixEnd_1186034 : Nat := 4983230072969 + 3 ^ 40 * 1186034 * 2
def baseEnd_1186034 : Nat := 203001838191572623406845

theorem tailTrace_1186034 : CollatzResearch.WordTrace tailWord_1186034 prefixEnd_1186034 203001838191572623406845 := by
  unfold tailWord_1186034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814553446302212831451289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28838809190139234217203437 10814553446302212831451289)
  ·
    refine ⟨8110915084726659623588467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10814553446302212831451289 8110915084726659623588467)
    ·
      refine ⟨12166372627089989435382701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8110915084726659623588467 12166372627089989435382701)
      ·
        refine ⟨4562389735158746038268513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12166372627089989435382701 4562389735158746038268513)
        ·
          refine ⟨3421792301369059528701385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4562389735158746038268513 3421792301369059528701385)
          ·
            refine ⟨2566344226026794646526039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3421792301369059528701385 2566344226026794646526039)
            ·
              refine ⟨3849516339040191969789059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566344226026794646526039 3849516339040191969789059)
              ·
                refine ⟨5774274508560287954683589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849516339040191969789059 5774274508560287954683589)
                ·
                  refine ⟨1082676470355053991503173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5774274508560287954683589 1082676470355053991503173)
                  ·
                    refine ⟨203001838191572623406845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082676470355053991503173 203001838191572623406845)
                    ·
                      rfl

theorem cell23_1186034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_1186034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186034 prefixEnd_1186034 := by exact prefixLift 1186034
  have htrace : WordTrace (prefixWord ++ tailWord_1186034) baseStart_1186034 baseEnd_1186034 := by
    simpa [prefixWord, tailWord_1186034, baseEnd_1186034] using wordTrace_append hprefix tailTrace_1186034
  have hstable : (prefixWord ++ tailWord_1186034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186034).length < 2 ^ (prefixWord ++ tailWord_1186034).sum := by decide
  have hdescent : baseEnd_1186034 < baseStart_1186034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186067 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 7, 2]
def baseStart_1186067 : Nat := 118140960795 + 1186067 * 2 ^ 59
def prefixEnd_1186067 : Nat := 4983230072969 + 3 ^ 40 * 1186067 * 2
def baseEnd_1186067 : Nat := 609022459436316241107883

theorem tailTrace_1186067 : CollatzResearch.WordTrace tailWord_1186067 prefixEnd_1186067 609022459436316241107883 := by
  unfold tailWord_1186067
  simp only [CollatzResearch.WordTrace]
  refine ⟨43259417394089297961756455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28839611596059531974504303 43259417394089297961756455)
  ·
    refine ⟨64889126091133946942634683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43259417394089297961756455 64889126091133946942634683)
    ·
      refine ⟨97333689136700920413952025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64889126091133946942634683 97333689136700920413952025)
      ·
        refine ⟨73000266852525690310464019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97333689136700920413952025 73000266852525690310464019)
        ·
          refine ⟨109500400278788535465696029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73000266852525690310464019 109500400278788535465696029)
          ·
            refine ⟨41062650104545700799636011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109500400278788535465696029 41062650104545700799636011)
            ·
              refine ⟨61593975156818551199454017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41062650104545700799636011 61593975156818551199454017)
              ·
                refine ⟨46195481367613913399590513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61593975156818551199454017 46195481367613913399590513)
                ·
                  refine ⟨34646611025710435049692885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46195481367613913399590513 34646611025710435049692885)
                  ·
                    refine ⟨812029945915088321477177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34646611025710435049692885 812029945915088321477177)
                    ·
                      refine ⟨609022459436316241107883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812029945915088321477177 609022459436316241107883)
                      ·
                        rfl

theorem cell23_1186067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7, 2].length) (baseStart_1186067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186067 prefixEnd_1186067 := by exact prefixLift 1186067
  have htrace : WordTrace (prefixWord ++ tailWord_1186067) baseStart_1186067 baseEnd_1186067 := by
    simpa [prefixWord, tailWord_1186067, baseEnd_1186067] using wordTrace_append hprefix tailTrace_1186067
  have hstable : (prefixWord ++ tailWord_1186067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186067).length < 2 ^ (prefixWord ++ tailWord_1186067).sum := by decide
  have hdescent : baseEnd_1186067 < baseStart_1186067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186078 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1186078 : Nat := 118140960795 + 1186078 * 2 ^ 59
def prefixEnd_1186078 : Nat := 4983230072969 + 3 ^ 40 * 1186078 * 2
def baseEnd_1186078 : Nat := 609028107723515698070333

theorem tailTrace_1186078 : CollatzResearch.WordTrace tailWord_1186078 prefixEnd_1186078 609028107723515698070333 := by
  unfold tailWord_1186078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407477324631180855050861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28839879064699631226937925 5407477324631180855050861)
  ·
    refine ⟨2027803996736692820644073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5407477324631180855050861 2027803996736692820644073)
    ·
      refine ⟨1520852997552519615483055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027803996736692820644073 1520852997552519615483055)
      ·
        refine ⟨2281279496328779423224583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520852997552519615483055 2281279496328779423224583)
        ·
          refine ⟨3421919244493169134836875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281279496328779423224583 3421919244493169134836875)
          ·
            refine ⟨5132878866739753702255313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421919244493169134836875 5132878866739753702255313)
            ·
              refine ⟨3849659150054815276691485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132878866739753702255313 3849659150054815276691485)
              ·
                refine ⟨1443622181270555728759307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849659150054815276691485 1443622181270555728759307)
                ·
                  refine ⟨2165433271905833593138961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443622181270555728759307 2165433271905833593138961)
                  ·
                    refine ⟨1624074953929375194854221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2165433271905833593138961 1624074953929375194854221)
                    ·
                      refine ⟨609028107723515698070333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1624074953929375194854221 609028107723515698070333)
                      ·
                        rfl

theorem cell23_1186078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1186078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186078 prefixEnd_1186078 := by exact prefixLift 1186078
  have htrace : WordTrace (prefixWord ++ tailWord_1186078) baseStart_1186078 baseEnd_1186078 := by
    simpa [prefixWord, tailWord_1186078, baseEnd_1186078] using wordTrace_append hprefix tailTrace_1186078
  have hstable : (prefixWord ++ tailWord_1186078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186078).length < 2 ^ (prefixWord ++ tailWord_1186078).sum := by decide
  have hdescent : baseEnd_1186078 < baseStart_1186078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186148 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_1186148 : Nat := 118140960795 + 1186148 * 2 ^ 59
def prefixEnd_1186148 : Nat := 4983230072969 + 3 ^ 40 * 1186148 * 2
def baseEnd_1186148 : Nat := 609064051369330424195011

theorem tailTrace_1186148 : CollatzResearch.WordTrace tailWord_1186148 prefixEnd_1186148 609064051369330424195011 := by
  unfold tailWord_1186148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21631185853397924397727549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28841581137863899196970065 21631185853397924397727549)
  ·
    refine ⟨8111694695024221649147831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21631185853397924397727549 8111694695024221649147831)
    ·
      refine ⟨12167542042536332473721747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8111694695024221649147831 12167542042536332473721747)
      ·
        refine ⟨18251313063804498710582621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12167542042536332473721747 18251313063804498710582621)
        ·
          refine ⟨6844242398926687016468483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18251313063804498710582621 6844242398926687016468483)
          ·
            refine ⟨10266363598390030524702725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844242398926687016468483 10266363598390030524702725)
            ·
              refine ⟨1924943174698130723381761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10266363598390030524702725 1924943174698130723381761)
              ·
                refine ⟨1443707381023598042536321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924943174698130723381761 1443707381023598042536321)
                ·
                  refine ⟨1082780535767698531902241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1443707381023598042536321 1082780535767698531902241)
                  ·
                    refine ⟨812085401825773898926681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1082780535767698531902241 812085401825773898926681)
                    ·
                      refine ⟨609064051369330424195011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812085401825773898926681 609064051369330424195011)
                      ·
                        rfl

theorem cell23_1186148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_1186148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186148 prefixEnd_1186148 := by exact prefixLift 1186148
  have htrace : WordTrace (prefixWord ++ tailWord_1186148) baseStart_1186148 baseEnd_1186148 := by
    simpa [prefixWord, tailWord_1186148, baseEnd_1186148] using wordTrace_append hprefix tailTrace_1186148
  have hstable : (prefixWord ++ tailWord_1186148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186148).length < 2 ^ (prefixWord ++ tailWord_1186148).sum := by decide
  have hdescent : baseEnd_1186148 < baseStart_1186148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186248 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 1, 4]
def baseStart_1186248 : Nat := 118140960795 + 1186248 * 2 ^ 59
def prefixEnd_1186248 : Nat := 4983230072969 + 3 ^ 40 * 1186248 * 2
def baseEnd_1186248 : Nat := 203038466478260010981517

theorem tailTrace_1186248 : CollatzResearch.WordTrace tailWord_1186248 prefixEnd_1186248 203038466478260010981517 := by
  unfold tailWord_1186248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21633009503216782937047699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28844012670955710582730265 21633009503216782937047699)
  ·
    refine ⟨32449514254825174405571549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21633009503216782937047699 32449514254825174405571549)
    ·
      refine ⟨12168567845559440402089331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32449514254825174405571549 12168567845559440402089331)
      ·
        refine ⟨18252851768339160603133997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12168567845559440402089331 18252851768339160603133997)
        ·
          refine ⟨6844819413127185226175249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18252851768339160603133997 6844819413127185226175249)
          ·
            refine ⟨5133614559845388919631437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6844819413127185226175249 5133614559845388919631437)
            ·
              refine ⟨1925105459942020844861789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5133614559845388919631437 1925105459942020844861789)
              ·
                refine ⟨721914547478257816823171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1925105459942020844861789 721914547478257816823171)
                ·
                  refine ⟨1082871821217386725234757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721914547478257816823171 1082871821217386725234757)
                  ·
                    refine ⟨203038466478260010981517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082871821217386725234757 203038466478260010981517)
                    ·
                      rfl

theorem cell23_1186248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_1186248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186248 prefixEnd_1186248 := by exact prefixLift 1186248
  have htrace : WordTrace (prefixWord ++ tailWord_1186248) baseStart_1186248 baseEnd_1186248 := by
    simpa [prefixWord, tailWord_1186248, baseEnd_1186248] using wordTrace_append hprefix tailTrace_1186248
  have hstable : (prefixWord ++ tailWord_1186248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186248).length < 2 ^ (prefixWord ++ tailWord_1186248).sum := by decide
  have hdescent : baseEnd_1186248 < baseStart_1186248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186358 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1186358 : Nat := 118140960795 + 1186358 * 2 ^ 59
def prefixEnd_1186358 : Nat := 4983230072969 + 3 ^ 40 * 1186358 * 2
def baseEnd_1186358 : Nat := 609171882306774602569045

theorem tailTrace_1186358 : CollatzResearch.WordTrace tailWord_1186358 prefixEnd_1186358 609171882306774602569045 := by
  unfold tailWord_1186358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704376939752190916287483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28846687357356703107066485 2704376939752190916287483)
  ·
    refine ⟨4056565409628286374431225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2704376939752190916287483 4056565409628286374431225)
    ·
      refine ⟨3042424057221214780823419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4056565409628286374431225 3042424057221214780823419)
      ·
        refine ⟨4563636085831822171235129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042424057221214780823419 4563636085831822171235129)
        ·
          refine ⟨3422727064373866628426347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4563636085831822171235129 3422727064373866628426347)
          ·
            refine ⟨5134090596560799942639521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422727064373866628426347 5134090596560799942639521)
            ·
              refine ⟨3850567947420599956979641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134090596560799942639521 3850567947420599956979641)
              ·
                refine ⟨2887925960565449967734731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850567947420599956979641 2887925960565449967734731)
                ·
                  refine ⟨4331888940848174951602097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887925960565449967734731 4331888940848174951602097)
                  ·
                    refine ⟨3248916705636131213701573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4331888940848174951602097 3248916705636131213701573)
                    ·
                      refine ⟨609171882306774602569045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3248916705636131213701573 609171882306774602569045)
                      ·
                        rfl

theorem cell23_1186358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1186358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186358 prefixEnd_1186358 := by exact prefixLift 1186358
  have htrace : WordTrace (prefixWord ++ tailWord_1186358) baseStart_1186358 baseEnd_1186358 := by
    simpa [prefixWord, tailWord_1186358, baseEnd_1186358] using wordTrace_append hprefix tailTrace_1186358
  have hstable : (prefixWord ++ tailWord_1186358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186358).length < 2 ^ (prefixWord ++ tailWord_1186358).sum := by decide
  have hdescent : baseEnd_1186358 < baseStart_1186358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186361 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1186361 : Nat := 118140960795 + 1186361 * 2 ^ 59
def prefixEnd_1186361 : Nat := 4983230072969 + 3 ^ 40 * 1186361 * 2
def baseEnd_1186361 : Nat := 609173422748738090831531

theorem tailTrace_1186361 : CollatzResearch.WordTrace tailWord_1186361 prefixEnd_1186361 609173422748738090831531 := by
  unfold tailWord_1186361
  simp only [CollatzResearch.WordTrace]
  refine ⟨43270140455024186172958937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28846760303349457448639291 43270140455024186172958937)
  ·
    refine ⟨32452605341268139629719203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43270140455024186172958937 32452605341268139629719203)
    ·
      refine ⟨48678908011902209444578805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32452605341268139629719203 48678908011902209444578805)
      ·
        refine ⟨4563647626115832135429263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48678908011902209444578805 4563647626115832135429263)
        ·
          refine ⟨6845471439173748203143895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4563647626115832135429263 6845471439173748203143895)
          ·
            refine ⟨10268207158760622304715843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6845471439173748203143895 10268207158760622304715843)
            ·
              refine ⟨15402310738140933457073765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10268207158760622304715843 15402310738140933457073765)
              ·
                refine ⟨2887933263401425023201331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15402310738140933457073765 2887933263401425023201331)
                ·
                  refine ⟨4331899895102137534801997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2887933263401425023201331 4331899895102137534801997)
                  ·
                    refine ⟨1624462460663301575550749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4331899895102137534801997 1624462460663301575550749)
                    ·
                      refine ⟨609173422748738090831531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1624462460663301575550749 609173422748738090831531)
                      ·
                        rfl

theorem cell23_1186361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1186361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186361 prefixEnd_1186361 := by exact prefixLift 1186361
  have htrace : WordTrace (prefixWord ++ tailWord_1186361) baseStart_1186361 baseEnd_1186361 := by
    simpa [prefixWord, tailWord_1186361, baseEnd_1186361] using wordTrace_append hprefix tailTrace_1186361
  have hstable : (prefixWord ++ tailWord_1186361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186361).length < 2 ^ (prefixWord ++ tailWord_1186361).sum := by decide
  have hdescent : baseEnd_1186361 < baseStart_1186361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186362 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2]
def baseStart_1186362 : Nat := 118140960795 + 1186362 * 2 ^ 59
def prefixEnd_1186362 : Nat := 4983230072969 + 3 ^ 40 * 1186362 * 2
def baseEnd_1186362 : Nat := 609173936229392586919027

theorem tailTrace_1186362 : CollatzResearch.WordTrace tailWord_1186362 prefixEnd_1186362 609173936229392586919027 := by
  unfold tailWord_1186362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10817544232005140835936335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28846784618680375562496893 10817544232005140835936335)
  ·
    refine ⟨16226316348007711253904503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10817544232005140835936335 16226316348007711253904503)
    ·
      refine ⟨24339474522011566880856755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16226316348007711253904503 24339474522011566880856755)
      ·
        refine ⟨36509211783017350321285133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24339474522011566880856755 36509211783017350321285133)
        ·
          refine ⟨13690954418631506370481925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36509211783017350321285133 13690954418631506370481925)
          ·
            refine ⟨2567053953493407444465361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13690954418631506370481925 2567053953493407444465361)
            ·
              refine ⟨1925290465120055583349021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2567053953493407444465361 1925290465120055583349021)
              ·
                refine ⟨721983924420020843755883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1925290465120055583349021 721983924420020843755883)
                ·
                  refine ⟨1082975886630031265633825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721983924420020843755883 1082975886630031265633825)
                  ·
                    refine ⟨812231914972523449225369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1082975886630031265633825 812231914972523449225369)
                    ·
                      refine ⟨609173936229392586919027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812231914972523449225369 609173936229392586919027)
                      ·
                        rfl

theorem cell23_1186362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_1186362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186362 prefixEnd_1186362 := by exact prefixLift 1186362
  have htrace : WordTrace (prefixWord ++ tailWord_1186362) baseStart_1186362 baseEnd_1186362 := by
    simpa [prefixWord, tailWord_1186362, baseEnd_1186362] using wordTrace_append hprefix tailTrace_1186362
  have hstable : (prefixWord ++ tailWord_1186362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186362).length < 2 ^ (prefixWord ++ tailWord_1186362).sum := by decide
  have hdescent : baseEnd_1186362 < baseStart_1186362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186365 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_1186365 : Nat := 118140960795 + 1186365 * 2 ^ 59
def prefixEnd_1186365 : Nat := 4983230072969 + 3 ^ 40 * 1186365 * 2
def baseEnd_1186365 : Nat := 609175476671356075181513

theorem tailTrace_1186365 : CollatzResearch.WordTrace tailWord_1186365 prefixEnd_1186365 609175476671356075181513 := by
  unfold tailWord_1186365
  simp only [CollatzResearch.WordTrace]
  refine ⟨43270286347009694856104549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28846857564673129904069699 43270286347009694856104549)
  ·
    refine ⟨8113178690064317785519603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43270286347009694856104549 8113178690064317785519603)
    ·
      refine ⟨12169768035096476678279405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8113178690064317785519603 12169768035096476678279405)
      ·
        refine ⟨4563663013161178754354777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12169768035096476678279405 4563663013161178754354777)
        ·
          refine ⟨3422747259870884065766083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4563663013161178754354777 3422747259870884065766083)
          ·
            refine ⟨5134120889806326098649125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422747259870884065766083 5134120889806326098649125)
            ·
              refine ⟨962647666838686143496711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5134120889806326098649125 962647666838686143496711)
              ·
                refine ⟨1443971500258029215245067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962647666838686143496711 1443971500258029215245067)
                ·
                  refine ⟨2165957250387043822867601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443971500258029215245067 2165957250387043822867601)
                  ·
                    refine ⟨1624467937790282867150701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2165957250387043822867601 1624467937790282867150701)
                    ·
                      refine ⟨609175476671356075181513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1624467937790282867150701 609175476671356075181513)
                      ·
                        rfl

theorem cell23_1186365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_1186365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186365 prefixEnd_1186365 := by exact prefixLift 1186365
  have htrace : WordTrace (prefixWord ++ tailWord_1186365) baseStart_1186365 baseEnd_1186365 := by
    simpa [prefixWord, tailWord_1186365, baseEnd_1186365] using wordTrace_append hprefix tailTrace_1186365
  have hstable : (prefixWord ++ tailWord_1186365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186365).length < 2 ^ (prefixWord ++ tailWord_1186365).sum := by decide
  have hdescent : baseEnd_1186365 < baseStart_1186365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186372 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1186372 : Nat := 118140960795 + 1186372 * 2 ^ 59
def prefixEnd_1186372 : Nat := 4983230072969 + 3 ^ 40 * 1186372 * 2
def baseEnd_1186372 : Nat := 203059690345312515931327

theorem tailTrace_1186372 : CollatzResearch.WordTrace tailWord_1186372 prefixEnd_1186372 203059690345312515931327 := by
  unfold tailWord_1186372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21635270828992167525804685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28847027771989556701072913 21635270828992167525804685)
  ·
    refine ⟨8113226560872062822176757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21635270828992167525804685 8113226560872062822176757)
    ·
      refine ⟨760614990081755889579071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8113226560872062822176757 760614990081755889579071)
      ·
        refine ⟨1140922485122633834368607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760614990081755889579071 1140922485122633834368607)
        ·
          refine ⟨1711383727683950751552911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140922485122633834368607 1711383727683950751552911)
          ·
            refine ⟨2567075591525926127329367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711383727683950751552911 2567075591525926127329367)
            ·
              refine ⟨3850613387288889190994051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567075591525926127329367 3850613387288889190994051)
              ·
                refine ⟨5775920080933333786491077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850613387288889190994051 5775920080933333786491077)
                ·
                  refine ⟨1082985015175000084967077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5775920080933333786491077 1082985015175000084967077)
                  ·
                    refine ⟨203059690345312515931327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1082985015175000084967077 203059690345312515931327)
                    ·
                      rfl

theorem cell23_1186372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1186372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186372 prefixEnd_1186372 := by exact prefixLift 1186372
  have htrace : WordTrace (prefixWord ++ tailWord_1186372) baseStart_1186372 baseEnd_1186372 := by
    simpa [prefixWord, tailWord_1186372, baseEnd_1186372] using wordTrace_append hprefix tailTrace_1186372
  have hstable : (prefixWord ++ tailWord_1186372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186372).length < 2 ^ (prefixWord ++ tailWord_1186372).sum := by decide
  have hdescent : baseEnd_1186372 < baseStart_1186372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186378 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1186378 : Nat := 118140960795 + 1186378 * 2 ^ 59
def prefixEnd_1186378 : Nat := 4983230072969 + 3 ^ 40 * 1186378 * 2
def baseEnd_1186378 : Nat := 609182151919864524318953

theorem tailTrace_1186378 : CollatzResearch.WordTrace tailWord_1186378 prefixEnd_1186378 609182151919864524318953 := by
  unfold tailWord_1186378
  simp only [CollatzResearch.WordTrace]
  refine ⟨10817690123990649519081947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28847173663975065384218525 10817690123990649519081947)
  ·
    refine ⟨16226535185985974278622921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10817690123990649519081947 16226535185985974278622921)
    ·
      refine ⟨12169901389489480708967191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16226535185985974278622921 12169901389489480708967191)
      ·
        refine ⟨18254852084234221063450787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169901389489480708967191 18254852084234221063450787)
        ·
          refine ⟨27382278126351331595176181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18254852084234221063450787 27382278126351331595176181)
          ·
            refine ⟨2567088574345437337047767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27382278126351331595176181 2567088574345437337047767)
            ·
              refine ⟨3850632861518156005571651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567088574345437337047767 3850632861518156005571651)
              ·
                refine ⟨5775949292277234008357477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3850632861518156005571651 5775949292277234008357477)
                ·
                  refine ⟨1082990492301981376567027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5775949292277234008357477 1082990492301981376567027)
                  ·
                    refine ⟨1624485738452972064850541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1082990492301981376567027 1624485738452972064850541)
                    ·
                      refine ⟨609182151919864524318953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1624485738452972064850541 609182151919864524318953)
                      ·
                        rfl

theorem cell23_1186378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1186378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186378 prefixEnd_1186378 := by exact prefixLift 1186378
  have htrace : WordTrace (prefixWord ++ tailWord_1186378) baseStart_1186378 baseEnd_1186378 := by
    simpa [prefixWord, tailWord_1186378, baseEnd_1186378] using wordTrace_append hprefix tailTrace_1186378
  have hstable : (prefixWord ++ tailWord_1186378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186378).length < 2 ^ (prefixWord ++ tailWord_1186378).sum := by decide
  have hdescent : baseEnd_1186378 < baseStart_1186378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186384 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_1186384 : Nat := 118140960795 + 1186384 * 2 ^ 59
def prefixEnd_1186384 : Nat := 4983230072969 + 3 ^ 40 * 1186384 * 2
def baseEnd_1186384 : Nat := 609185232803791500843925

theorem tailTrace_1186384 : CollatzResearch.WordTrace tailWord_1186384 prefixEnd_1186384 609185232803791500843925 := by
  unfold tailWord_1186384
  simp only [CollatzResearch.WordTrace]
  refine ⟨21635489666970430550523103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28847319555960574067364137 21635489666970430550523103)
  ·
    refine ⟨32453234500455645825784655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21635489666970430550523103 32453234500455645825784655)
    ·
      refine ⟨48679851750683468738676983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32453234500455645825784655 48679851750683468738676983)
      ·
        refine ⟨73019777626025203108015475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48679851750683468738676983 73019777626025203108015475)
        ·
          refine ⟨109529666439037804662023213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73019777626025203108015475 109529666439037804662023213)
          ·
            refine ⟨41073624914639176748258705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109529666439037804662023213 41073624914639176748258705)
            ·
              refine ⟨30805218685979382561194029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41073624914639176748258705 30805218685979382561194029)
              ·
                refine ⟨11551957007242268460447761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30805218685979382561194029 11551957007242268460447761)
                ·
                  refine ⟨8663967755431701345335821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11551957007242268460447761 8663967755431701345335821)
                  ·
                    refine ⟨3248987908286888004500933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8663967755431701345335821 3248987908286888004500933)
                    ·
                      refine ⟨609185232803791500843925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3248987908286888004500933 609185232803791500843925)
                      ·
                        rfl

theorem cell23_1186384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_1186384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186384 prefixEnd_1186384 := by exact prefixLift 1186384
  have htrace : WordTrace (prefixWord ++ tailWord_1186384) baseStart_1186384 baseEnd_1186384 := by
    simpa [prefixWord, tailWord_1186384, baseEnd_1186384] using wordTrace_append hprefix tailTrace_1186384
  have hstable : (prefixWord ++ tailWord_1186384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186384).length < 2 ^ (prefixWord ++ tailWord_1186384).sum := by decide
  have hdescent : baseEnd_1186384 < baseStart_1186384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186402 : List Nat := [3, 3, 2, 3, 2, 1, 2, 7]
def baseStart_1186402 : Nat := 118140960795 + 1186402 * 2 ^ 59
def prefixEnd_1186402 : Nat := 4983230072969 + 3 ^ 40 * 1186402 * 2
def baseEnd_1186402 : Nat := 22562758350206386311809

theorem tailTrace_1186402 : CollatzResearch.WordTrace tailWord_1186402 prefixEnd_1186402 22562758350206386311809 := by
  unfold tailWord_1186402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10817908961968912543800365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28847757231917100116800973 10817908961968912543800365)
  ·
    refine ⟨4056715860738342203925137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10817908961968912543800365 4056715860738342203925137)
    ·
      refine ⟨3042536895553756652943853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4056715860738342203925137 3042536895553756652943853)
      ·
        refine ⟨1140951335832658744853945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3042536895553756652943853 1140951335832658744853945)
        ·
          refine ⟨855713501874494058640459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140951335832658744853945 855713501874494058640459)
          ·
            refine ⟨1283570252811741087960689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855713501874494058640459 1283570252811741087960689)
            ·
              refine ⟨962677689608805815970517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283570252811741087960689 962677689608805815970517)
              ·
                refine ⟨22562758350206386311809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 962677689608805815970517 22562758350206386311809)
                ·
                  rfl

theorem cell23_1186402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_1186402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186402 prefixEnd_1186402 := by exact prefixLift 1186402
  have htrace : WordTrace (prefixWord ++ tailWord_1186402) baseStart_1186402 baseEnd_1186402 := by
    simpa [prefixWord, tailWord_1186402, baseEnd_1186402] using wordTrace_append hprefix tailTrace_1186402
  have hstable : (prefixWord ++ tailWord_1186402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186402).length < 2 ^ (prefixWord ++ tailWord_1186402).sum := by decide
  have hdescent : baseEnd_1186402 < baseStart_1186402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186444 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1186444 : Nat := 118140960795 + 1186444 * 2 ^ 59
def prefixEnd_1186444 : Nat := 4983230072969 + 3 ^ 40 * 1186444 * 2
def baseEnd_1186444 : Nat := 609216041643061266093649

theorem tailTrace_1186444 : CollatzResearch.WordTrace tailWord_1186444 prefixEnd_1186444 609216041643061266093649 := by
  unfold tailWord_1186444
  simp only [CollatzResearch.WordTrace]
  refine ⟨21636583856861745674115193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28848778475815660898820257 21636583856861745674115193)
  ·
    refine ⟨16227437892646309255586395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21636583856861745674115193 16227437892646309255586395)
    ·
      refine ⟨24341156838969463883379593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16227437892646309255586395 24341156838969463883379593)
      ·
        refine ⟨18255867629227097912534695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24341156838969463883379593 18255867629227097912534695)
        ·
          refine ⟨27383801443840646868802043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18255867629227097912534695 27383801443840646868802043)
          ·
            refine ⟨41075702165760970303203065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27383801443840646868802043 41075702165760970303203065)
            ·
              refine ⟨30806776624320727727402299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41075702165760970303203065 30806776624320727727402299)
              ·
                refine ⟨46210164936481091591103449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30806776624320727727402299 46210164936481091591103449)
                ·
                  refine ⟨34657623702360818693327587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46210164936481091591103449 34657623702360818693327587)
                  ·
                    refine ⟨51986435553541228039991381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34657623702360818693327587 51986435553541228039991381)
                    ·
                      refine ⟨609216041643061266093649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 51986435553541228039991381 609216041643061266093649)
                      ·
                        rfl

theorem cell23_1186444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1186444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186444 prefixEnd_1186444 := by exact prefixLift 1186444
  have htrace : WordTrace (prefixWord ++ tailWord_1186444) baseStart_1186444 baseEnd_1186444 := by
    simpa [prefixWord, tailWord_1186444, baseEnd_1186444] using wordTrace_append hprefix tailTrace_1186444
  have hstable : (prefixWord ++ tailWord_1186444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186444).length < 2 ^ (prefixWord ++ tailWord_1186444).sum := by decide
  have hdescent : baseEnd_1186444 < baseStart_1186444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186486 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1186486 : Nat := 118140960795 + 1186486 * 2 ^ 59
def prefixEnd_1186486 : Nat := 4983230072969 + 3 ^ 40 * 1186486 * 2
def baseEnd_1186486 : Nat := 609237607830550101768457

theorem tailTrace_1186486 : CollatzResearch.WordTrace tailWord_1186486 prefixEnd_1186486 609237607830550101768457 := by
  unfold tailWord_1186486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704668723723208282578707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28849799719714221680839541 2704668723723208282578707)
  ·
    refine ⟨4057003085584812423868061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2704668723723208282578707 4057003085584812423868061)
    ·
      refine ⟨1521376157094304658950523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4057003085584812423868061 1521376157094304658950523)
      ·
        refine ⟨2282064235641456988425785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521376157094304658950523 2282064235641456988425785)
        ·
          refine ⟨1711548176731092741319339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282064235641456988425785 1711548176731092741319339)
          ·
            refine ⟨2567322265096639111979009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711548176731092741319339 2567322265096639111979009)
            ·
              refine ⟨1925491698822479333984257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2567322265096639111979009 1925491698822479333984257)
              ·
                refine ⟨1444118774116859500488193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925491698822479333984257 1444118774116859500488193)
                ·
                  refine ⟨1083089080587644625366145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1444118774116859500488193 1083089080587644625366145)
                  ·
                    refine ⟨812316810440733469024609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1083089080587644625366145 812316810440733469024609)
                    ·
                      refine ⟨609237607830550101768457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812316810440733469024609 609237607830550101768457)
                      ·
                        rfl

theorem cell23_1186486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1186486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186486 prefixEnd_1186486 := by exact prefixLift 1186486
  have htrace : WordTrace (prefixWord ++ tailWord_1186486) baseStart_1186486 baseEnd_1186486 := by
    simpa [prefixWord, tailWord_1186486, baseEnd_1186486] using wordTrace_append hprefix tailTrace_1186486
  have hstable : (prefixWord ++ tailWord_1186486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186486).length < 2 ^ (prefixWord ++ tailWord_1186486).sum := by decide
  have hdescent : baseEnd_1186486 < baseStart_1186486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_1186601 : Nat := 118140960795 + 1186601 * 2 ^ 59
def prefixEnd_1186601 : Nat := 4983230072969 + 3 ^ 40 * 1186601 * 2
def baseEnd_1186601 : Nat := 609296658105817151830427

theorem tailTrace_1186601 : CollatzResearch.WordTrace tailWord_1186601 prefixEnd_1186601 609296658105817151830427 := by
  unfold tailWord_1186601
  simp only [CollatzResearch.WordTrace]
  refine ⟨43278893974154707161695657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28852595982769804774463771 43278893974154707161695657)
  ·
    refine ⟨32459170480616030371271743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43278893974154707161695657 32459170480616030371271743)
    ·
      refine ⟨48688755720924045556907615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32459170480616030371271743 48688755720924045556907615)
      ·
        refine ⟨73033133581386068335361423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48688755720924045556907615 73033133581386068335361423)
        ·
          refine ⟨109549700372079102503042135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73033133581386068335361423 109549700372079102503042135)
          ·
            refine ⟨164324550558118653754563203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109549700372079102503042135 164324550558118653754563203)
            ·
              refine ⟨246486825837177980631844805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164324550558118653754563203 246486825837177980631844805)
              ·
                refine ⟨46216279844470871368470901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246486825837177980631844805 46216279844470871368470901)
                ·
                  refine ⟨4332776235419144190794147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46216279844470871368470901 4332776235419144190794147)
                  ·
                    refine ⟨6499164353128716286191221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4332776235419144190794147 6499164353128716286191221)
                    ·
                      refine ⟨609296658105817151830427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6499164353128716286191221 609296658105817151830427)
                      ·
                        rfl

theorem cell23_1186601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_1186601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186601 prefixEnd_1186601 := by exact prefixLift 1186601
  have htrace : WordTrace (prefixWord ++ tailWord_1186601) baseStart_1186601 baseEnd_1186601 := by
    simpa [prefixWord, tailWord_1186601, baseEnd_1186601] using wordTrace_append hprefix tailTrace_1186601
  have hstable : (prefixWord ++ tailWord_1186601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186601).length < 2 ^ (prefixWord ++ tailWord_1186601).sum := by decide
  have hdescent : baseEnd_1186601 < baseStart_1186601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186609 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 1, 1, 3]
def baseStart_1186609 : Nat := 118140960795 + 1186609 * 2 ^ 59
def prefixEnd_1186609 : Nat := 4983230072969 + 3 ^ 40 * 1186609 * 2
def baseEnd_1186609 : Nat := 609300765951053120530391

theorem tailTrace_1186609 : CollatzResearch.WordTrace tailWord_1186609 prefixEnd_1186609 609300765951053120530391 := by
  unfold tailWord_1186609
  simp only [CollatzResearch.WordTrace]
  refine ⟨43279185758125724527986881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28852790505417149685324587 43279185758125724527986881)
  ·
    refine ⟨32459389318594293395990161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43279185758125724527986881 32459389318594293395990161)
    ·
      refine ⟨24344541988945720046992621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32459389318594293395990161 24344541988945720046992621)
      ·
        refine ⟨9129203245854645017622233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24344541988945720046992621 9129203245854645017622233)
        ·
          refine ⟨6846902434390983763216675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9129203245854645017622233 6846902434390983763216675)
          ·
            refine ⟨10270353651586475644825013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6846902434390983763216675 10270353651586475644825013)
            ·
              refine ⟨962845654836232091702345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10270353651586475644825013 962845654836232091702345)
              ·
                refine ⟨722134241127174068776759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962845654836232091702345 722134241127174068776759)
                ·
                  refine ⟨1083201361690761103165139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722134241127174068776759 1083201361690761103165139)
                  ·
                    refine ⟨1624802042536141654747709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1083201361690761103165139 1624802042536141654747709)
                    ·
                      refine ⟨609300765951053120530391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1624802042536141654747709 609300765951053120530391)
                      ·
                        rfl

theorem cell23_1186609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_1186609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186609 prefixEnd_1186609 := by exact prefixLift 1186609
  have htrace : WordTrace (prefixWord ++ tailWord_1186609) baseStart_1186609 baseEnd_1186609 := by
    simpa [prefixWord, tailWord_1186609, baseEnd_1186609] using wordTrace_append hprefix tailTrace_1186609
  have hstable : (prefixWord ++ tailWord_1186609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186609).length < 2 ^ (prefixWord ++ tailWord_1186609).sum := by decide
  have hdescent : baseEnd_1186609 < baseStart_1186609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186652 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1186652 : Nat := 118140960795 + 1186652 * 2 ^ 59
def prefixEnd_1186652 : Nat := 4983230072969 + 3 ^ 40 * 1186652 * 2
def baseEnd_1186652 : Nat := 609322845619196452292693

theorem tailTrace_1186652 : CollatzResearch.WordTrace tailWord_1186652 prefixEnd_1186652 609322845619196452292693 := by
  unfold tailWord_1186652
  simp only [CollatzResearch.WordTrace]
  refine ⟨21640377048484971435901105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28853836064646628581201473 21640377048484971435901105)
  ·
    refine ⟨16230282786363728576925829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21640377048484971435901105 16230282786363728576925829)
    ·
      refine ⟨3043178022443199108173593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16230282786363728576925829 3043178022443199108173593)
      ·
        refine ⟨2282383516832399331130195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3043178022443199108173593 2282383516832399331130195)
        ·
          refine ⟨3423575275248598996695293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282383516832399331130195 3423575275248598996695293)
          ·
            refine ⟨1283840728218224623760735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3423575275248598996695293 1283840728218224623760735)
            ·
              refine ⟨1925761092327336935641103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283840728218224623760735 1925761092327336935641103)
              ·
                refine ⟨2888641638491005403461655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925761092327336935641103 2888641638491005403461655)
                ·
                  refine ⟨4332962457736508105192483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2888641638491005403461655 4332962457736508105192483)
                  ·
                    refine ⟨6499443686604762157788725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4332962457736508105192483 6499443686604762157788725)
                    ·
                      refine ⟨609322845619196452292693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6499443686604762157788725 609322845619196452292693)
                      ·
                        rfl

theorem cell23_1186652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1186652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186652 prefixEnd_1186652 := by exact prefixLift 1186652
  have htrace : WordTrace (prefixWord ++ tailWord_1186652) baseStart_1186652 baseEnd_1186652 := by
    simpa [prefixWord, tailWord_1186652, baseEnd_1186652] using wordTrace_append hprefix tailTrace_1186652
  have hstable : (prefixWord ++ tailWord_1186652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186652).length < 2 ^ (prefixWord ++ tailWord_1186652).sum := by decide
  have hdescent : baseEnd_1186652 < baseStart_1186652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186675 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 3, 3, 2]
def baseStart_1186675 : Nat := 118140960795 + 1186675 * 2 ^ 59
def prefixEnd_1186675 : Nat := 4983230072969 + 3 ^ 40 * 1186675 * 2
def baseEnd_1186675 : Nat := 609334655674249862305087

theorem tailTrace_1186675 : CollatzResearch.WordTrace tailWord_1186675 prefixEnd_1186675 609334655674249862305087 := by
  unfold tailWord_1186675
  simp only [CollatzResearch.WordTrace]
  refine ⟨43281592975886617799889479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28854395317257745199926319 43281592975886617799889479)
  ·
    refine ⟨64922389463829926699834219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43281592975886617799889479 64922389463829926699834219)
    ·
      refine ⟨97383584195744890049751329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64922389463829926699834219 97383584195744890049751329)
      ·
        refine ⟨73037688146808667537313497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97383584195744890049751329 73037688146808667537313497)
        ·
          refine ⟨54778266110106500652985123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73037688146808667537313497 54778266110106500652985123)
          ·
            refine ⟨82167399165159750979477685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54778266110106500652985123 82167399165159750979477685)
            ·
              refine ⟨7703193671733726654326033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82167399165159750979477685 7703193671733726654326033)
              ·
                refine ⟨5777395253800294990744525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7703193671733726654326033 5777395253800294990744525)
                ·
                  refine ⟨2166523220175110621529197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5777395253800294990744525 2166523220175110621529197)
                  ·
                    refine ⟨812446207565666483073449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2166523220175110621529197 812446207565666483073449)
                    ·
                      refine ⟨609334655674249862305087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812446207565666483073449 609334655674249862305087)
                      ·
                        rfl

theorem cell23_1186675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3, 2].length) (baseStart_1186675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186675 prefixEnd_1186675 := by exact prefixLift 1186675
  have htrace : WordTrace (prefixWord ++ tailWord_1186675) baseStart_1186675 baseEnd_1186675 := by
    simpa [prefixWord, tailWord_1186675, baseEnd_1186675] using wordTrace_append hprefix tailTrace_1186675
  have hstable : (prefixWord ++ tailWord_1186675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186675).length < 2 ^ (prefixWord ++ tailWord_1186675).sum := by decide
  have hdescent : baseEnd_1186675 < baseStart_1186675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186692 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_1186692 : Nat := 118140960795 + 1186692 * 2 ^ 59
def prefixEnd_1186692 : Nat := 4983230072969 + 3 ^ 40 * 1186692 * 2
def baseEnd_1186692 : Nat := 609343384845376295792509

theorem tailTrace_1186692 : CollatzResearch.WordTrace tailWord_1186692 prefixEnd_1186692 609343384845376295792509 := by
  unfold tailWord_1186692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21641106508412514851629165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28854808677883353135505553 21641106508412514851629165)
  ·
    refine ⟨8115414940654693069360937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21641106508412514851629165 8115414940654693069360937)
    ·
      refine ⟨6086561205491019802020703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8115414940654693069360937 6086561205491019802020703)
      ·
        refine ⟨9129841808236529703031055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6086561205491019802020703 9129841808236529703031055)
        ·
          refine ⟨13694762712354794554546583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9129841808236529703031055 13694762712354794554546583)
          ·
            refine ⟨20542144068532191831819875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13694762712354794554546583 20542144068532191831819875)
            ·
              refine ⟨30813216102798287747729813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20542144068532191831819875 30813216102798287747729813)
              ·
                refine ⟨1444369504818669738174835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30813216102798287747729813 1444369504818669738174835)
                ·
                  refine ⟨2166554257228004607262253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444369504818669738174835 2166554257228004607262253)
                  ·
                    refine ⟨812457846460501727723345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2166554257228004607262253 812457846460501727723345)
                    ·
                      refine ⟨609343384845376295792509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812457846460501727723345 609343384845376295792509)
                      ·
                        rfl

theorem cell23_1186692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_1186692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186692 prefixEnd_1186692 := by exact prefixLift 1186692
  have htrace : WordTrace (prefixWord ++ tailWord_1186692) baseStart_1186692 baseEnd_1186692 := by
    simpa [prefixWord, tailWord_1186692, baseEnd_1186692] using wordTrace_append hprefix tailTrace_1186692
  have hstable : (prefixWord ++ tailWord_1186692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186692).length < 2 ^ (prefixWord ++ tailWord_1186692).sum := by decide
  have hdescent : baseEnd_1186692 < baseStart_1186692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186709 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_1186709 : Nat := 118140960795 + 1186709 * 2 ^ 59
def prefixEnd_1186709 : Nat := 4983230072969 + 3 ^ 40 * 1186709 * 2
def baseEnd_1186709 : Nat := 609352114016502729279931

theorem tailTrace_1186709 : CollatzResearch.WordTrace tailWord_1186709 prefixEnd_1186709 609352114016502729279931 := by
  unfold tailWord_1186709
  simp only [CollatzResearch.WordTrace]
  refine ⟨43282833057763441606627181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28855222038508961071084787 43282833057763441606627181)
  ·
    refine ⟨16231062396661290602485193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43282833057763441606627181 16231062396661290602485193)
    ·
      refine ⟨12173296797495967951863895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16231062396661290602485193 12173296797495967951863895)
      ·
        refine ⟨18259945196243951927795843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12173296797495967951863895 18259945196243951927795843)
        ·
          refine ⟨27389917794365927891693765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18259945196243951927795843 27389917794365927891693765)
          ·
            refine ⟨5135609586443611479692581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27389917794365927891693765 5135609586443611479692581)
            ·
              refine ⟨962926797458177152442359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5135609586443611479692581 962926797458177152442359)
              ·
                refine ⟨1444390196187265728663539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962926797458177152442359 1444390196187265728663539)
                ·
                  refine ⟨2166585294280898592995309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444390196187265728663539 2166585294280898592995309)
                  ·
                    refine ⟨812469485355336972373241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2166585294280898592995309 812469485355336972373241)
                    ·
                      refine ⟨609352114016502729279931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812469485355336972373241 609352114016502729279931)
                      ·
                        rfl

theorem cell23_1186709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_1186709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186709 prefixEnd_1186709 := by exact prefixLift 1186709
  have htrace : WordTrace (prefixWord ++ tailWord_1186709) baseStart_1186709 baseEnd_1186709 := by
    simpa [prefixWord, tailWord_1186709, baseEnd_1186709] using wordTrace_append hprefix tailTrace_1186709
  have hstable : (prefixWord ++ tailWord_1186709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186709).length < 2 ^ (prefixWord ++ tailWord_1186709).sum := by decide
  have hdescent : baseEnd_1186709 < baseStart_1186709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186716 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1186716 : Nat := 118140960795 + 1186716 * 2 ^ 59
def prefixEnd_1186716 : Nat := 4983230072969 + 3 ^ 40 * 1186716 * 2
def baseEnd_1186716 : Nat := 609355708381084201892399

theorem tailTrace_1186716 : CollatzResearch.WordTrace tailWord_1186716 prefixEnd_1186716 609355708381084201892399 := by
  unfold tailWord_1186716
  simp only [CollatzResearch.WordTrace]
  refine ⟨21641544184369040901066001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28855392245825387868088001 21641544184369040901066001)
  ·
    refine ⟨16231158138276780675799501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21641544184369040901066001 16231158138276780675799501)
    ·
      refine ⟨6086684301853792753424813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16231158138276780675799501 6086684301853792753424813)
      ·
        refine ⟨2282506613195172282534305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6086684301853792753424813 2282506613195172282534305)
        ·
          refine ⟨1711879959896379211900729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282506613195172282534305 1711879959896379211900729)
          ·
            refine ⟨1283909969922284408925547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1711879959896379211900729 1283909969922284408925547)
            ·
              refine ⟨1925864954883426613388321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283909969922284408925547 1925864954883426613388321)
              ·
                refine ⟨1444398716162569960041241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925864954883426613388321 1444398716162569960041241)
                ·
                  refine ⟨1083299037121927470030931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1444398716162569960041241 1083299037121927470030931)
                  ·
                    refine ⟨1624948555682891205046397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1083299037121927470030931 1624948555682891205046397)
                    ·
                      refine ⟨609355708381084201892399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1624948555682891205046397 609355708381084201892399)
                      ·
                        rfl

theorem cell23_1186716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1186716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186716 prefixEnd_1186716 := by exact prefixLift 1186716
  have htrace : WordTrace (prefixWord ++ tailWord_1186716) baseStart_1186716 baseEnd_1186716 := by
    simpa [prefixWord, tailWord_1186716, baseEnd_1186716] using wordTrace_append hprefix tailTrace_1186716
  have hstable : (prefixWord ++ tailWord_1186716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186716).length < 2 ^ (prefixWord ++ tailWord_1186716).sum := by decide
  have hdescent : baseEnd_1186716 < baseStart_1186716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186733 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1186733 : Nat := 118140960795 + 1186733 * 2 ^ 59
def prefixEnd_1186733 : Nat := 4983230072969 + 3 ^ 40 * 1186733 * 2
def baseEnd_1186733 : Nat := 609364437552210635379821

theorem tailTrace_1186733 : CollatzResearch.WordTrace tailWord_1186733 prefixEnd_1186733 609364437552210635379821 := by
  unfold tailWord_1186733
  simp only [CollatzResearch.WordTrace]
  refine ⟨43283708409676493705500853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28855805606450995803667235 43283708409676493705500853)
  ·
    refine ⟨4057847663407171284890705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43283708409676493705500853 4057847663407171284890705)
    ·
      refine ⟨3043385747555378463668029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4057847663407171284890705 3043385747555378463668029)
      ·
        refine ⟨1141269655333266923875511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3043385747555378463668029 1141269655333266923875511)
        ·
          refine ⟨1711904482999900385813267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141269655333266923875511 1711904482999900385813267)
          ·
            refine ⟨2567856724499850578719901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711904482999900385813267 2567856724499850578719901)
            ·
              refine ⟨962946271687443967019963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2567856724499850578719901 962946271687443967019963)
              ·
                refine ⟨1444419407531165950529945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962946271687443967019963 1444419407531165950529945)
                ·
                  refine ⟨1083314555648374462897459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1444419407531165950529945 1083314555648374462897459)
                  ·
                    refine ⟨1624971833472561694346189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1083314555648374462897459 1624971833472561694346189)
                    ·
                      refine ⟨609364437552210635379821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1624971833472561694346189 609364437552210635379821)
                      ·
                        rfl

theorem cell23_1186733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1186733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186733 prefixEnd_1186733 := by exact prefixLift 1186733
  have htrace : WordTrace (prefixWord ++ tailWord_1186733) baseStart_1186733 baseEnd_1186733 := by
    simpa [prefixWord, tailWord_1186733, baseEnd_1186733] using wordTrace_append hprefix tailTrace_1186733
  have hstable : (prefixWord ++ tailWord_1186733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186733).length < 2 ^ (prefixWord ++ tailWord_1186733).sum := by decide
  have hdescent : baseEnd_1186733 < baseStart_1186733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186768 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_1186768 : Nat := 118140960795 + 1186768 * 2 ^ 59
def prefixEnd_1186768 : Nat := 4983230072969 + 3 ^ 40 * 1186768 * 2
def baseEnd_1186768 : Nat := 609382409375117998442159

theorem tailTrace_1186768 : CollatzResearch.WordTrace tailWord_1186768 prefixEnd_1186768 609382409375117998442159 := by
  unfold tailWord_1186768
  simp only [CollatzResearch.WordTrace]
  refine ⟨21642492482274847341512479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28856656643033129788683305 21642492482274847341512479)
  ·
    refine ⟨32463738723412271012268719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21642492482274847341512479 32463738723412271012268719)
    ·
      refine ⟨48695608085118406518403079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32463738723412271012268719 48695608085118406518403079)
      ·
        refine ⟨73043412127677609777604619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48695608085118406518403079 73043412127677609777604619)
        ·
          refine ⟨109565118191516414666406929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73043412127677609777604619 109565118191516414666406929)
          ·
            refine ⟨82173838643637310999805197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109565118191516414666406929 82173838643637310999805197)
            ·
              refine ⟨30815189491363991624926949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82173838643637310999805197 30815189491363991624926949)
              ·
                refine ⟨5777848029630748429673803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30815189491363991624926949 5777848029630748429673803)
                ·
                  refine ⟨8666772044446122644510705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5777848029630748429673803 8666772044446122644510705)
                  ·
                    refine ⟨6500079033334591983383029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8666772044446122644510705 6500079033334591983383029)
                    ·
                      refine ⟨609382409375117998442159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6500079033334591983383029 609382409375117998442159)
                      ·
                        rfl

theorem cell23_1186768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_1186768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186768 prefixEnd_1186768 := by exact prefixLift 1186768
  have htrace : WordTrace (prefixWord ++ tailWord_1186768) baseStart_1186768 baseEnd_1186768 := by
    simpa [prefixWord, tailWord_1186768, baseEnd_1186768] using wordTrace_append hprefix tailTrace_1186768
  have hstable : (prefixWord ++ tailWord_1186768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186768).length < 2 ^ (prefixWord ++ tailWord_1186768).sum := by decide
  have hdescent : baseEnd_1186768 < baseStart_1186768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186788 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_1186788 : Nat := 118140960795 + 1186788 * 2 ^ 59
def prefixEnd_1186788 : Nat := 4983230072969 + 3 ^ 40 * 1186788 * 2
def baseEnd_1186788 : Nat := 203130892996069306730689

theorem tailTrace_1186788 : CollatzResearch.WordTrace tailWord_1186788 prefixEnd_1186788 203130892996069306730689 := by
  unfold tailWord_1186788
  simp only [CollatzResearch.WordTrace]
  refine ⟨21642857212238619049376509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28857142949651492065835345 21642857212238619049376509)
  ·
    refine ⟨8116071454589482143516191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21642857212238619049376509 8116071454589482143516191)
    ·
      refine ⟨12174107181884223215274287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116071454589482143516191 12174107181884223215274287)
      ·
        refine ⟨18261160772826334822911431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12174107181884223215274287 18261160772826334822911431)
        ·
          refine ⟨27391741159239502234367147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18261160772826334822911431 27391741159239502234367147)
          ·
            refine ⟨41087611738859253351550721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27391741159239502234367147 41087611738859253351550721)
            ·
              refine ⟨30815708804144440013663041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41087611738859253351550721 30815708804144440013663041)
              ·
                refine ⟨23111781603108330010247281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30815708804144440013663041 23111781603108330010247281)
                ·
                  refine ⟨17333836202331247507685461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23111781603108330010247281 17333836202331247507685461)
                  ·
                    refine ⟨203130892996069306730689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17333836202331247507685461 203130892996069306730689)
                    ·
                      rfl

theorem cell23_1186788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_1186788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186788 prefixEnd_1186788 := by exact prefixLift 1186788
  have htrace : WordTrace (prefixWord ++ tailWord_1186788) baseStart_1186788 baseEnd_1186788 := by
    simpa [prefixWord, tailWord_1186788, baseEnd_1186788] using wordTrace_append hprefix tailTrace_1186788
  have hstable : (prefixWord ++ tailWord_1186788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186788).length < 2 ^ (prefixWord ++ tailWord_1186788).sum := by decide
  have hdescent : baseEnd_1186788 < baseStart_1186788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186808 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1186808 : Nat := 118140960795 + 1186808 * 2 ^ 59
def prefixEnd_1186808 : Nat := 4983230072969 + 3 ^ 40 * 1186808 * 2
def baseEnd_1186808 : Nat := 609402948601297841941975

theorem tailTrace_1186808 : CollatzResearch.WordTrace tailWord_1186808 prefixEnd_1186808 609402948601297841941975 := by
  unfold tailWord_1186808
  simp only [CollatzResearch.WordTrace]
  refine ⟨21643221942202390757240539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28857629256269854342987385 21643221942202390757240539)
  ·
    refine ⟨32464832913303586135860809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21643221942202390757240539 32464832913303586135860809)
    ·
      refine ⟨24348624684977689601895607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32464832913303586135860809 24348624684977689601895607)
      ·
        refine ⟨36522937027466534402843411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24348624684977689601895607 36522937027466534402843411)
        ·
          refine ⟨54784405541199801604265117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36522937027466534402843411 54784405541199801604265117)
          ·
            refine ⟨20544152077949925601599419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54784405541199801604265117 20544152077949925601599419)
            ·
              refine ⟨30816228116924888402399129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20544152077949925601599419 30816228116924888402399129)
              ·
                refine ⟨23112171087693666301799347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30816228116924888402399129 23112171087693666301799347)
                ·
                  refine ⟨34668256631540499452699021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23112171087693666301799347 34668256631540499452699021)
                  ·
                    refine ⟨13000596236827687294762133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34668256631540499452699021 13000596236827687294762133)
                    ·
                      refine ⟨609402948601297841941975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13000596236827687294762133 609402948601297841941975)
                      ·
                        rfl

theorem cell23_1186808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1186808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186808 prefixEnd_1186808 := by exact prefixLift 1186808
  have htrace : WordTrace (prefixWord ++ tailWord_1186808) baseStart_1186808 baseEnd_1186808 := by
    simpa [prefixWord, tailWord_1186808, baseEnd_1186808] using wordTrace_append hprefix tailTrace_1186808
  have hstable : (prefixWord ++ tailWord_1186808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186808).length < 2 ^ (prefixWord ++ tailWord_1186808).sum := by decide
  have hdescent : baseEnd_1186808 < baseStart_1186808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186812 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_1186812 : Nat := 118140960795 + 1186812 * 2 ^ 59
def prefixEnd_1186812 : Nat := 4983230072969 + 3 ^ 40 * 1186812 * 2
def baseEnd_1186812 : Nat := 609405002523915826291957

theorem tailTrace_1186812 : CollatzResearch.WordTrace tailWord_1186812 prefixEnd_1186812 609405002523915826291957 := by
  unfold tailWord_1186812
  simp only [CollatzResearch.WordTrace]
  refine ⟨21643294888195145098813345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28857726517593526798417793 21643294888195145098813345)
  ·
    refine ⟨16232471166146358824110009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21643294888195145098813345 16232471166146358824110009)
    ·
      refine ⟨12174353374609769118082507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16232471166146358824110009 12174353374609769118082507)
      ·
        refine ⟨18261530061914653677123761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12174353374609769118082507 18261530061914653677123761)
        ·
          refine ⟨13696147546435990257842821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18261530061914653677123761 13696147546435990257842821)
          ·
            refine ⟨2568027664956748173345529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13696147546435990257842821 2568027664956748173345529)
            ·
              refine ⟨1926020748717561130009147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568027664956748173345529 1926020748717561130009147)
              ·
                refine ⟨2889031123076341695013721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926020748717561130009147 2889031123076341695013721)
                ·
                  refine ⟨2166773342307256271260291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2889031123076341695013721 2166773342307256271260291)
                  ·
                    refine ⟨3250160013460884406890437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2166773342307256271260291 3250160013460884406890437)
                    ·
                      refine ⟨609405002523915826291957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3250160013460884406890437 609405002523915826291957)
                      ·
                        rfl

theorem cell23_1186812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_1186812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186812 prefixEnd_1186812 := by exact prefixLift 1186812
  have htrace : WordTrace (prefixWord ++ tailWord_1186812) baseStart_1186812 baseEnd_1186812 := by
    simpa [prefixWord, tailWord_1186812, baseEnd_1186812] using wordTrace_append hprefix tailTrace_1186812
  have hstable : (prefixWord ++ tailWord_1186812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186812).length < 2 ^ (prefixWord ++ tailWord_1186812).sum := by decide
  have hdescent : baseEnd_1186812 < baseStart_1186812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186852 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 6]
def baseStart_1186852 : Nat := 118140960795 + 1186852 * 2 ^ 59
def prefixEnd_1186852 : Nat := 4983230072969 + 3 ^ 40 * 1186852 * 2
def baseEnd_1186852 : Nat := 67713949083343963310197

theorem tailTrace_1186852 : CollatzResearch.WordTrace tailWord_1186852 prefixEnd_1186852 67713949083343963310197 := by
  unfold tailWord_1186852
  simp only [CollatzResearch.WordTrace]
  refine ⟨21644024348122688514541405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28858699130830251352721873 21644024348122688514541405)
  ·
    refine ⟨8116509130546008192953027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21644024348122688514541405 8116509130546008192953027)
    ·
      refine ⟨12174763695819012289429541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116509130546008192953027 12174763695819012289429541)
      ·
        refine ⟨2282768192966064804268039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12174763695819012289429541 2282768192966064804268039)
        ·
          refine ⟨3424152289449097206402059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282768192966064804268039 3424152289449097206402059)
          ·
            refine ⟨5136228434173645809603089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424152289449097206402059 5136228434173645809603089)
            ·
              refine ⟨3852171325630234357202317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5136228434173645809603089 3852171325630234357202317)
              ·
                refine ⟨1444564247111337883950869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3852171325630234357202317 1444564247111337883950869)
                ·
                  refine ⟨67713949083343963310197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1444564247111337883950869 67713949083343963310197)
                  ·
                    rfl

theorem cell23_1186852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_1186852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186852 prefixEnd_1186852 := by exact prefixLift 1186852
  have htrace : WordTrace (prefixWord ++ tailWord_1186852) baseStart_1186852 baseEnd_1186852 := by
    simpa [prefixWord, tailWord_1186852, baseEnd_1186852] using wordTrace_append hprefix tailTrace_1186852
  have hstable : (prefixWord ++ tailWord_1186852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186852).length < 2 ^ (prefixWord ++ tailWord_1186852).sum := by decide
  have hdescent : baseEnd_1186852 < baseStart_1186852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186865 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_1186865 : Nat := 118140960795 + 1186865 * 2 ^ 59
def prefixEnd_1186865 : Nat := 4983230072969 + 3 ^ 40 * 1186865 * 2
def baseEnd_1186865 : Nat := 203144072332868039643071

theorem tailTrace_1186865 : CollatzResearch.WordTrace tailWord_1186865 prefixEnd_1186865 203144072332868039643071 := by
  unfold tailWord_1186865
  simp only [CollatzResearch.WordTrace]
  refine ⟨43288522845198280249306049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28859015230132186832870699 43288522845198280249306049)
  ·
    refine ⟨32466392133898710186979537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43288522845198280249306049 32466392133898710186979537)
    ·
      refine ⟨24349794100424032640234653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32466392133898710186979537 24349794100424032640234653)
      ·
        refine ⟨9131172787659012240087995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24349794100424032640234653 9131172787659012240087995)
        ·
          refine ⟨13696759181488518360131993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9131172787659012240087995 13696759181488518360131993)
          ·
            refine ⟨10272569386116388770098995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13696759181488518360131993 10272569386116388770098995)
            ·
              refine ⟨15408854079174583155148493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10272569386116388770098995 15408854079174583155148493)
              ·
                refine ⟨5778320279690468683180685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15408854079174583155148493 5778320279690468683180685)
                ·
                  refine ⟨2166870104883925756192757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5778320279690468683180685 2166870104883925756192757)
                  ·
                    refine ⟨203144072332868039643071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2166870104883925756192757 203144072332868039643071)
                    ·
                      rfl

theorem cell23_1186865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_1186865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186865 prefixEnd_1186865 := by exact prefixLift 1186865
  have htrace : WordTrace (prefixWord ++ tailWord_1186865) baseStart_1186865 baseEnd_1186865 := by
    simpa [prefixWord, tailWord_1186865, baseEnd_1186865] using wordTrace_append hprefix tailTrace_1186865
  have hstable : (prefixWord ++ tailWord_1186865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186865).length < 2 ^ (prefixWord ++ tailWord_1186865).sum := by decide
  have hdescent : baseEnd_1186865 < baseStart_1186865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186886 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1186886 : Nat := 118140960795 + 1186886 * 2 ^ 59
def prefixEnd_1186886 : Nat := 4983230072969 + 3 ^ 40 * 1186886 * 2
def baseEnd_1186886 : Nat := 67715888899149837418513

theorem tailTrace_1186886 : CollatzResearch.WordTrace tailWord_1186886 prefixEnd_1186886 67715888899149837418513 := by
  unfold tailWord_1186886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1352790274316318776119391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28859525852081467223880341 1352790274316318776119391)
  ·
    refine ⟨2029185411474478164179087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1352790274316318776119391 2029185411474478164179087)
    ·
      refine ⟨3043778117211717246268631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029185411474478164179087 3043778117211717246268631)
      ·
        refine ⟨4565667175817575869402947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3043778117211717246268631 4565667175817575869402947)
        ·
          refine ⟨6848500763726363804104421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565667175817575869402947 6848500763726363804104421)
          ·
            refine ⟨1284093893198693213269579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6848500763726363804104421 1284093893198693213269579)
            ·
              refine ⟨1926140839798039819904369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284093893198693213269579 1926140839798039819904369)
              ·
                refine ⟨1444605629848529864928277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926140839798039819904369 1444605629848529864928277)
                ·
                  refine ⟨67715888899149837418513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1444605629848529864928277 67715888899149837418513)
                  ·
                    rfl

theorem cell23_1186886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1186886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186886 prefixEnd_1186886 := by exact prefixLift 1186886
  have htrace : WordTrace (prefixWord ++ tailWord_1186886) baseStart_1186886 baseEnd_1186886 := by
    simpa [prefixWord, tailWord_1186886, baseEnd_1186886] using wordTrace_append hprefix tailTrace_1186886
  have hstable : (prefixWord ++ tailWord_1186886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186886).length < 2 ^ (prefixWord ++ tailWord_1186886).sum := by decide
  have hdescent : baseEnd_1186886 < baseStart_1186886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186905 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_1186905 : Nat := 118140960795 + 1186905 * 2 ^ 59
def prefixEnd_1186905 : Nat := 4983230072969 + 3 ^ 40 * 1186905 * 2
def baseEnd_1186905 : Nat := 609452756224783962429029

theorem tailTrace_1186905 : CollatzResearch.WordTrace tailWord_1186905 prefixEnd_1186905 609452756224783962429029 := by
  unfold tailWord_1186905
  simp only [CollatzResearch.WordTrace]
  refine ⟨43289981765053367080762169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28859987843368911387174779 43289981765053367080762169)
  ·
    refine ⟨32467486323790025310571627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43289981765053367080762169 32467486323790025310571627)
    ·
      refine ⟨48701229485685037965857441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32467486323790025310571627 48701229485685037965857441)
      ·
        refine ⟨36525922114263778474393081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48701229485685037965857441 36525922114263778474393081)
        ·
          refine ⟨27394441585697833855794811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36525922114263778474393081 27394441585697833855794811)
          ·
            refine ⟨41091662378546750783692217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27394441585697833855794811 41091662378546750783692217)
            ·
              refine ⟨30818746783910063087769163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41091662378546750783692217 30818746783910063087769163)
              ·
                refine ⟨46228120175865094631653745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30818746783910063087769163 46228120175865094631653745)
                ·
                  refine ⟨34671090131898820973740309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46228120175865094631653745 34671090131898820973740309)
                  ·
                    refine ⟨1625207349932757233144077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34671090131898820973740309 1625207349932757233144077)
                    ·
                      refine ⟨609452756224783962429029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1625207349932757233144077 609452756224783962429029)
                      ·
                        rfl

theorem cell23_1186905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_1186905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186905 prefixEnd_1186905 := by exact prefixLift 1186905
  have htrace : WordTrace (prefixWord ++ tailWord_1186905) baseStart_1186905 baseEnd_1186905 := by
    simpa [prefixWord, tailWord_1186905, baseEnd_1186905] using wordTrace_append hprefix tailTrace_1186905
  have hstable : (prefixWord ++ tailWord_1186905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186905).length < 2 ^ (prefixWord ++ tailWord_1186905).sum := by decide
  have hdescent : baseEnd_1186905 < baseStart_1186905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186919 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_1186919 : Nat := 118140960795 + 1186919 * 2 ^ 59
def prefixEnd_1186919 : Nat := 4983230072969 + 3 ^ 40 * 1186919 * 2
def baseEnd_1186919 : Nat := 609459944953946907653965

theorem tailTrace_1186919 : CollatzResearch.WordTrace tailWord_1186919 prefixEnd_1186919 609459944953946907653965 := by
  unfold tailWord_1186919
  simp only [CollatzResearch.WordTrace]
  refine ⟨43290492387002647471771811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28860328258001764981181207 43290492387002647471771811)
  ·
    refine ⟨64935738580503971207657717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43290492387002647471771811 64935738580503971207657717)
    ·
      refine ⟨6087725491922247300717911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64935738580503971207657717 6087725491922247300717911)
      ·
        refine ⟨9131588237883370951076867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6087725491922247300717911 9131588237883370951076867)
        ·
          refine ⟨13697382356825056426615301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9131588237883370951076867 13697382356825056426615301)
          ·
            refine ⟨2568259191904698079990369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13697382356825056426615301 2568259191904698079990369)
            ·
              refine ⟨1926194393928523559992777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568259191904698079990369 1926194393928523559992777)
              ·
                refine ⟨1444645795446392669994583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926194393928523559992777 1444645795446392669994583)
                ·
                  refine ⟨2166968693169589004991875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444645795446392669994583 2166968693169589004991875)
                  ·
                    refine ⟨3250453039754383507487813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2166968693169589004991875 3250453039754383507487813)
                    ·
                      refine ⟨609459944953946907653965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3250453039754383507487813 609459944953946907653965)
                      ·
                        rfl

theorem cell23_1186919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_1186919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186919 prefixEnd_1186919 := by exact prefixLift 1186919
  have htrace : WordTrace (prefixWord ++ tailWord_1186919) baseStart_1186919 baseEnd_1186919 := by
    simpa [prefixWord, tailWord_1186919, baseEnd_1186919] using wordTrace_append hprefix tailTrace_1186919
  have hstable : (prefixWord ++ tailWord_1186919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186919).length < 2 ^ (prefixWord ++ tailWord_1186919).sum := by decide
  have hdescent : baseEnd_1186919 < baseStart_1186919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186965 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1186965 : Nat := 118140960795 + 1186965 * 2 ^ 59
def prefixEnd_1186965 : Nat := 4983230072969 + 3 ^ 40 * 1186965 * 2
def baseEnd_1186965 : Nat := 609483565064053727678753

theorem tailTrace_1186965 : CollatzResearch.WordTrace tailWord_1186965 prefixEnd_1186965 609483565064053727678753 := by
  unfold tailWord_1186965
  simp only [CollatzResearch.WordTrace]
  refine ⟨43292170144835997327946349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28861446763223998218630899 43292170144835997327946349)
  ·
    refine ⟨16234563804313498997979881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43292170144835997327946349 16234563804313498997979881)
    ·
      refine ⟨12175922853235124248484911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16234563804313498997979881 12175922853235124248484911)
      ·
        refine ⟨18263884279852686372727367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12175922853235124248484911 18263884279852686372727367)
        ·
          refine ⟨27395826419779029559091051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18263884279852686372727367 27395826419779029559091051)
          ·
            refine ⟨41093739629668544338636577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27395826419779029559091051 41093739629668544338636577)
            ·
              refine ⟨30820304722251408253977433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41093739629668544338636577 30820304722251408253977433)
              ·
                refine ⟨23115228541688556190483075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30820304722251408253977433 23115228541688556190483075)
                ·
                  refine ⟨34672842812532834285724613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23115228541688556190483075 34672842812532834285724613)
                  ·
                    refine ⟨6501158027349906428573365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34672842812532834285724613 6501158027349906428573365)
                    ·
                      refine ⟨609483565064053727678753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6501158027349906428573365 609483565064053727678753)
                      ·
                        rfl

theorem cell23_1186965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1186965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186965 prefixEnd_1186965 := by exact prefixLift 1186965
  have htrace : WordTrace (prefixWord ++ tailWord_1186965) baseStart_1186965 baseEnd_1186965 := by
    simpa [prefixWord, tailWord_1186965, baseEnd_1186965] using wordTrace_append hprefix tailTrace_1186965
  have hstable : (prefixWord ++ tailWord_1186965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186965).length < 2 ^ (prefixWord ++ tailWord_1186965).sum := by decide
  have hdescent : baseEnd_1186965 < baseStart_1186965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186986 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1186986 : Nat := 118140960795 + 1186986 * 2 ^ 59
def prefixEnd_1186986 : Nat := 4983230072969 + 3 ^ 40 * 1186986 * 2
def baseEnd_1186986 : Nat := 609494348157798145516157

theorem tailTrace_1186986 : CollatzResearch.WordTrace tailWord_1186986 prefixEnd_1186986 609494348157798145516157 := by
  unfold tailWord_1186986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823234019439979478615203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28861957385173278609640541 10823234019439979478615203)
  ·
    refine ⟨16234851029159969217922805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10823234019439979478615203 16234851029159969217922805)
    ·
      refine ⟨1522017283983747114180263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16234851029159969217922805 1522017283983747114180263)
      ·
        refine ⟨2283025925975620671270395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522017283983747114180263 2283025925975620671270395)
        ·
          refine ⟨3424538888963431006905593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283025925975620671270395 3424538888963431006905593)
          ·
            refine ⟨2568404166722573255179195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3424538888963431006905593 2568404166722573255179195)
            ·
              refine ⟨3852606250083859882768793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568404166722573255179195 3852606250083859882768793)
              ·
                refine ⟨2889454687562894912076595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852606250083859882768793 2889454687562894912076595)
                ·
                  refine ⟨4334182031344342368114893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889454687562894912076595 4334182031344342368114893)
                  ·
                    refine ⟨1625318261754128388043085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4334182031344342368114893 1625318261754128388043085)
                    ·
                      refine ⟨609494348157798145516157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1625318261754128388043085 609494348157798145516157)
                      ·
                        rfl

theorem cell23_1186986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1186986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1186986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1186986 prefixEnd_1186986 := by exact prefixLift 1186986
  have htrace : WordTrace (prefixWord ++ tailWord_1186986) baseStart_1186986 baseEnd_1186986 := by
    simpa [prefixWord, tailWord_1186986, baseEnd_1186986] using wordTrace_append hprefix tailTrace_1186986
  have hstable : (prefixWord ++ tailWord_1186986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186986).length < 2 ^ (prefixWord ++ tailWord_1186986).sum := by decide
  have hdescent : baseEnd_1186986 < baseStart_1186986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187009 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1187009 : Nat := 118140960795 + 1187009 * 2 ^ 59
def prefixEnd_1187009 : Nat := 4983230072969 + 3 ^ 40 * 1187009 * 2
def baseEnd_1187009 : Nat := 609506158212851555528551

theorem tailTrace_1187009 : CollatzResearch.WordTrace tailWord_1187009 prefixEnd_1187009 609506158212851555528551 := by
  unfold tailWord_1187009
  simp only [CollatzResearch.WordTrace]
  refine ⟨43293774956676592842548081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28862516637784395228365387 43293774956676592842548081)
  ·
    refine ⟨32470331217507444631911061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43293774956676592842548081 32470331217507444631911061)
    ·
      refine ⟨1522046775820661467120831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32470331217507444631911061 1522046775820661467120831)
      ·
        refine ⟨2283070163730992200681247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522046775820661467120831 2283070163730992200681247)
        ·
          refine ⟨3424605245596488301021871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283070163730992200681247 3424605245596488301021871)
          ·
            refine ⟨5136907868394732451532807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424605245596488301021871 5136907868394732451532807)
            ·
              refine ⟨7705361802592098677299211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5136907868394732451532807 7705361802592098677299211)
              ·
                refine ⟨11558042703888148015948817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7705361802592098677299211 11558042703888148015948817)
                ·
                  refine ⟨8668532027916111011961613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11558042703888148015948817 8668532027916111011961613)
                  ·
                    refine ⟨3250699510468541629485605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8668532027916111011961613 3250699510468541629485605)
                    ·
                      refine ⟨609506158212851555528551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3250699510468541629485605 609506158212851555528551)
                      ·
                        rfl

theorem cell23_1187009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1187009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187009 prefixEnd_1187009 := by exact prefixLift 1187009
  have htrace : WordTrace (prefixWord ++ tailWord_1187009) baseStart_1187009 baseEnd_1187009 := by
    simpa [prefixWord, tailWord_1187009, baseEnd_1187009] using wordTrace_append hprefix tailTrace_1187009
  have hstable : (prefixWord ++ tailWord_1187009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187009).length < 2 ^ (prefixWord ++ tailWord_1187009).sum := by decide
  have hdescent : baseEnd_1187009 < baseStart_1187009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187015 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 11]
def baseStart_1187015 : Nat := 118140960795 + 1187015 * 2 ^ 59
def prefixEnd_1187015 : Nat := 4983230072969 + 3 ^ 40 * 1187015 * 2
def baseEnd_1187015 : Nat := 67723248788530948005947

theorem tailTrace_1187015 : CollatzResearch.WordTrace tailWord_1187015 prefixEnd_1187015 67723248788530948005947 := by
  unfold tailWord_1187015
  simp only [CollatzResearch.WordTrace]
  refine ⟨43293993794654855867266499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28862662529769903911510999 43293993794654855867266499)
  ·
    refine ⟨64940990691982283800899749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43293993794654855867266499 64940990691982283800899749)
    ·
      refine ⟨12176435754746678212668703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64940990691982283800899749 12176435754746678212668703)
      ·
        refine ⟨18264653632120017319003055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12176435754746678212668703 18264653632120017319003055)
        ·
          refine ⟨27396980448180025978504583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18264653632120017319003055 27396980448180025978504583)
          ·
            refine ⟨41095470672270038967756875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27396980448180025978504583 41095470672270038967756875)
            ·
              refine ⟨61643206008405058451635313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41095470672270038967756875 61643206008405058451635313)
              ·
                refine ⟨46232404506303793838726485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61643206008405058451635313 46232404506303793838726485)
                ·
                  refine ⟨67723248788530948005947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 46232404506303793838726485 67723248788530948005947)
                  ·
                    rfl

theorem cell23_1187015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 11].length) (baseStart_1187015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187015 prefixEnd_1187015 := by exact prefixLift 1187015
  have htrace : WordTrace (prefixWord ++ tailWord_1187015) baseStart_1187015 baseEnd_1187015 := by
    simpa [prefixWord, tailWord_1187015, baseEnd_1187015] using wordTrace_append hprefix tailTrace_1187015
  have hstable : (prefixWord ++ tailWord_1187015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187015).length < 2 ^ (prefixWord ++ tailWord_1187015).sum := by decide
  have hdescent : baseEnd_1187015 < baseStart_1187015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187026 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1187026 : Nat := 118140960795 + 1187026 * 2 ^ 59
def prefixEnd_1187026 : Nat := 4983230072969 + 3 ^ 40 * 1187026 * 2
def baseEnd_1187026 : Nat := 609514887383977989015973

theorem tailTrace_1187026 : CollatzResearch.WordTrace tailWord_1187026 prefixEnd_1187026 609514887383977989015973 := by
  unfold tailWord_1187026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10823598749403751186479233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28862929998410003163944621 10823598749403751186479233)
  ·
    refine ⟨8117699062052813389859425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10823598749403751186479233 8117699062052813389859425)
    ·
      refine ⟨6088274296539610042394569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8117699062052813389859425 6088274296539610042394569)
      ·
        refine ⟨4566205722404707531795927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6088274296539610042394569 4566205722404707531795927)
        ·
          refine ⟨6849308583607061297693891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566205722404707531795927 6849308583607061297693891)
          ·
            refine ⟨10273962875410591946540837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6849308583607061297693891 10273962875410591946540837)
            ·
              refine ⟨1926368039139485989976407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10273962875410591946540837 1926368039139485989976407)
              ·
                refine ⟨2889552058709228984964611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926368039139485989976407 2889552058709228984964611)
                ·
                  refine ⟨4334328088063843477446917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2889552058709228984964611 4334328088063843477446917)
                  ·
                    refine ⟨812686516511970652021297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4334328088063843477446917 812686516511970652021297)
                    ·
                      refine ⟨609514887383977989015973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812686516511970652021297 609514887383977989015973)
                      ·
                        rfl

theorem cell23_1187026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1187026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187026 prefixEnd_1187026 := by exact prefixLift 1187026
  have htrace : WordTrace (prefixWord ++ tailWord_1187026) baseStart_1187026 baseEnd_1187026 := by
    simpa [prefixWord, tailWord_1187026, baseEnd_1187026] using wordTrace_append hprefix tailTrace_1187026
  have hstable : (prefixWord ++ tailWord_1187026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187026).length < 2 ^ (prefixWord ++ tailWord_1187026).sum := by decide
  have hdescent : baseEnd_1187026 < baseStart_1187026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187035 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_1187035 : Nat := 118140960795 + 1187035 * 2 ^ 59
def prefixEnd_1187035 : Nat := 4983230072969 + 3 ^ 40 * 1187035 * 2
def baseEnd_1187035 : Nat := 609519508709868453803431

theorem tailTrace_1187035 : CollatzResearch.WordTrace tailWord_1187035 prefixEnd_1187035 609519508709868453803431 := by
  unfold tailWord_1187035
  simp only [CollatzResearch.WordTrace]
  refine ⟨43294723254582399282994559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28863148836388266188663039 43294723254582399282994559)
  ·
    refine ⟨64942084881873598924491839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43294723254582399282994559 64942084881873598924491839)
    ·
      refine ⟨97413127322810398386737759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64942084881873598924491839 97413127322810398386737759)
      ·
        refine ⟨146119690984215597580106639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97413127322810398386737759 146119690984215597580106639)
        ·
          refine ⟨219179536476323396370159959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146119690984215597580106639 219179536476323396370159959)
          ·
            refine ⟨328769304714485094555239939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219179536476323396370159959 328769304714485094555239939)
            ·
              refine ⟨493153957071727641832859909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328769304714485094555239939 493153957071727641832859909)
              ·
                refine ⟨92466366950948932843661233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493153957071727641832859909 92466366950948932843661233)
                ·
                  refine ⟨69349775213211699632745925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92466366950948932843661233 69349775213211699632745925)
                  ·
                    refine ⟨13003082852477193681139861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69349775213211699632745925 13003082852477193681139861)
                    ·
                      refine ⟨609519508709868453803431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13003082852477193681139861 609519508709868453803431)
                      ·
                        rfl

theorem cell23_1187035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_1187035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187035 prefixEnd_1187035 := by exact prefixLift 1187035
  have htrace : WordTrace (prefixWord ++ tailWord_1187035) baseStart_1187035 baseEnd_1187035 := by
    simpa [prefixWord, tailWord_1187035, baseEnd_1187035] using wordTrace_append hprefix tailTrace_1187035
  have hstable : (prefixWord ++ tailWord_1187035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187035).length < 2 ^ (prefixWord ++ tailWord_1187035).sum := by decide
  have hdescent : baseEnd_1187035 < baseStart_1187035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187047 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1187047 : Nat := 118140960795 + 1187047 * 2 ^ 59
def prefixEnd_1187047 : Nat := 4983230072969 + 3 ^ 40 * 1187047 * 2
def baseEnd_1187047 : Nat := 609525670477722406853377

theorem tailTrace_1187047 : CollatzResearch.WordTrace tailWord_1187047 prefixEnd_1187047 609525670477722406853377 := by
  unfold tailWord_1187047
  simp only [CollatzResearch.WordTrace]
  refine ⟨43295160930538925332431395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28863440620359283554954263 43295160930538925332431395)
  ·
    refine ⟨64942741395808387998647093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43295160930538925332431395 64942741395808387998647093)
    ·
      refine ⟨6088382005857036374873165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64942741395808387998647093 6088382005857036374873165)
      ·
        refine ⟨2283143252196388640577437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6088382005857036374873165 2283143252196388640577437)
        ·
          refine ⟨856178719573645740216539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2283143252196388640577437 856178719573645740216539)
          ·
            refine ⟨1284268079360468610324809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856178719573645740216539 1284268079360468610324809)
            ·
              refine ⟨963201059520351457743607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284268079360468610324809 963201059520351457743607)
              ·
                refine ⟨1444801589280527186615411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963201059520351457743607 1444801589280527186615411)
                ·
                  refine ⟨2167202383920790779923117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444801589280527186615411 2167202383920790779923117)
                  ·
                    refine ⟨812700893970296542471169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2167202383920790779923117 812700893970296542471169)
                    ·
                      refine ⟨609525670477722406853377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812700893970296542471169 609525670477722406853377)
                      ·
                        rfl

theorem cell23_1187047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1187047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187047 prefixEnd_1187047 := by exact prefixLift 1187047
  have htrace : WordTrace (prefixWord ++ tailWord_1187047) baseStart_1187047 baseEnd_1187047 := by
    simpa [prefixWord, tailWord_1187047, baseEnd_1187047] using wordTrace_append hprefix tailTrace_1187047
  have hstable : (prefixWord ++ tailWord_1187047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187047).length < 2 ^ (prefixWord ++ tailWord_1187047).sum := by decide
  have hdescent : baseEnd_1187047 < baseStart_1187047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187169 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1187169 : Nat := 118140960795 + 1187169 * 2 ^ 59
def prefixEnd_1187169 : Nat := 4983230072969 + 3 ^ 40 * 1187169 * 2
def baseEnd_1187169 : Nat := 203196105039190309842605

theorem tailTrace_1187169 : CollatzResearch.WordTrace tailWord_1187169 prefixEnd_1187169 203196105039190309842605 := by
  unfold tailWord_1187169
  simp only [CollatzResearch.WordTrace]
  refine ⟨43299610636096940168372561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28866407090731293445581707 43299610636096940168372561)
  ·
    refine ⟨32474707977072705126279421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43299610636096940168372561 32474707977072705126279421)
    ·
      refine ⟨12178015491402264422354783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32474707977072705126279421 12178015491402264422354783)
      ·
        refine ⟨18267023237103396633532175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12178015491402264422354783 18267023237103396633532175)
        ·
          refine ⟨27400534855655094950298263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18267023237103396633532175 27400534855655094950298263)
          ·
            refine ⟨41100802283482642425447395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27400534855655094950298263 41100802283482642425447395)
            ·
              refine ⟨61651203425223963638171093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41100802283482642425447395 61651203425223963638171093)
              ·
                refine ⟨1444950080278686647769635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61651203425223963638171093 1444950080278686647769635)
                ·
                  refine ⟨2167425120418029971654453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444950080278686647769635 2167425120418029971654453)
                  ·
                    refine ⟨203196105039190309842605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2167425120418029971654453 203196105039190309842605)
                    ·
                      rfl

theorem cell23_1187169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1187169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187169 prefixEnd_1187169 := by exact prefixLift 1187169
  have htrace : WordTrace (prefixWord ++ tailWord_1187169) baseStart_1187169 baseEnd_1187169 := by
    simpa [prefixWord, tailWord_1187169, baseEnd_1187169] using wordTrace_append hprefix tailTrace_1187169
  have hstable : (prefixWord ++ tailWord_1187169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187169).length < 2 ^ (prefixWord ++ tailWord_1187169).sum := by decide
  have hdescent : baseEnd_1187169 < baseStart_1187169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187183 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 1, 1, 3]
def baseStart_1187183 : Nat := 118140960795 + 1187183 * 2 ^ 59
def prefixEnd_1187183 : Nat := 4983230072969 + 3 ^ 40 * 1187183 * 2
def baseEnd_1187183 : Nat := 609595503846733874752751

theorem tailTrace_1187183 : CollatzResearch.WordTrace tailWord_1187183 prefixEnd_1187183 609595503846733874752751 := by
  unfold tailWord_1187183
  simp only [CollatzResearch.WordTrace]
  refine ⟨43300121258046220559382203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28866747505364147039588135 43300121258046220559382203)
  ·
    refine ⟨64950181887069330839073305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43300121258046220559382203 64950181887069330839073305)
    ·
      refine ⟨48712636415301998129304979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64950181887069330839073305 48712636415301998129304979)
      ·
        refine ⟨73068954622952997193957469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48712636415301998129304979 73068954622952997193957469)
        ·
          refine ⟨27400857983607373947734051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73068954622952997193957469 27400857983607373947734051)
          ·
            refine ⟨41101286975411060921601077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27400857983607373947734051 41101286975411060921601077)
            ·
              refine ⟨3853245653944786961400101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41101286975411060921601077 3853245653944786961400101)
              ·
                refine ⟨722483560114647555262519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3853245653944786961400101 722483560114647555262519)
                ·
                  refine ⟨1083725340171971332893779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722483560114647555262519 1083725340171971332893779)
                  ·
                    refine ⟨1625588010257956999340669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1083725340171971332893779 1625588010257956999340669)
                    ·
                      refine ⟨609595503846733874752751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1625588010257956999340669 609595503846733874752751)
                      ·
                        rfl

theorem cell23_1187183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 1, 3].length) (baseStart_1187183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187183 prefixEnd_1187183 := by exact prefixLift 1187183
  have htrace : WordTrace (prefixWord ++ tailWord_1187183) baseStart_1187183 baseEnd_1187183 := by
    simpa [prefixWord, tailWord_1187183, baseEnd_1187183] using wordTrace_append hprefix tailTrace_1187183
  have hstable : (prefixWord ++ tailWord_1187183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187183).length < 2 ^ (prefixWord ++ tailWord_1187183).sum := by decide
  have hdescent : baseEnd_1187183 < baseStart_1187183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187220 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1187220 : Nat := 118140960795 + 1187220 * 2 ^ 59
def prefixEnd_1187220 : Nat := 4983230072969 + 3 ^ 40 * 1187220 * 2
def baseEnd_1187220 : Nat := 203204834210316743330027

theorem tailTrace_1187220 : CollatzResearch.WordTrace tailWord_1187220 prefixEnd_1187220 203204834210316743330027 := by
  unfold tailWord_1187220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650735379456087939239557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28867647172608117252319409 21650735379456087939239557)
  ·
    refine ⟨4059512883648016488607417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21650735379456087939239557 4059512883648016488607417)
    ·
      refine ⟨3044634662736012366455563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4059512883648016488607417 3044634662736012366455563)
      ·
        refine ⟨4566951994104018549683345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044634662736012366455563 4566951994104018549683345)
        ·
          refine ⟨3425213995578013912262509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4566951994104018549683345 3425213995578013912262509)
          ·
            refine ⟨1284455248341755217098441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3425213995578013912262509 1284455248341755217098441)
            ·
              refine ⟨963341436256316412823831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284455248341755217098441 963341436256316412823831)
              ·
                refine ⟨1445012154384474619235747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963341436256316412823831 1445012154384474619235747)
                ·
                  refine ⟨2167518231576711928853621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445012154384474619235747 2167518231576711928853621)
                  ·
                    refine ⟨203204834210316743330027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2167518231576711928853621 203204834210316743330027)
                    ·
                      rfl

theorem cell23_1187220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1187220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187220 prefixEnd_1187220 := by exact prefixLift 1187220
  have htrace : WordTrace (prefixWord ++ tailWord_1187220) baseStart_1187220 baseEnd_1187220 := by
    simpa [prefixWord, tailWord_1187220, baseEnd_1187220] using wordTrace_append hprefix tailTrace_1187220
  have hstable : (prefixWord ++ tailWord_1187220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187220).length < 2 ^ (prefixWord ++ tailWord_1187220).sum := by decide
  have hdescent : baseEnd_1187220 < baseStart_1187220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187229 : List Nat := [1, 4, 2, 1, 3, 2, 10]
def baseStart_1187229 : Nat := 118140960795 + 1187229 * 2 ^ 59
def prefixEnd_1187229 : Nat := 4983230072969 + 3 ^ 40 * 1187229 * 2
def baseEnd_1187229 : Nat := 7526162024158527096019

theorem tailTrace_1187229 : CollatzResearch.WordTrace tailWord_1187229 prefixEnd_1187229 7526162024158527096019 := by
  unfold tailWord_1187229
  simp only [CollatzResearch.WordTrace]
  refine ⟨43301799015879570415556741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28867866010586380277037827 43301799015879570415556741)
  ·
    refine ⟨8119087315477419452916889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43301799015879570415556741 8119087315477419452916889)
    ·
      refine ⟨6089315486608064589687667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8119087315477419452916889 6089315486608064589687667)
      ·
        refine ⟨9133973229912096884531501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6089315486608064589687667 9133973229912096884531501)
        ·
          refine ⟨3425239961217036331699313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9133973229912096884531501 3425239961217036331699313)
          ·
            refine ⟨2568929970912777248774485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3425239961217036331699313 2568929970912777248774485)
            ·
              refine ⟨7526162024158527096019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2568929970912777248774485 7526162024158527096019)
              ·
                rfl

theorem cell23_1187229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 10].length) (baseStart_1187229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187229 prefixEnd_1187229 := by exact prefixLift 1187229
  have htrace : WordTrace (prefixWord ++ tailWord_1187229) baseStart_1187229 baseEnd_1187229 := by
    simpa [prefixWord, tailWord_1187229, baseEnd_1187229] using wordTrace_append hprefix tailTrace_1187229
  have hstable : (prefixWord ++ tailWord_1187229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187229).length < 2 ^ (prefixWord ++ tailWord_1187229).sum := by decide
  have hdescent : baseEnd_1187229 < baseStart_1187229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187253 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1187253 : Nat := 118140960795 + 1187253 * 2 ^ 59
def prefixEnd_1187253 : Nat := 4983230072969 + 3 ^ 40 * 1187253 * 2
def baseEnd_1187253 : Nat := 609631447492548600877429

theorem tailTrace_1187253 : CollatzResearch.WordTrace tailWord_1187253 prefixEnd_1187253 609631447492548600877429 := by
  unfold tailWord_1187253
  simp only [CollatzResearch.WordTrace]
  refine ⟨43302674367792622514430413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28868449578528415009620275 43302674367792622514430413)
  ·
    refine ⟨16238502887922233442911405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43302674367792622514430413 16238502887922233442911405)
    ·
      refine ⟨6089438582970837541091777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16238502887922233442911405 6089438582970837541091777)
      ·
        refine ⟨4567078937228128155818833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089438582970837541091777 4567078937228128155818833)
        ·
          refine ⟨3425309202921096116864125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567078937228128155818833 3425309202921096116864125)
          ·
            refine ⟨1284490951095411043824047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3425309202921096116864125 1284490951095411043824047)
            ·
              refine ⟨1926736426643116565736071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284490951095411043824047 1926736426643116565736071)
              ·
                refine ⟨2890104639964674848604107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926736426643116565736071 2890104639964674848604107)
                ·
                  refine ⟨4335156959947012272906161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890104639964674848604107 4335156959947012272906161)
                  ·
                    refine ⟨3251367719960259204679621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4335156959947012272906161 3251367719960259204679621)
                    ·
                      refine ⟨609631447492548600877429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3251367719960259204679621 609631447492548600877429)
                      ·
                        rfl

theorem cell23_1187253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1187253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187253 prefixEnd_1187253 := by exact prefixLift 1187253
  have htrace : WordTrace (prefixWord ++ tailWord_1187253) baseStart_1187253 baseEnd_1187253 := by
    simpa [prefixWord, tailWord_1187253, baseEnd_1187253] using wordTrace_append hprefix tailTrace_1187253
  have hstable : (prefixWord ++ tailWord_1187253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187253).length < 2 ^ (prefixWord ++ tailWord_1187253).sum := by decide
  have hdescent : baseEnd_1187253 < baseStart_1187253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187256 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_1187256 : Nat := 118140960795 + 1187256 * 2 ^ 59
def prefixEnd_1187256 : Nat := 4983230072969 + 3 ^ 40 * 1187256 * 2
def baseEnd_1187256 : Nat := 609632987934512089139915

theorem tailTrace_1187256 : CollatzResearch.WordTrace tailWord_1187256 prefixEnd_1187256 609632987934512089139915 := by
  unfold tailWord_1187256
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651391893390877013394811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28868522524521169351193081 21651391893390877013394811)
  ·
    refine ⟨32477087840086315520092217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21651391893390877013394811 32477087840086315520092217)
    ·
      refine ⟨24357815880064736640069163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32477087840086315520092217 24357815880064736640069163)
      ·
        refine ⟨36536723820097104960103745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24357815880064736640069163 36536723820097104960103745)
        ·
          refine ⟨27402542865072828720077809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36536723820097104960103745 27402542865072828720077809)
          ·
            refine ⟨20551907148804621540058357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27402542865072828720077809 20551907148804621540058357)
            ·
              refine ⟨1926741295200433269380471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20551907148804621540058357 1926741295200433269380471)
              ·
                refine ⟨2890111942800649904070707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926741295200433269380471 2890111942800649904070707)
                ·
                  refine ⟨4335167914200974856106061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890111942800649904070707 4335167914200974856106061)
                  ·
                    refine ⟨1625687967825365571039773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4335167914200974856106061 1625687967825365571039773)
                    ·
                      refine ⟨609632987934512089139915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1625687967825365571039773 609632987934512089139915)
                      ·
                        rfl

theorem cell23_1187256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_1187256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187256 prefixEnd_1187256 := by exact prefixLift 1187256
  have htrace : WordTrace (prefixWord ++ tailWord_1187256) baseStart_1187256 baseEnd_1187256 := by
    simpa [prefixWord, tailWord_1187256, baseEnd_1187256] using wordTrace_append hprefix tailTrace_1187256
  have hstable : (prefixWord ++ tailWord_1187256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187256).length < 2 ^ (prefixWord ++ tailWord_1187256).sum := by decide
  have hdescent : baseEnd_1187256 < baseStart_1187256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187260 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1187260 : Nat := 118140960795 + 1187260 * 2 ^ 59
def prefixEnd_1187260 : Nat := 4983230072969 + 3 ^ 40 * 1187260 * 2
def baseEnd_1187260 : Nat := 609635041857130073489897

theorem tailTrace_1187260 : CollatzResearch.WordTrace tailWord_1187260 prefixEnd_1187260 609635041857130073489897 := by
  unfold tailWord_1187260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651464839383631354967617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28868619785844841806623489 21651464839383631354967617)
  ·
    refine ⟨16238598629537723516225713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21651464839383631354967617 16238598629537723516225713)
    ·
      refine ⟨12178948972153292637169285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16238598629537723516225713 12178948972153292637169285)
      ·
        refine ⟨2283552932278742369469241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12178948972153292637169285 2283552932278742369469241)
        ·
          refine ⟨1712664699209056777101931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283552932278742369469241 1712664699209056777101931)
          ·
            refine ⟨2568997048813585165652897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712664699209056777101931 2568997048813585165652897)
            ·
              refine ⟨1926747786610188874239673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568997048813585165652897 1926747786610188874239673)
              ·
                refine ⟨1445060839957641655679755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926747786610188874239673 1445060839957641655679755)
                ·
                  refine ⟨2167591259936462483519633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445060839957641655679755 2167591259936462483519633)
                  ·
                    refine ⟨1625693444952346862639725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2167591259936462483519633 1625693444952346862639725)
                    ·
                      refine ⟨609635041857130073489897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1625693444952346862639725 609635041857130073489897)
                      ·
                        rfl

theorem cell23_1187260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1187260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187260 prefixEnd_1187260 := by exact prefixLift 1187260
  have htrace : WordTrace (prefixWord ++ tailWord_1187260) baseStart_1187260 baseEnd_1187260 := by
    simpa [prefixWord, tailWord_1187260, baseEnd_1187260] using wordTrace_append hprefix tailTrace_1187260
  have hstable : (prefixWord ++ tailWord_1187260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187260).length < 2 ^ (prefixWord ++ tailWord_1187260).sum := by decide
  have hdescent : baseEnd_1187260 < baseStart_1187260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187296 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 5, 4, 2]
def baseStart_1187296 : Nat := 118140960795 + 1187296 * 2 ^ 59
def prefixEnd_1187296 : Nat := 4983230072969 + 3 ^ 40 * 1187296 * 2
def baseEnd_1187296 : Nat := 609653527160691932639731

theorem tailTrace_1187296 : CollatzResearch.WordTrace tailWord_1187296 prefixEnd_1187296 609653527160691932639731 := by
  unfold tailWord_1187296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21652121353318420429122871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28869495137757893905497161 21652121353318420429122871)
  ·
    refine ⟨32478182029977630643684307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21652121353318420429122871 32478182029977630643684307)
    ·
      refine ⟨48717273044966445965526461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32478182029977630643684307 48717273044966445965526461)
      ·
        refine ⟨18268977391862417237072423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48717273044966445965526461 18268977391862417237072423)
        ·
          refine ⟨27403466087793625855608635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18268977391862417237072423 27403466087793625855608635)
          ·
            refine ⟨41105199131690438783412953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27403466087793625855608635 41105199131690438783412953)
            ·
              refine ⟨30828899348767829087559715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41105199131690438783412953 30828899348767829087559715)
              ·
                refine ⟨46243349023151743631339573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30828899348767829087559715 46243349023151743631339573)
                ·
                  refine ⟨4335313970920475965438085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46243349023151743631339573 4335313970920475965438085)
                  ·
                    refine ⟨812871369547589243519641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335313970920475965438085 812871369547589243519641)
                    ·
                      refine ⟨609653527160691932639731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812871369547589243519641 609653527160691932639731)
                      ·
                        rfl

theorem cell23_1187296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_1187296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187296 prefixEnd_1187296 := by exact prefixLift 1187296
  have htrace : WordTrace (prefixWord ++ tailWord_1187296) baseStart_1187296 baseEnd_1187296 := by
    simpa [prefixWord, tailWord_1187296, baseEnd_1187296] using wordTrace_append hprefix tailTrace_1187296
  have hstable : (prefixWord ++ tailWord_1187296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187296).length < 2 ^ (prefixWord ++ tailWord_1187296).sum := by decide
  have hdescent : baseEnd_1187296 < baseStart_1187296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187317 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1187317 : Nat := 118140960795 + 1187317 * 2 ^ 59
def prefixEnd_1187317 : Nat := 4983230072969 + 3 ^ 40 * 1187317 * 2
def baseEnd_1187317 : Nat := 609664310254436350477135

theorem tailTrace_1187317 : CollatzResearch.WordTrace tailWord_1187317 prefixEnd_1187317 609664310254436350477135 := by
  unfold tailWord_1187317
  simp only [CollatzResearch.WordTrace]
  refine ⟨43305008639560761444760205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28870005759707174296506803 43305008639560761444760205)
  ·
    refine ⟨16239378239835285541785077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43305008639560761444760205 16239378239835285541785077)
    ·
      refine ⟨1522441709984558019542351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16239378239835285541785077 1522441709984558019542351)
      ·
        refine ⟨2283662564976837029313527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522441709984558019542351 2283662564976837029313527)
        ·
          refine ⟨3425493847465255543970291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283662564976837029313527 3425493847465255543970291)
          ·
            refine ⟨5138240771197883315955437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425493847465255543970291 5138240771197883315955437)
            ·
              refine ⟨1926840289199206243483289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5138240771197883315955437 1926840289199206243483289)
              ·
                refine ⟨1445130216899404682612467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926840289199206243483289 1445130216899404682612467)
                ·
                  refine ⟨2167695325349107023918701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445130216899404682612467 2167695325349107023918701)
                  ·
                    refine ⟨812885747005915133969513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2167695325349107023918701 812885747005915133969513)
                    ·
                      refine ⟨609664310254436350477135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812885747005915133969513 609664310254436350477135)
                      ·
                        rfl

theorem cell23_1187317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1187317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187317 prefixEnd_1187317 := by exact prefixLift 1187317
  have htrace : WordTrace (prefixWord ++ tailWord_1187317) baseStart_1187317 baseEnd_1187317 := by
    simpa [prefixWord, tailWord_1187317, baseEnd_1187317] using wordTrace_append hprefix tailTrace_1187317
  have hstable : (prefixWord ++ tailWord_1187317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187317).length < 2 ^ (prefixWord ++ tailWord_1187317).sum := by decide
  have hdescent : baseEnd_1187317 < baseStart_1187317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187330 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1187330 : Nat := 118140960795 + 1187330 * 2 ^ 59
def prefixEnd_1187330 : Nat := 4983230072969 + 3 ^ 40 * 1187330 * 2
def baseEnd_1187330 : Nat := 609670985502944799614575

theorem tailTrace_1187330 : CollatzResearch.WordTrace tailWord_1187330 prefixEnd_1187330 609670985502944799614575 := by
  unfold tailWord_1187330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826370697128416166245861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28870321859009109776655629 10826370697128416166245861)
  ·
    refine ⟨2029944505711578031171099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10826370697128416166245861 2029944505711578031171099)
    ·
      refine ⟨3044916758567367046756649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029944505711578031171099 3044916758567367046756649)
      ·
        refine ⟨2283687568925525285067487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044916758567367046756649 2283687568925525285067487)
        ·
          refine ⟨3425531353388287927601231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283687568925525285067487 3425531353388287927601231)
          ·
            refine ⟨5138297030082431891401847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425531353388287927601231 5138297030082431891401847)
            ·
              refine ⟨7707445545123647837102771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138297030082431891401847 7707445545123647837102771)
              ·
                refine ⟨11561168317685471755654157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7707445545123647837102771 11561168317685471755654157)
                ·
                  refine ⟨4335438119132051908370309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11561168317685471755654157 4335438119132051908370309)
                  ·
                    refine ⟨812894647337259732819433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335438119132051908370309 812894647337259732819433)
                    ·
                      refine ⟨609670985502944799614575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812894647337259732819433 609670985502944799614575)
                      ·
                        rfl

theorem cell23_1187330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1187330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187330 prefixEnd_1187330 := by exact prefixLift 1187330
  have htrace : WordTrace (prefixWord ++ tailWord_1187330) baseStart_1187330 baseEnd_1187330 := by
    simpa [prefixWord, tailWord_1187330, baseEnd_1187330] using wordTrace_append hprefix tailTrace_1187330
  have hstable : (prefixWord ++ tailWord_1187330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187330).length < 2 ^ (prefixWord ++ tailWord_1187330).sum := by decide
  have hdescent : baseEnd_1187330 < baseStart_1187330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187363 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 3]
def baseStart_1187363 : Nat := 118140960795 + 1187363 * 2 ^ 59
def prefixEnd_1187363 : Nat := 4983230072969 + 3 ^ 40 * 1187363 * 2
def baseEnd_1187363 : Nat := 609687930364543170501923

theorem tailTrace_1187363 : CollatzResearch.WordTrace tailWord_1187363 prefixEnd_1187363 609687930364543170501923 := by
  unfold tailWord_1187363
  simp only [CollatzResearch.WordTrace]
  refine ⟨43306686397394111300934743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28871124264929407533956495 43306686397394111300934743)
  ·
    refine ⟨64960029596091166951402115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43306686397394111300934743 64960029596091166951402115)
    ·
      refine ⟨97440044394136750427103173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64960029596091166951402115 97440044394136750427103173)
      ·
        refine ⟨18270008323900640705081845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97440044394136750427103173 18270008323900640705081845)
        ·
          refine ⟨1712813280365685066101423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18270008323900640705081845 1712813280365685066101423)
          ·
            refine ⟨2569219920548527599152135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712813280365685066101423 2569219920548527599152135)
            ·
              refine ⟨3853829880822791398728203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569219920548527599152135 3853829880822791398728203)
              ·
                refine ⟨5780744821234187098092305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853829880822791398728203 5780744821234187098092305)
                ·
                  refine ⟨4335558615925640323569229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5780744821234187098092305 4335558615925640323569229)
                  ·
                    refine ⟨1625834480972115121338461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4335558615925640323569229 1625834480972115121338461)
                    ·
                      refine ⟨609687930364543170501923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1625834480972115121338461 609687930364543170501923)
                      ·
                        rfl

theorem cell23_1187363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_1187363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187363 prefixEnd_1187363 := by exact prefixLift 1187363
  have htrace : WordTrace (prefixWord ++ tailWord_1187363) baseStart_1187363 baseEnd_1187363 := by
    simpa [prefixWord, tailWord_1187363, baseEnd_1187363] using wordTrace_append hprefix tailTrace_1187363
  have hstable : (prefixWord ++ tailWord_1187363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187363).length < 2 ^ (prefixWord ++ tailWord_1187363).sum := by decide
  have hdescent : baseEnd_1187363 < baseStart_1187363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187383 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 2, 5]
def baseStart_1187383 : Nat := 118140960795 + 1187383 * 2 ^ 59
def prefixEnd_1187383 : Nat := 4983230072969 + 3 ^ 40 * 1187383 * 2
def baseEnd_1187383 : Nat := 203232733325877697417277

theorem tailTrace_1187383 : CollatzResearch.WordTrace tailWord_1187383 prefixEnd_1187383 203232733325877697417277 := by
  unfold tailWord_1187383
  simp only [CollatzResearch.WordTrace]
  refine ⟨43307415857321654716662803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28871610571547769811108535 43307415857321654716662803)
  ·
    refine ⟨64961123785982482074994205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43307415857321654716662803 64961123785982482074994205)
    ·
      refine ⟨24360421419743430778122827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64961123785982482074994205 24360421419743430778122827)
      ·
        refine ⟨36540632129615146167184241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24360421419743430778122827 36540632129615146167184241)
        ·
          refine ⟨27405474097211359625388181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36540632129615146167184241 27405474097211359625388181)
          ·
            refine ⟨1284631598306782482440071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27405474097211359625388181 1284631598306782482440071)
            ·
              refine ⟨1926947397460173723660107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284631598306782482440071 1926947397460173723660107)
              ·
                refine ⟨2890421096190260585490161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926947397460173723660107 2890421096190260585490161)
                ·
                  refine ⟨2167815822142695439117621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2890421096190260585490161 2167815822142695439117621)
                  ·
                    refine ⟨203232733325877697417277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2167815822142695439117621 203232733325877697417277)
                    ·
                      rfl

theorem cell23_1187383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_1187383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187383 prefixEnd_1187383 := by exact prefixLift 1187383
  have htrace : WordTrace (prefixWord ++ tailWord_1187383) baseStart_1187383 baseEnd_1187383 := by
    simpa [prefixWord, tailWord_1187383, baseEnd_1187383] using wordTrace_append hprefix tailTrace_1187383
  have hstable : (prefixWord ++ tailWord_1187383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187383).length < 2 ^ (prefixWord ++ tailWord_1187383).sum := by decide
  have hdescent : baseEnd_1187383 < baseStart_1187383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187386 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1187386 : Nat := 118140960795 + 1187386 * 2 ^ 59
def prefixEnd_1187386 : Nat := 4983230072969 + 3 ^ 40 * 1187386 * 2
def baseEnd_1187386 : Nat := 609699740419596580514317

theorem tailTrace_1187386 : CollatzResearch.WordTrace tailWord_1187386 prefixEnd_1187386 609699740419596580514317 := by
  unfold tailWord_1187386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10826881319077696557255503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28871683517540524152681341 10826881319077696557255503)
  ·
    refine ⟨16240321978616544835883255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10826881319077696557255503 16240321978616544835883255)
    ·
      refine ⟨24360482967924817253824883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16240321978616544835883255 24360482967924817253824883)
      ·
        refine ⟨36540724451887225880737325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24360482967924817253824883 36540724451887225880737325)
        ·
          refine ⟨13702771669457709705276497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36540724451887225880737325 13702771669457709705276497)
          ·
            refine ⟨10277078752093282278957373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13702771669457709705276497 10277078752093282278957373)
            ·
              refine ⟨3853904532034980854609015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10277078752093282278957373 3853904532034980854609015)
              ·
                refine ⟨5780856798052471281913523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3853904532034980854609015 5780856798052471281913523)
                ·
                  refine ⟨8671285197078706922870285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5780856798052471281913523 8671285197078706922870285)
                  ·
                    refine ⟨3251731948904515096076357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8671285197078706922870285 3251731948904515096076357)
                    ·
                      refine ⟨609699740419596580514317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3251731948904515096076357 609699740419596580514317)
                      ·
                        rfl

theorem cell23_1187386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1187386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187386 prefixEnd_1187386 := by exact prefixLift 1187386
  have htrace : WordTrace (prefixWord ++ tailWord_1187386) baseStart_1187386 baseEnd_1187386 := by
    simpa [prefixWord, tailWord_1187386, baseEnd_1187386] using wordTrace_append hprefix tailTrace_1187386
  have hstable : (prefixWord ++ tailWord_1187386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187386).length < 2 ^ (prefixWord ++ tailWord_1187386).sum := by decide
  have hdescent : baseEnd_1187386 < baseStart_1187386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187398 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1187398 : Nat := 118140960795 + 1187398 * 2 ^ 59
def prefixEnd_1187398 : Nat := 4983230072969 + 3 ^ 40 * 1187398 * 2
def baseEnd_1187398 : Nat := 609705902187450533564263

theorem tailTrace_1187398 : CollatzResearch.WordTrace tailWord_1187398 prefixEnd_1187398 609705902187450533564263 := by
  unfold tailWord_1187398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353373842258353508701839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28871975301511541518972565 1353373842258353508701839)
  ·
    refine ⟨2030060763387530263052759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353373842258353508701839 2030060763387530263052759)
    ·
      refine ⟨3045091145081295394579139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030060763387530263052759 3045091145081295394579139)
      ·
        refine ⟨4567636717621943091868709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045091145081295394579139 4567636717621943091868709)
        ·
          refine ⟨856431884554114329725383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4567636717621943091868709 856431884554114329725383)
          ·
            refine ⟨1284647826831171494588075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856431884554114329725383 1284647826831171494588075)
            ·
              refine ⟨1926971740246757241882113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284647826831171494588075 1926971740246757241882113)
              ·
                refine ⟨1445228805185067931411585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926971740246757241882113 1445228805185067931411585)
                ·
                  refine ⟨1083921603888800948558689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445228805185067931411585 1083921603888800948558689)
                  ·
                    refine ⟨812941202916600711419017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1083921603888800948558689 812941202916600711419017)
                    ·
                      refine ⟨609705902187450533564263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812941202916600711419017 609705902187450533564263)
                      ·
                        rfl

theorem cell23_1187398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1187398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187398 prefixEnd_1187398 := by exact prefixLift 1187398
  have htrace : WordTrace (prefixWord ++ tailWord_1187398) baseStart_1187398 baseEnd_1187398 := by
    simpa [prefixWord, tailWord_1187398, baseEnd_1187398] using wordTrace_append hprefix tailTrace_1187398
  have hstable : (prefixWord ++ tailWord_1187398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187398).length < 2 ^ (prefixWord ++ tailWord_1187398).sum := by decide
  have hdescent : baseEnd_1187398 < baseStart_1187398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187420 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_1187420 : Nat := 118140960795 + 1187420 * 2 ^ 59
def prefixEnd_1187420 : Nat := 4983230072969 + 3 ^ 40 * 1187420 * 2
def baseEnd_1187420 : Nat := 609717198761849447489161

theorem tailTrace_1187420 : CollatzResearch.WordTrace tailWord_1187420 prefixEnd_1187420 609717198761849447489161 := by
  unfold tailWord_1187420
  simp only [CollatzResearch.WordTrace]
  refine ⟨21654382679093805017879857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28872510238791740023839809 21654382679093805017879857)
  ·
    refine ⟨16240787009320353763409893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21654382679093805017879857 16240787009320353763409893)
    ·
      refine ⟨3045147564247566330639355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16240787009320353763409893 3045147564247566330639355)
      ·
        refine ⟨4567721346371349495959033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045147564247566330639355 4567721346371349495959033)
        ·
          refine ⟨3425791009778512121969275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567721346371349495959033 3425791009778512121969275)
          ·
            refine ⟨5138686514667768182953913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425791009778512121969275 5138686514667768182953913)
            ·
              refine ⟨3854014886000826137215435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5138686514667768182953913 3854014886000826137215435)
              ·
                refine ⟨5781022329001239205823153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854014886000826137215435 5781022329001239205823153)
                ·
                  refine ⟨4335766746750929404367365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781022329001239205823153 4335766746750929404367365)
                  ·
                    refine ⟨812956265015799263318881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4335766746750929404367365 812956265015799263318881)
                    ·
                      refine ⟨609717198761849447489161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 812956265015799263318881 609717198761849447489161)
                      ·
                        rfl

theorem cell23_1187420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_1187420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187420 prefixEnd_1187420 := by exact prefixLift 1187420
  have htrace : WordTrace (prefixWord ++ tailWord_1187420) baseStart_1187420 baseEnd_1187420 := by
    simpa [prefixWord, tailWord_1187420, baseEnd_1187420] using wordTrace_append hprefix tailTrace_1187420
  have hstable : (prefixWord ++ tailWord_1187420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187420).length < 2 ^ (prefixWord ++ tailWord_1187420).sum := by decide
  have hdescent : baseEnd_1187420 < baseStart_1187420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187436 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_1187436 : Nat := 118140960795 + 1187436 * 2 ^ 59
def prefixEnd_1187436 : Nat := 4983230072969 + 3 ^ 40 * 1187436 * 2
def baseEnd_1187436 : Nat := 609725414452321384889087

theorem tailTrace_1187436 : CollatzResearch.WordTrace tailWord_1187436 prefixEnd_1187436 609725414452321384889087 := by
  unfold tailWord_1187436
  simp only [CollatzResearch.WordTrace]
  refine ⟨21654674463064822384171081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28872899284086429845561441 21654674463064822384171081)
  ·
    refine ⟨16241005847298616788128311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21654674463064822384171081 16241005847298616788128311)
    ·
      refine ⟨24361508770947925182192467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16241005847298616788128311 24361508770947925182192467)
      ·
        refine ⟨36542263156421887773288701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24361508770947925182192467 36542263156421887773288701)
        ·
          refine ⟨13703348683658207914983263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36542263156421887773288701 13703348683658207914983263)
          ·
            refine ⟨20555023025487311872474895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13703348683658207914983263 20555023025487311872474895)
            ·
              refine ⟨30832534538230967808712343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20555023025487311872474895 30832534538230967808712343)
              ·
                refine ⟨46248801807346451713068515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30832534538230967808712343 46248801807346451713068515)
                ·
                  refine ⟨69373202711019677569602773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46248801807346451713068515 69373202711019677569602773)
                  ·
                    refine ⟨1625934438539523693037565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 69373202711019677569602773 1625934438539523693037565)
                    ·
                      refine ⟨609725414452321384889087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1625934438539523693037565 609725414452321384889087)
                      ·
                        rfl

theorem cell23_1187436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_1187436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187436 prefixEnd_1187436 := by exact prefixLift 1187436
  have htrace : WordTrace (prefixWord ++ tailWord_1187436) baseStart_1187436 baseEnd_1187436 := by
    simpa [prefixWord, tailWord_1187436, baseEnd_1187436] using wordTrace_append hprefix tailTrace_1187436
  have hstable : (prefixWord ++ tailWord_1187436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187436).length < 2 ^ (prefixWord ++ tailWord_1187436).sum := by decide
  have hdescent : baseEnd_1187436 < baseStart_1187436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187464 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1187464 : Nat := 118140960795 + 1187464 * 2 ^ 59
def prefixEnd_1187464 : Nat := 4983230072969 + 3 ^ 40 * 1187464 * 2
def baseEnd_1187464 : Nat := 203246597303549091779653

theorem tailTrace_1187464 : CollatzResearch.WordTrace tailWord_1187464 prefixEnd_1187464 203246597303549091779653 := by
  unfold tailWord_1187464
  simp only [CollatzResearch.WordTrace]
  refine ⟨21655185085014102775180723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28873580113352137033574297 21655185085014102775180723)
  ·
    refine ⟨32482777627521154162771085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21655185085014102775180723 32482777627521154162771085)
    ·
      refine ⟨12181041610320432811039157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32482777627521154162771085 12181041610320432811039157)
      ·
        refine ⟨1141972650967540576034921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12181041610320432811039157 1141972650967540576034921)
        ·
          refine ⟨856479488225655432026191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141972650967540576034921 856479488225655432026191)
          ·
            refine ⟨1284719232338483148039287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856479488225655432026191 1284719232338483148039287)
            ·
              refine ⟨1927078848507724722058931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284719232338483148039287 1927078848507724722058931)
              ·
                refine ⟨2890618272761587083088397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927078848507724722058931 2890618272761587083088397)
                ·
                  refine ⟨1083981852285595156158149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2890618272761587083088397 1083981852285595156158149)
                  ·
                    refine ⟨203246597303549091779653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1083981852285595156158149 203246597303549091779653)
                    ·
                      rfl

theorem cell23_1187464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1187464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187464 prefixEnd_1187464 := by exact prefixLift 1187464
  have htrace : WordTrace (prefixWord ++ tailWord_1187464) baseStart_1187464 baseEnd_1187464 := by
    simpa [prefixWord, tailWord_1187464, baseEnd_1187464] using wordTrace_append hprefix tailTrace_1187464
  have hstable : (prefixWord ++ tailWord_1187464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187464).length < 2 ^ (prefixWord ++ tailWord_1187464).sum := by decide
  have hdescent : baseEnd_1187464 < baseStart_1187464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187493 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 6, 2]
def baseStart_1187493 : Nat := 118140960795 + 1187493 * 2 ^ 59
def prefixEnd_1187493 : Nat := 4983230072969 + 3 ^ 40 * 1187493 * 2
def baseEnd_1187493 : Nat := 609754682849627661876325

theorem tailTrace_1187493 : CollatzResearch.WordTrace tailWord_1187493 prefixEnd_1187493 609754682849627661876325 := by
  unfold tailWord_1187493
  simp only [CollatzResearch.WordTrace]
  refine ⟨43311427886923143503167133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28874285257948762335444755 43311427886923143503167133)
  ·
    refine ⟨16241785457596178813687675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43311427886923143503167133 16241785457596178813687675)
    ·
      refine ⟨24362678186394268220531513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16241785457596178813687675 24362678186394268220531513)
      ·
        refine ⟨18272008639795701165398635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24362678186394268220531513 18272008639795701165398635)
        ·
          refine ⟨27408012959693551748097953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18272008639795701165398635 27408012959693551748097953)
          ·
            refine ⟨20556009719770163811073465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27408012959693551748097953 20556009719770163811073465)
            ·
              refine ⟨15417007289827622858305099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20556009719770163811073465 15417007289827622858305099)
              ·
                refine ⟨23125510934741434287457649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15417007289827622858305099 23125510934741434287457649)
                ·
                  refine ⟨17344133201056075715593237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23125510934741434287457649 17344133201056075715593237)
                  ·
                    refine ⟨813006243799503549168433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17344133201056075715593237 813006243799503549168433)
                    ·
                      refine ⟨609754682849627661876325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813006243799503549168433 609754682849627661876325)
                      ·
                        rfl

theorem cell23_1187493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_1187493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187493 prefixEnd_1187493 := by exact prefixLift 1187493
  have htrace : WordTrace (prefixWord ++ tailWord_1187493) baseStart_1187493 baseEnd_1187493 := by
    simpa [prefixWord, tailWord_1187493, baseEnd_1187493] using wordTrace_append hprefix tailTrace_1187493
  have hstable : (prefixWord ++ tailWord_1187493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187493).length < 2 ^ (prefixWord ++ tailWord_1187493).sum := by decide
  have hdescent : baseEnd_1187493 < baseStart_1187493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187513 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1187513 : Nat := 118140960795 + 1187513 * 2 ^ 59
def prefixEnd_1187513 : Nat := 4983230072969 + 3 ^ 40 * 1187513 * 2
def baseEnd_1187513 : Nat := 609764952462717583626233

theorem tailTrace_1187513 : CollatzResearch.WordTrace tailWord_1187513 prefixEnd_1187513 609764952462717583626233 := by
  unfold tailWord_1187513
  simp only [CollatzResearch.WordTrace]
  refine ⟨43312157346850686918895193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28874771564567124612596795 43312157346850686918895193)
  ·
    refine ⟨32484118010138015189171395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43312157346850686918895193 32484118010138015189171395)
    ·
      refine ⟨48726177015207022783757093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32484118010138015189171395 48726177015207022783757093)
      ·
        refine ⟨9136158190351316771954455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48726177015207022783757093 9136158190351316771954455)
        ·
          refine ⟨13704237285526975157931683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136158190351316771954455 13704237285526975157931683)
          ·
            refine ⟨20556355928290462736897525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13704237285526975157931683 20556355928290462736897525)
            ·
              refine ⟨1927158368277230881584143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20556355928290462736897525 1927158368277230881584143)
              ·
                refine ⟨2890737552415846322376215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927158368277230881584143 2890737552415846322376215)
                ·
                  refine ⟨4336106328623769483564323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890737552415846322376215 4336106328623769483564323)
                  ·
                    refine ⟨6504159492935654225346485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336106328623769483564323 6504159492935654225346485)
                    ·
                      refine ⟨609764952462717583626233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6504159492935654225346485 609764952462717583626233)
                      ·
                        rfl

theorem cell23_1187513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1187513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187513 prefixEnd_1187513 := by exact prefixLift 1187513
  have htrace : WordTrace (prefixWord ++ tailWord_1187513) baseStart_1187513 baseEnd_1187513 := by
    simpa [prefixWord, tailWord_1187513, baseEnd_1187513] using wordTrace_append hprefix tailTrace_1187513
  have hstable : (prefixWord ++ tailWord_1187513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187513).length < 2 ^ (prefixWord ++ tailWord_1187513).sum := by decide
  have hdescent : baseEnd_1187513 < baseStart_1187513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187516 : List Nat := [2, 2, 2, 3, 1, 13]
def baseStart_1187516 : Nat := 118140960795 + 1187516 * 2 ^ 59
def prefixEnd_1187516 : Nat := 4983230072969 + 3 ^ 40 * 1187516 * 2
def baseEnd_1187516 : Nat := 2509327131294983834933

theorem tailTrace_1187516 : CollatzResearch.WordTrace tailWord_1187516 prefixEnd_1187516 2509327131294983834933 := by
  unfold tailWord_1187516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21656133382919909215627201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28874844510559878954169601 21656133382919909215627201)
  ·
    refine ⟨16242100037189931911720401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21656133382919909215627201 16242100037189931911720401)
    ·
      refine ⟨12181575027892448933790301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16242100037189931911720401 12181575027892448933790301)
      ·
        refine ⟨4568090635459668350171363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12181575027892448933790301 4568090635459668350171363)
        ·
          refine ⟨6852135953189502525257045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568090635459668350171363 6852135953189502525257045)
          ·
            refine ⟨2509327131294983834933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 6852135953189502525257045 2509327131294983834933)
            ·
              rfl

theorem cell23_1187516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 13].length) (baseStart_1187516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187516 prefixEnd_1187516 := by exact prefixLift 1187516
  have htrace : WordTrace (prefixWord ++ tailWord_1187516) baseStart_1187516 baseEnd_1187516 := by
    simpa [prefixWord, tailWord_1187516, baseEnd_1187516] using wordTrace_append hprefix tailTrace_1187516
  have hstable : (prefixWord ++ tailWord_1187516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187516).length < 2 ^ (prefixWord ++ tailWord_1187516).sum := by decide
  have hdescent : baseEnd_1187516 < baseStart_1187516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187520 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 2, 4]
def baseStart_1187520 : Nat := 118140960795 + 1187520 * 2 ^ 59
def prefixEnd_1187520 : Nat := 4983230072969 + 3 ^ 40 * 1187520 * 2
def baseEnd_1187520 : Nat := 203256182275766352079567

theorem tailTrace_1187520 : CollatzResearch.WordTrace tailWord_1187520 prefixEnd_1187520 203256182275766352079567 := by
  unfold tailWord_1187520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21656206328912663557200007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28874941771883551409600009 21656206328912663557200007)
  ·
    refine ⟨32484309493368995335800011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21656206328912663557200007 32484309493368995335800011)
    ·
      refine ⟨48726464240053493003700017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32484309493368995335800011 48726464240053493003700017)
      ·
        refine ⟨36544848180040119752775013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48726464240053493003700017 36544848180040119752775013)
        ·
          refine ⟨6852159033757522453645315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36544848180040119752775013 6852159033757522453645315)
          ·
            refine ⟨10278238550636283680467973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852159033757522453645315 10278238550636283680467973)
            ·
              refine ⟨1927169728244303190087745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10278238550636283680467973 1927169728244303190087745)
              ·
                refine ⟨1445377296183227392565809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927169728244303190087745 1445377296183227392565809)
                ·
                  refine ⟨1084032972137420544424357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445377296183227392565809 1084032972137420544424357)
                  ·
                    refine ⟨203256182275766352079567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1084032972137420544424357 203256182275766352079567)
                    ·
                      rfl

theorem cell23_1187520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_1187520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187520 prefixEnd_1187520 := by exact prefixLift 1187520
  have htrace : WordTrace (prefixWord ++ tailWord_1187520) baseStart_1187520 baseEnd_1187520 := by
    simpa [prefixWord, tailWord_1187520, baseEnd_1187520] using wordTrace_append hprefix tailTrace_1187520
  have hstable : (prefixWord ++ tailWord_1187520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187520).length < 2 ^ (prefixWord ++ tailWord_1187520).sum := by decide
  have hdescent : baseEnd_1187520 < baseStart_1187520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187540 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1187540 : Nat := 118140960795 + 1187540 * 2 ^ 59
def prefixEnd_1187540 : Nat := 4983230072969 + 3 ^ 40 * 1187540 * 2
def baseEnd_1187540 : Nat := 609778816440388977988609

theorem tailTrace_1187540 : CollatzResearch.WordTrace tailWord_1187540 prefixEnd_1187540 609778816440388977988609 := by
  unfold tailWord_1187540
  simp only [CollatzResearch.WordTrace]
  refine ⟨21656571058876435265064037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28875428078501913686752049 21656571058876435265064037)
  ·
    refine ⟨4060607073539331612199507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21656571058876435265064037 4060607073539331612199507)
    ·
      refine ⟨6090910610308997418299261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060607073539331612199507 6090910610308997418299261)
      ·
        refine ⟨2284091478865874031862223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6090910610308997418299261 2284091478865874031862223)
        ·
          refine ⟨3426137218298811047793335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2284091478865874031862223 3426137218298811047793335)
          ·
            refine ⟨5139205827448216571690003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426137218298811047793335 5139205827448216571690003)
            ·
              refine ⟨7708808741172324857535005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139205827448216571690003 7708808741172324857535005)
              ·
                refine ⟨2890803277939621821575627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7708808741172324857535005 2890803277939621821575627)
                ·
                  refine ⟨4336204916909432732363441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890803277939621821575627 4336204916909432732363441)
                  ·
                    refine ⟨3252153687682074549272581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4336204916909432732363441 3252153687682074549272581)
                    ·
                      refine ⟨609778816440388977988609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3252153687682074549272581 609778816440388977988609)
                      ·
                        rfl

theorem cell23_1187540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1187540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187540 prefixEnd_1187540 := by exact prefixLift 1187540
  have htrace : WordTrace (prefixWord ++ tailWord_1187540) baseStart_1187540 baseEnd_1187540 := by
    simpa [prefixWord, tailWord_1187540, baseEnd_1187540] using wordTrace_append hprefix tailTrace_1187540
  have hstable : (prefixWord ++ tailWord_1187540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187540).length < 2 ^ (prefixWord ++ tailWord_1187540).sum := by decide
  have hdescent : baseEnd_1187540 < baseStart_1187540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187560 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1187560 : Nat := 118140960795 + 1187560 * 2 ^ 59
def prefixEnd_1187560 : Nat := 4983230072969 + 3 ^ 40 * 1187560 * 2
def baseEnd_1187560 : Nat := 609789086053478899738517

theorem tailTrace_1187560 : CollatzResearch.WordTrace tailWord_1187560 prefixEnd_1187560 609789086053478899738517 := by
  unfold tailWord_1187560
  simp only [CollatzResearch.WordTrace]
  refine ⟨21656935788840206972928067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28875914385120275963904089 21656935788840206972928067)
  ·
    refine ⟨32485403683260310459392101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21656935788840206972928067 32485403683260310459392101)
    ·
      refine ⟨6091013190611308211136019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32485403683260310459392101 6091013190611308211136019)
      ·
        refine ⟨9136519785916962316704029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091013190611308211136019 9136519785916962316704029)
        ·
          refine ⟨3426194919718860868764011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9136519785916962316704029 3426194919718860868764011)
          ·
            refine ⟨5139292379578291303146017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426194919718860868764011 5139292379578291303146017)
            ·
              refine ⟨3854469284683718477359513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5139292379578291303146017 3854469284683718477359513)
              ·
                refine ⟨2890851963512788858019635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854469284683718477359513 2890851963512788858019635)
                ·
                  refine ⟨4336277945269183287029453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2890851963512788858019635 4336277945269183287029453)
                  ·
                    refine ⟨1626104229475943732636045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4336277945269183287029453 1626104229475943732636045)
                    ·
                      refine ⟨609789086053478899738517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1626104229475943732636045 609789086053478899738517)
                      ·
                        rfl

theorem cell23_1187560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1187560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187560 prefixEnd_1187560 := by exact prefixLift 1187560
  have htrace : WordTrace (prefixWord ++ tailWord_1187560) baseStart_1187560 baseEnd_1187560 := by
    simpa [prefixWord, tailWord_1187560, baseEnd_1187560] using wordTrace_append hprefix tailTrace_1187560
  have hstable : (prefixWord ++ tailWord_1187560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187560).length < 2 ^ (prefixWord ++ tailWord_1187560).sum := by decide
  have hdescent : baseEnd_1187560 < baseStart_1187560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187594 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_1187594 : Nat := 118140960795 + 1187594 * 2 ^ 59
def prefixEnd_1187594 : Nat := 4983230072969 + 3 ^ 40 * 1187594 * 2
def baseEnd_1187594 : Nat := 609806544395731766713361

theorem tailTrace_1187594 : CollatzResearch.WordTrace tailWord_1187594 prefixEnd_1187594 609806544395731766713361 := by
  unfold tailWord_1187594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10828777914889309438148459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28876741106371491835062557 10828777914889309438148459)
  ·
    refine ⟨16243166872333964157222689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10828777914889309438148459 16243166872333964157222689)
    ·
      refine ⟨12182375154250473117917017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16243166872333964157222689 12182375154250473117917017)
      ·
        refine ⟨9136781365687854838437763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12182375154250473117917017 9136781365687854838437763)
        ·
          refine ⟨13705172048531782257656645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136781365687854838437763 13705172048531782257656645)
          ·
            refine ⟨2569719759099709173310621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13705172048531782257656645 2569719759099709173310621)
            ·
              refine ⟨963644909662390939991483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2569719759099709173310621 963644909662390939991483)
              ·
                refine ⟨1445467364493586409987225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963644909662390939991483 1445467364493586409987225)
                ·
                  refine ⟨1084100523370189807490419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445467364493586409987225 1084100523370189807490419)
                  ·
                    refine ⟨1626150785055284711235629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1084100523370189807490419 1626150785055284711235629)
                    ·
                      refine ⟨609806544395731766713361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1626150785055284711235629 609806544395731766713361)
                      ·
                        rfl

theorem cell23_1187594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_1187594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187594 prefixEnd_1187594 := by exact prefixLift 1187594
  have htrace : WordTrace (prefixWord ++ tailWord_1187594) baseStart_1187594 baseEnd_1187594 := by
    simpa [prefixWord, tailWord_1187594, baseEnd_1187594] using wordTrace_append hprefix tailTrace_1187594
  have hstable : (prefixWord ++ tailWord_1187594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187594).length < 2 ^ (prefixWord ++ tailWord_1187594).sum := by decide
  have hdescent : baseEnd_1187594 < baseStart_1187594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187617 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_1187617 : Nat := 118140960795 + 1187617 * 2 ^ 59
def prefixEnd_1187617 : Nat := 4983230072969 + 3 ^ 40 * 1187617 * 2
def baseEnd_1187617 : Nat := 609818354450785176725755

theorem tailTrace_1187617 : CollatzResearch.WordTrace tailWord_1187617 prefixEnd_1187617 609818354450785176725755 := by
  unfold tailWord_1187617
  simp only [CollatzResearch.WordTrace]
  refine ⟨43315950538473912680681105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28877300358982608453787403 43315950538473912680681105)
  ·
    refine ⟨32486962903855434510510829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43315950538473912680681105 32486962903855434510510829)
    ·
      refine ⟨12182611088945787941441561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32486962903855434510510829 12182611088945787941441561)
      ·
        refine ⟨9136958316709340956081171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12182611088945787941441561 9136958316709340956081171)
        ·
          refine ⟨13705437475064011434121757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136958316709340956081171 13705437475064011434121757)
          ·
            refine ⟨5139539053149004287795659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13705437475064011434121757 5139539053149004287795659)
            ·
              refine ⟨7709308579723506431693489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139539053149004287795659 7709308579723506431693489)
              ·
                refine ⟨5781981434792629823770117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7709308579723506431693489 5781981434792629823770117)
                ·
                  refine ⟨1084121519023618091956897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5781981434792629823770117 1084121519023618091956897)
                  ·
                    refine ⟨813091139267713568967673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1084121519023618091956897 813091139267713568967673)
                    ·
                      refine ⟨609818354450785176725755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813091139267713568967673 609818354450785176725755)
                      ·
                        rfl

theorem cell23_1187617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_1187617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187617 prefixEnd_1187617 := by exact prefixLift 1187617
  have htrace : WordTrace (prefixWord ++ tailWord_1187617) baseStart_1187617 baseEnd_1187617 := by
    simpa [prefixWord, tailWord_1187617, baseEnd_1187617] using wordTrace_append hprefix tailTrace_1187617
  have hstable : (prefixWord ++ tailWord_1187617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187617).length < 2 ^ (prefixWord ++ tailWord_1187617).sum := by decide
  have hdescent : baseEnd_1187617 < baseStart_1187617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187620 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1187620 : Nat := 118140960795 + 1187620 * 2 ^ 59
def prefixEnd_1187620 : Nat := 4983230072969 + 3 ^ 40 * 1187620 * 2
def baseEnd_1187620 : Nat := 609819894892748664988241

theorem tailTrace_1187620 : CollatzResearch.WordTrace tailWord_1187620 prefixEnd_1187620 609819894892748664988241 := by
  unfold tailWord_1187620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658029978731522096520157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28877373304975362795360209 21658029978731522096520157)
  ·
    refine ⟨8121761242024320786195059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21658029978731522096520157 8121761242024320786195059)
    ·
      refine ⟨12182641863036481179292589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8121761242024320786195059 12182641863036481179292589)
      ·
        refine ⟨4568490698638680442234721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12182641863036481179292589 4568490698638680442234721)
        ·
          refine ⟨3426368023979010331676041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4568490698638680442234721 3426368023979010331676041)
          ·
            refine ⟨2569776017984257748757031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3426368023979010331676041 2569776017984257748757031)
            ·
              refine ⟨3854664026976386623135547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569776017984257748757031 3854664026976386623135547)
              ·
                refine ⟨5781996040464579934703321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3854664026976386623135547 5781996040464579934703321)
                ·
                  refine ⟨4336497030348434951027491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5781996040464579934703321 4336497030348434951027491)
                  ·
                    refine ⟨6504745545522652426541237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4336497030348434951027491 6504745545522652426541237)
                    ·
                      refine ⟨609819894892748664988241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6504745545522652426541237 609819894892748664988241)
                      ·
                        rfl

theorem cell23_1187620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1187620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187620 prefixEnd_1187620 := by exact prefixLift 1187620
  have htrace : WordTrace (prefixWord ++ tailWord_1187620) baseStart_1187620 baseEnd_1187620 := by
    simpa [prefixWord, tailWord_1187620, baseEnd_1187620] using wordTrace_append hprefix tailTrace_1187620
  have hstable : (prefixWord ++ tailWord_1187620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187620).length < 2 ^ (prefixWord ++ tailWord_1187620).sum := by decide
  have hdescent : baseEnd_1187620 < baseStart_1187620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187640 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 7]
def baseStart_1187640 : Nat := 118140960795 + 1187640 * 2 ^ 59
def prefixEnd_1187640 : Nat := 4983230072969 + 3 ^ 40 * 1187640 * 2
def baseEnd_1187640 : Nat := 67758907167315398526461

theorem tailTrace_1187640 : CollatzResearch.WordTrace tailWord_1187640 prefixEnd_1187640 67758907167315398526461 := by
  unfold tailWord_1187640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658394708695293804384187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28877859611593725072512249 21658394708695293804384187)
  ·
    refine ⟨32487592063042940706576281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21658394708695293804384187 32487592063042940706576281)
    ·
      refine ⟨24365694047282205529932211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32487592063042940706576281 24365694047282205529932211)
      ·
        refine ⟨36548541070923308294898317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24365694047282205529932211 36548541070923308294898317)
        ·
          refine ⟨13705702901596240610586869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36548541070923308294898317 13705702901596240610586869)
          ·
            refine ⟨1284909647024647557242519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13705702901596240610586869 1284909647024647557242519)
            ·
              refine ⟨1927364470536971335863779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284909647024647557242519 1927364470536971335863779)
              ·
                refine ⟨2891046705805457003795669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927364470536971335863779 2891046705805457003795669)
                ·
                  refine ⟨67758907167315398526461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2891046705805457003795669 67758907167315398526461)
                  ·
                    rfl

theorem cell23_1187640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 7].length) (baseStart_1187640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187640 prefixEnd_1187640 := by exact prefixLift 1187640
  have htrace : WordTrace (prefixWord ++ tailWord_1187640) baseStart_1187640 baseEnd_1187640 := by
    simpa [prefixWord, tailWord_1187640, baseEnd_1187640] using wordTrace_append hprefix tailTrace_1187640
  have hstable : (prefixWord ++ tailWord_1187640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187640).length < 2 ^ (prefixWord ++ tailWord_1187640).sum := by decide
  have hdescent : baseEnd_1187640 < baseStart_1187640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187651 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 2, 2, 2]
def baseStart_1187651 : Nat := 118140960795 + 1187651 * 2 ^ 59
def prefixEnd_1187651 : Nat := 4983230072969 + 3 ^ 40 * 1187651 * 2
def baseEnd_1187651 : Nat := 609835812793038043700599

theorem tailTrace_1187651 : CollatzResearch.WordTrace tailWord_1187651 prefixEnd_1187651 609835812793038043700599 := by
  unfold tailWord_1187651
  simp only [CollatzResearch.WordTrace]
  refine ⟨43317190620350736487418807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28878127080233824324945871 43317190620350736487418807)
  ·
    refine ⟨64975785930526104731128211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43317190620350736487418807 64975785930526104731128211)
    ·
      refine ⟨97463678895789157096692317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64975785930526104731128211 97463678895789157096692317)
      ·
        refine ⟨36548879585920933911259619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97463678895789157096692317 36548879585920933911259619)
        ·
          refine ⟨54823319378881400866889429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36548879585920933911259619 54823319378881400866889429)
          ·
            refine ⟨1284921547942532832817721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54823319378881400866889429 1284921547942532832817721)
            ·
              refine ⟨963691160956899624613291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284921547942532832817721 963691160956899624613291)
              ·
                refine ⟨1445536741435349436919937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963691160956899624613291 1445536741435349436919937)
                ·
                  refine ⟨1084152556076512077689953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445536741435349436919937 1084152556076512077689953)
                  ·
                    refine ⟨813114417057384058267465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1084152556076512077689953 813114417057384058267465)
                    ·
                      refine ⟨609835812793038043700599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813114417057384058267465 609835812793038043700599)
                      ·
                        rfl

theorem cell23_1187651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_1187651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187651 prefixEnd_1187651 := by exact prefixLift 1187651
  have htrace : WordTrace (prefixWord ++ tailWord_1187651) baseStart_1187651 baseEnd_1187651 := by
    simpa [prefixWord, tailWord_1187651, baseEnd_1187651] using wordTrace_append hprefix tailTrace_1187651
  have hstable : (prefixWord ++ tailWord_1187651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187651).length < 2 ^ (prefixWord ++ tailWord_1187651).sum := by decide
  have hdescent : baseEnd_1187651 < baseStart_1187651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187653 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_1187653 : Nat := 118140960795 + 1187653 * 2 ^ 59
def prefixEnd_1187653 : Nat := 4983230072969 + 3 ^ 40 * 1187653 * 2
def baseEnd_1187653 : Nat := 203278946584782345291863

theorem tailTrace_1187653 : CollatzResearch.WordTrace tailWord_1187653 prefixEnd_1187653 203278946584782345291863 := by
  unfold tailWord_1187653
  simp only [CollatzResearch.WordTrace]
  refine ⟨43317263566343490828991613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28878175710895660552661075 43317263566343490828991613)
  ·
    refine ⟨16243973837378809060871855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43317263566343490828991613 16243973837378809060871855)
    ·
      refine ⟨24365960756068213591307783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16243973837378809060871855 24365960756068213591307783)
      ·
        refine ⟨36548941134102320386961675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24365960756068213591307783 36548941134102320386961675)
        ·
          refine ⟨54823411701153480580442513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36548941134102320386961675 54823411701153480580442513)
          ·
            refine ⟨41117558775865110435331885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54823411701153480580442513 41117558775865110435331885)
            ·
              refine ⟨15419084540949416413249457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41117558775865110435331885 15419084540949416413249457)
              ·
                refine ⟨11564313405712062309937093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15419084540949416413249457 11564313405712062309937093)
                ·
                  refine ⟨2168308763571011683113205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11564313405712062309937093 2168308763571011683113205)
                  ·
                    refine ⟨203278946584782345291863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2168308763571011683113205 203278946584782345291863)
                    ·
                      rfl

theorem cell23_1187653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_1187653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187653 prefixEnd_1187653 := by exact prefixLift 1187653
  have htrace : WordTrace (prefixWord ++ tailWord_1187653) baseStart_1187653 baseEnd_1187653 := by
    simpa [prefixWord, tailWord_1187653, baseEnd_1187653] using wordTrace_append hprefix tailTrace_1187653
  have hstable : (prefixWord ++ tailWord_1187653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187653).length < 2 ^ (prefixWord ++ tailWord_1187653).sum := by decide
  have hdescent : baseEnd_1187653 < baseStart_1187653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187703 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_1187703 : Nat := 118140960795 + 1187703 * 2 ^ 59
def prefixEnd_1187703 : Nat := 4983230072969 + 3 ^ 40 * 1187703 * 2
def baseEnd_1187703 : Nat := 609862513787071840250359

theorem tailTrace_1187703 : CollatzResearch.WordTrace tailWord_1187703 prefixEnd_1187703 609862513787071840250359 := by
  unfold tailWord_1187703
  simp only [CollatzResearch.WordTrace]
  refine ⟨43319087216162349368311763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28879391477441566245541175 43319087216162349368311763)
  ·
    refine ⟨64978630824243524052467645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43319087216162349368311763 64978630824243524052467645)
    ·
      refine ⟨24366986559091321519675367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64978630824243524052467645 24366986559091321519675367)
      ·
        refine ⟨36550479838636982279513051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24366986559091321519675367 36550479838636982279513051)
        ·
          refine ⟨54825719757955473419269577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36550479838636982279513051 54825719757955473419269577)
          ·
            refine ⟨41119289818466605064452183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54825719757955473419269577 41119289818466605064452183)
            ·
              refine ⟨61678934727699907596678275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41119289818466605064452183 61678934727699907596678275)
              ·
                refine ⟨92518402091549861395017413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61678934727699907596678275 92518402091549861395017413)
                ·
                  refine ⟨17347200392165599011565765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92518402091549861395017413 17347200392165599011565765)
                  ·
                    refine ⟨3252600073531049814668581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17347200392165599011565765 3252600073531049814668581)
                    ·
                      refine ⟨609862513787071840250359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3252600073531049814668581 609862513787071840250359)
                      ·
                        rfl

theorem cell23_1187703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_1187703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187703 prefixEnd_1187703 := by exact prefixLift 1187703
  have htrace : WordTrace (prefixWord ++ tailWord_1187703) baseStart_1187703 baseEnd_1187703 := by
    simpa [prefixWord, tailWord_1187703, baseEnd_1187703] using wordTrace_append hprefix tailTrace_1187703
  have hstable : (prefixWord ++ tailWord_1187703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187703).length < 2 ^ (prefixWord ++ tailWord_1187703).sum := by decide
  have hdescent : baseEnd_1187703 < baseStart_1187703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187753 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_1187753 : Nat := 118140960795 + 1187753 * 2 ^ 59
def prefixEnd_1187753 : Nat := 4983230072969 + 3 ^ 40 * 1187753 * 2
def baseEnd_1187753 : Nat := 609888187819796644625129

theorem tailTrace_1187753 : CollatzResearch.WordTrace tailWord_1187753 prefixEnd_1187753 609888187819796644625129 := by
  unfold tailWord_1187753
  simp only [CollatzResearch.WordTrace]
  refine ⟨43320910865981207907631913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28880607243987471938421275 43320910865981207907631913)
  ·
    refine ⟨32490683149485905930723935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43320910865981207907631913 32490683149485905930723935)
    ·
      refine ⟨48736024724228858896085903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32490683149485905930723935 48736024724228858896085903)
      ·
        refine ⟨73104037086343288344128855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48736024724228858896085903 73104037086343288344128855)
        ·
          refine ⟨109656055629514932516193283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73104037086343288344128855 109656055629514932516193283)
          ·
            refine ⟨164484083444272398774289925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109656055629514932516193283 164484083444272398774289925)
            ·
              refine ⟨30840765645801074770179361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164484083444272398774289925 30840765645801074770179361)
              ·
                refine ⟨23130574234350806077634521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30840765645801074770179361 23130574234350806077634521)
                ·
                  refine ⟨17347930675763104558225891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23130574234350806077634521 17347930675763104558225891)
                  ·
                    refine ⟨26021896013644656837338837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17347930675763104558225891 26021896013644656837338837)
                    ·
                      refine ⟨609888187819796644625129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26021896013644656837338837 609888187819796644625129)
                      ·
                        rfl

theorem cell23_1187753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_1187753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187753 prefixEnd_1187753 := by exact prefixLift 1187753
  have htrace : WordTrace (prefixWord ++ tailWord_1187753) baseStart_1187753 baseEnd_1187753 := by
    simpa [prefixWord, tailWord_1187753, baseEnd_1187753] using wordTrace_append hprefix tailTrace_1187753
  have hstable : (prefixWord ++ tailWord_1187753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187753).length < 2 ^ (prefixWord ++ tailWord_1187753).sum := by decide
  have hdescent : baseEnd_1187753 < baseStart_1187753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187774 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1187774 : Nat := 118140960795 + 1187774 * 2 ^ 59
def prefixEnd_1187774 : Nat := 4983230072969 + 3 ^ 40 * 1187774 * 2
def baseEnd_1187774 : Nat := 609898970913541062462533

theorem tailTrace_1187774 : CollatzResearch.WordTrace tailWord_1187774 prefixEnd_1187774 609898970913541062462533 := by
  unfold tailWord_1187774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415209599863141061768297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28881117865936752329430917 5415209599863141061768297)
  ·
    refine ⟨4061407199897355796326223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5415209599863141061768297 4061407199897355796326223)
    ·
      refine ⟨6092110799846033694489335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061407199897355796326223 6092110799846033694489335)
      ·
        refine ⟨9138166199769050541734003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6092110799846033694489335 9138166199769050541734003)
        ·
          refine ⟨13707249299653575812601005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9138166199769050541734003 13707249299653575812601005)
          ·
            refine ⟨5140218487370090929725377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13707249299653575812601005 5140218487370090929725377)
            ·
              refine ⟨3855163865527568197294033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5140218487370090929725377 3855163865527568197294033)
              ·
                refine ⟨2891372899145676147970525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855163865527568197294033 2891372899145676147970525)
                ·
                  refine ⟨1084264837179628555488947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2891372899145676147970525 1084264837179628555488947)
                  ·
                    refine ⟨1626397255769442833233421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1084264837179628555488947 1626397255769442833233421)
                    ·
                      refine ⟨609898970913541062462533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1626397255769442833233421 609898970913541062462533)
                      ·
                        rfl

theorem cell23_1187774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1187774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187774 prefixEnd_1187774 := by exact prefixLift 1187774
  have htrace : WordTrace (prefixWord ++ tailWord_1187774) baseStart_1187774 baseEnd_1187774 := by
    simpa [prefixWord, tailWord_1187774, baseEnd_1187774] using wordTrace_append hprefix tailTrace_1187774
  have hstable : (prefixWord ++ tailWord_1187774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187774).length < 2 ^ (prefixWord ++ tailWord_1187774).sum := by decide
  have hdescent : baseEnd_1187774 < baseStart_1187774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187790 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_1187790 : Nat := 118140960795 + 1187790 * 2 ^ 59
def prefixEnd_1187790 : Nat := 4983230072969 + 3 ^ 40 * 1187790 * 2
def baseEnd_1187790 : Nat := 203302395534670999954153

theorem tailTrace_1187790 : CollatzResearch.WordTrace tailWord_1187790 prefixEnd_1187790 203302395534670999954153 := by
  unfold tailWord_1187790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415282545855895403341103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28881506911231442151152549 5415282545855895403341103)
  ·
    refine ⟨8122923818783843105011655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5415282545855895403341103 8122923818783843105011655)
    ·
      refine ⟨12184385728175764657517483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8122923818783843105011655 12184385728175764657517483)
      ·
        refine ⟨18276578592263646986276225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12184385728175764657517483 18276578592263646986276225)
        ·
          refine ⟨13707433944197735239707169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18276578592263646986276225 13707433944197735239707169)
          ·
            refine ⟨10280575458148301429780377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13707433944197735239707169 10280575458148301429780377)
            ·
              refine ⟨7710431593611226072335283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10280575458148301429780377 7710431593611226072335283)
              ·
                refine ⟨11565647390416839108502925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7710431593611226072335283 11565647390416839108502925)
                ·
                  refine ⟨4337117771406314665688597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11565647390416839108502925 4337117771406314665688597)
                  ·
                    refine ⟨203302395534670999954153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4337117771406314665688597 203302395534670999954153)
                    ·
                      rfl

theorem cell23_1187790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_1187790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187790 prefixEnd_1187790 := by exact prefixLift 1187790
  have htrace : WordTrace (prefixWord ++ tailWord_1187790) baseStart_1187790 baseEnd_1187790 := by
    simpa [prefixWord, tailWord_1187790, baseEnd_1187790] using wordTrace_append hprefix tailTrace_1187790
  have hstable : (prefixWord ++ tailWord_1187790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187790).length < 2 ^ (prefixWord ++ tailWord_1187790).sum := by decide
  have hdescent : baseEnd_1187790 < baseStart_1187790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187807 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 4, 4]
def baseStart_1187807 : Nat := 118140960795 + 1187807 * 2 ^ 59
def prefixEnd_1187807 : Nat := 4983230072969 + 3 ^ 40 * 1187807 * 2
def baseEnd_1187807 : Nat := 203305305258379811116627

theorem tailTrace_1187807 : CollatzResearch.WordTrace tailWord_1187807 prefixEnd_1187807 203305305258379811116627 := by
  unfold tailWord_1187807
  simp only [CollatzResearch.WordTrace]
  refine ⟨43322880407785575130097675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28881920271857050086731783 43322880407785575130097675)
  ·
    refine ⟨64984320611678362695146513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43322880407785575130097675 64984320611678362695146513)
    ·
      refine ⟨48738240458758772021359885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64984320611678362695146513 48738240458758772021359885)
      ·
        refine ⟨18276840172034539508009957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48738240458758772021359885 18276840172034539508009957)
        ·
          refine ⟨3426907532256476157751867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18276840172034539508009957 3426907532256476157751867)
          ·
            refine ⟨5140361298384714236627801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426907532256476157751867 5140361298384714236627801)
            ·
              refine ⟨3855270973788535677470851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5140361298384714236627801 3855270973788535677470851)
              ·
                refine ⟨5782906460682803516206277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3855270973788535677470851 5782906460682803516206277)
                ·
                  refine ⟨1084294961378025659288677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5782906460682803516206277 1084294961378025659288677)
                  ·
                    refine ⟨203305305258379811116627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1084294961378025659288677 203305305258379811116627)
                    ·
                      rfl

theorem cell23_1187807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_1187807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187807 prefixEnd_1187807 := by exact prefixLift 1187807
  have htrace : WordTrace (prefixWord ++ tailWord_1187807) baseStart_1187807 baseEnd_1187807 := by
    simpa [prefixWord, tailWord_1187807, baseEnd_1187807] using wordTrace_append hprefix tailTrace_1187807
  have hstable : (prefixWord ++ tailWord_1187807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187807).length < 2 ^ (prefixWord ++ tailWord_1187807).sum := by decide
  have hdescent : baseEnd_1187807 < baseStart_1187807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187824 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 2, 4]
def baseStart_1187824 : Nat := 118140960795 + 1187824 * 2 ^ 59
def prefixEnd_1187824 : Nat := 4983230072969 + 3 ^ 40 * 1187824 * 2
def baseEnd_1187824 : Nat := 203308214982088622279101

theorem tailTrace_1187824 : CollatzResearch.WordTrace tailWord_1187824 prefixEnd_1187824 203308214982088622279101 := by
  unfold tailWord_1187824
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661750224361993516733263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28882333632482658022311017 21661750224361993516733263)
  ·
    refine ⟨32492625336542990275099895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21661750224361993516733263 32492625336542990275099895)
    ·
      refine ⟨48738938004814485412649843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32492625336542990275099895 48738938004814485412649843)
      ·
        refine ⟨73108407007221728118974765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48738938004814485412649843 73108407007221728118974765)
        ·
          refine ⟨27415652627708148044615537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73108407007221728118974765 27415652627708148044615537)
          ·
            refine ⟨20561739470781111033461653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27415652627708148044615537 20561739470781111033461653)
            ·
              refine ⟨963831537692864579693515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20561739470781111033461653 963831537692864579693515)
              ·
                refine ⟨1445747306539296869540273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963831537692864579693515 1445747306539296869540273)
                ·
                  refine ⟨1084310479904472652155205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445747306539296869540273 1084310479904472652155205)
                  ·
                    refine ⟨203308214982088622279101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1084310479904472652155205 203308214982088622279101)
                    ·
                      rfl

theorem cell23_1187824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 4].length) (baseStart_1187824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187824 prefixEnd_1187824 := by exact prefixLift 1187824
  have htrace : WordTrace (prefixWord ++ tailWord_1187824) baseStart_1187824 baseEnd_1187824 := by
    simpa [prefixWord, tailWord_1187824, baseEnd_1187824] using wordTrace_append hprefix tailTrace_1187824
  have hstable : (prefixWord ++ tailWord_1187824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187824).length < 2 ^ (prefixWord ++ tailWord_1187824).sum := by decide
  have hdescent : baseEnd_1187824 < baseStart_1187824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187847 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1187847 : Nat := 118140960795 + 1187847 * 2 ^ 59
def prefixEnd_1187847 : Nat := 4983230072969 + 3 ^ 40 * 1187847 * 2
def baseEnd_1187847 : Nat := 609936455001319276849697

theorem tailTrace_1187847 : CollatzResearch.WordTrace tailWord_1187847 prefixEnd_1187847 609936455001319276849697 := by
  unfold tailWord_1187847
  simp only [CollatzResearch.WordTrace]
  refine ⟨43324339327640661961553795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28882892885093774641035863 43324339327640661961553795)
  ·
    refine ⟨64986508991460992942330693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43324339327640661961553795 64986508991460992942330693)
    ·
      refine ⟨12184970435898936176687005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64986508991460992942330693 12184970435898936176687005)
      ·
        refine ⟨4569363913462101066257627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12184970435898936176687005 4569363913462101066257627)
        ·
          refine ⟨6854045870193151599386441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569363913462101066257627 6854045870193151599386441)
          ·
            refine ⟨5140534402644863699539831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6854045870193151599386441 5140534402644863699539831)
            ·
              refine ⟨7710801603967295549309747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5140534402644863699539831 7710801603967295549309747)
              ·
                refine ⟨11566202405950943323964621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7710801603967295549309747 11566202405950943323964621)
                ·
                  refine ⟨4337325902231603746486733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11566202405950943323964621 4337325902231603746486733)
                  ·
                    refine ⟨1626497213336851404932525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4337325902231603746486733 1626497213336851404932525)
                    ·
                      refine ⟨609936455001319276849697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1626497213336851404932525 609936455001319276849697)
                      ·
                        rfl

theorem cell23_1187847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1187847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187847 prefixEnd_1187847 := by exact prefixLift 1187847
  have htrace : WordTrace (prefixWord ++ tailWord_1187847) baseStart_1187847 baseEnd_1187847 := by
    simpa [prefixWord, tailWord_1187847, baseEnd_1187847] using wordTrace_append hprefix tailTrace_1187847
  have hstable : (prefixWord ++ tailWord_1187847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187847).length < 2 ^ (prefixWord ++ tailWord_1187847).sum := by decide
  have hdescent : baseEnd_1187847 < baseStart_1187847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187874 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_1187874 : Nat := 118140960795 + 1187874 * 2 ^ 59
def prefixEnd_1187874 : Nat := 4983230072969 + 3 ^ 40 * 1187874 * 2
def baseEnd_1187874 : Nat := 609950318978990671212073

theorem tailTrace_1187874 : CollatzResearch.WordTrace tailWord_1187874 prefixEnd_1187874 609950318978990671212073 := by
  unfold tailWord_1187874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831331024635711393196669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28883549399028563715191117 10831331024635711393196669)
  ·
    refine ⟨4061749134238391772448751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10831331024635711393196669 4061749134238391772448751)
    ·
      refine ⟨6092623701357587658673127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061749134238391772448751 6092623701357587658673127)
      ·
        refine ⟨9138935552036381488009691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6092623701357587658673127 9138935552036381488009691)
        ·
          refine ⟨13708403328054572232014537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9138935552036381488009691 13708403328054572232014537)
          ·
            refine ⟨10281302496040929174010903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13708403328054572232014537 10281302496040929174010903)
            ·
              refine ⟨15421953744061393761016355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10281302496040929174010903 15421953744061393761016355)
              ·
                refine ⟨23132930616092090641524533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15421953744061393761016355 23132930616092090641524533)
                ·
                  refine ⟨2168712245258633497642925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23132930616092090641524533 2168712245258633497642925)
                  ·
                    refine ⟨813267091971987561616097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2168712245258633497642925 813267091971987561616097)
                    ·
                      refine ⟨609950318978990671212073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813267091971987561616097 609950318978990671212073)
                      ·
                        rfl

theorem cell23_1187874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_1187874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187874 prefixEnd_1187874 := by exact prefixLift 1187874
  have htrace : WordTrace (prefixWord ++ tailWord_1187874) baseStart_1187874 baseEnd_1187874 := by
    simpa [prefixWord, tailWord_1187874, baseEnd_1187874] using wordTrace_append hprefix tailTrace_1187874
  have hstable : (prefixWord ++ tailWord_1187874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187874).length < 2 ^ (prefixWord ++ tailWord_1187874).sum := by decide
  have hdescent : baseEnd_1187874 < baseStart_1187874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187904 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 1, 4, 2]
def baseStart_1187904 : Nat := 118140960795 + 1187904 * 2 ^ 59
def prefixEnd_1187904 : Nat := 4983230072969 + 3 ^ 40 * 1187904 * 2
def baseEnd_1187904 : Nat := 609965723398625553836935

theorem tailTrace_1187904 : CollatzResearch.WordTrace tailWord_1187904 prefixEnd_1187904 609965723398625553836935 := by
  unfold tailWord_1187904
  simp only [CollatzResearch.WordTrace]
  refine ⟨21663209144217080348189383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28884278858956107130919177 21663209144217080348189383)
  ·
    refine ⟨32494813716325620522284075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21663209144217080348189383 32494813716325620522284075)
    ·
      refine ⟨48742220574488430783426113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32494813716325620522284075 48742220574488430783426113)
      ·
        refine ⟨36556665430866323087569585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48742220574488430783426113 36556665430866323087569585)
        ·
          refine ⟨27417499073149742315677189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36556665430866323087569585 27417499073149742315677189)
          ·
            refine ⟨5140781076215576684189473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27417499073149742315677189 5140781076215576684189473)
            ·
              refine ⟨3855585807161682513142105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5140781076215576684189473 3855585807161682513142105)
              ·
                refine ⟨2891689355371261884856579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855585807161682513142105 2891689355371261884856579)
                ·
                  refine ⟨4337534033056892827284869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2891689355371261884856579 4337534033056892827284869)
                  ·
                    refine ⟨813287631198167405115913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4337534033056892827284869 813287631198167405115913)
                    ·
                      refine ⟨609965723398625553836935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813287631198167405115913 609965723398625553836935)
                      ·
                        rfl

theorem cell23_1187904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_1187904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187904 prefixEnd_1187904 := by exact prefixLift 1187904
  have htrace : WordTrace (prefixWord ++ tailWord_1187904) baseStart_1187904 baseEnd_1187904 := by
    simpa [prefixWord, tailWord_1187904, baseEnd_1187904] using wordTrace_append hprefix tailTrace_1187904
  have hstable : (prefixWord ++ tailWord_1187904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187904).length < 2 ^ (prefixWord ++ tailWord_1187904).sum := by decide
  have hdescent : baseEnd_1187904 < baseStart_1187904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187961 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 5]
def baseStart_1187961 : Nat := 118140960795 + 1187961 * 2 ^ 59
def prefixEnd_1187961 : Nat := 4983230072969 + 3 ^ 40 * 1187961 * 2
def baseEnd_1187961 : Nat := 67777221310659092313797

theorem tailTrace_1187961 : CollatzResearch.WordTrace tailWord_1187961 prefixEnd_1187961 67777221310659092313797 := by
  unfold tailWord_1187961
  simp only [CollatzResearch.WordTrace]
  refine ⟨43328497249227659431203737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28885664832818439620802491 43328497249227659431203737)
  ·
    refine ⟨32496372936920744573402803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43328497249227659431203737 32496372936920744573402803)
    ·
      refine ⟨48744559405381116860104205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32496372936920744573402803 48744559405381116860104205)
      ·
        refine ⟨18279209777017918822539077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48744559405381116860104205 18279209777017918822539077)
        ·
          refine ⟨3427351833190859779226077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18279209777017918822539077 3427351833190859779226077)
          ·
            refine ⟨1285256937446572417209779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3427351833190859779226077 1285256937446572417209779)
            ·
              refine ⟨1927885406169858625814669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285256937446572417209779 1927885406169858625814669)
              ·
                refine ⟨722957027313696984680501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1927885406169858625814669 722957027313696984680501)
                ·
                  refine ⟨67777221310659092313797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 722957027313696984680501 67777221310659092313797)
                  ·
                    rfl

theorem cell23_1187961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 5].length) (baseStart_1187961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1187961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1187961 prefixEnd_1187961 := by exact prefixLift 1187961
  have htrace : WordTrace (prefixWord ++ tailWord_1187961) baseStart_1187961 baseEnd_1187961 := by
    simpa [prefixWord, tailWord_1187961, baseEnd_1187961] using wordTrace_append hprefix tailTrace_1187961
  have hstable : (prefixWord ++ tailWord_1187961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187961).length < 2 ^ (prefixWord ++ tailWord_1187961).sum := by decide
  have hdescent : baseEnd_1187961 < baseStart_1187961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188047 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 5, 5]
def baseStart_1188047 : Nat := 118140960795 + 1188047 * 2 ^ 59
def prefixEnd_1188047 : Nat := 4983230072969 + 3 ^ 40 * 1188047 * 2
def baseEnd_1188047 : Nat := 203346383710739498116259

theorem tailTrace_1188047 : CollatzResearch.WordTrace tailWord_1188047 prefixEnd_1188047 203346383710739498116259 := by
  unfold tailWord_1188047
  simp only [CollatzResearch.WordTrace]
  refine ⟨43331633926916096118834395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28887755951277397412556263 43331633926916096118834395)
  ·
    refine ⟨64997450890374144178251593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43331633926916096118834395 64997450890374144178251593)
    ·
      refine ⟨48748088167780608133688695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64997450890374144178251593 48748088167780608133688695)
      ·
        refine ⟨73122132251670912200533043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48748088167780608133688695 73122132251670912200533043)
        ·
          refine ⟨109683198377506368300799565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73122132251670912200533043 109683198377506368300799565)
          ·
            refine ⟨41131199391564888112799837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109683198377506368300799565 41131199391564888112799837)
            ·
              refine ⟨15424199771836833042299939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41131199391564888112799837 15424199771836833042299939)
              ·
                refine ⟨23136299657755249563449909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15424199771836833042299939 23136299657755249563449909)
                ·
                  refine ⟨2169028092914554646573429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23136299657755249563449909 2169028092914554646573429)
                  ·
                    refine ⟨203346383710739498116259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2169028092914554646573429 203346383710739498116259)
                    ·
                      rfl

theorem cell23_1188047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_1188047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188047 prefixEnd_1188047 := by exact prefixLift 1188047
  have htrace : WordTrace (prefixWord ++ tailWord_1188047) baseStart_1188047 baseEnd_1188047 := by
    simpa [prefixWord, tailWord_1188047, baseEnd_1188047] using wordTrace_append hprefix tailTrace_1188047
  have hstable : (prefixWord ++ tailWord_1188047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188047).length < 2 ^ (prefixWord ++ tailWord_1188047).sum := by decide
  have hdescent : baseEnd_1188047 < baseStart_1188047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188064 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 1, 5]
def baseStart_1188064 : Nat := 118140960795 + 1188064 * 2 ^ 59
def prefixEnd_1188064 : Nat := 4983230072969 + 3 ^ 40 * 1188064 * 2
def baseEnd_1188064 : Nat := 203349293434448309278733

theorem tailTrace_1188064 : CollatzResearch.WordTrace tailWord_1188064 prefixEnd_1188064 203349293434448309278733 := by
  unfold tailWord_1188064
  simp only [CollatzResearch.WordTrace]
  refine ⟨21666126983927254011101623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28888169311903005348135497 21666126983927254011101623)
  ·
    refine ⟨32499190475890881016652435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21666126983927254011101623 32499190475890881016652435)
    ·
      refine ⟨48748785713836321524978653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32499190475890881016652435 48748785713836321524978653)
      ·
        refine ⟨18280794642688620571866995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48748785713836321524978653 18280794642688620571866995)
        ·
          refine ⟨27421191964032930857800493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18280794642688620571866995 27421191964032930857800493)
          ·
            refine ⟨10282946986512349071675185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27421191964032930857800493 10282946986512349071675185)
            ·
              refine ⟨7712210239884261803756389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10282946986512349071675185 7712210239884261803756389)
              ·
                refine ⟨1446039419978299088204323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7712210239884261803756389 1446039419978299088204323)
                ·
                  refine ⟨2169059129967448632306485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446039419978299088204323 2169059129967448632306485)
                  ·
                    refine ⟨203349293434448309278733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2169059129967448632306485 203349293434448309278733)
                    ·
                      rfl

theorem cell23_1188064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_1188064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188064 prefixEnd_1188064 := by exact prefixLift 1188064
  have htrace : WordTrace (prefixWord ++ tailWord_1188064) baseStart_1188064 baseEnd_1188064 := by
    simpa [prefixWord, tailWord_1188064, baseEnd_1188064] using wordTrace_append hprefix tailTrace_1188064
  have hstable : (prefixWord ++ tailWord_1188064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188064).length < 2 ^ (prefixWord ++ tailWord_1188064).sum := by decide
  have hdescent : baseEnd_1188064 < baseStart_1188064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188081 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 1, 5]
def baseStart_1188081 : Nat := 118140960795 + 1188081 * 2 ^ 59
def prefixEnd_1188081 : Nat := 4983230072969 + 3 ^ 40 * 1188081 * 2
def baseEnd_1188081 : Nat := 203352203158157120441207

theorem tailTrace_1188081 : CollatzResearch.WordTrace tailWord_1188081 prefixEnd_1188081 203352203158157120441207 := by
  unfold tailWord_1188081
  simp only [CollatzResearch.WordTrace]
  refine ⟨43332874008792919925572097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28888582672528613283714731 43332874008792919925572097)
  ·
    refine ⟨32499655506594689944179073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43332874008792919925572097 32499655506594689944179073)
    ·
      refine ⟨24374741629946017458134305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32499655506594689944179073 24374741629946017458134305)
      ·
        refine ⟨18281056222459513093600729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24374741629946017458134305 18281056222459513093600729)
        ·
          refine ⟨13710792166844634820200547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18281056222459513093600729 13710792166844634820200547)
          ·
            refine ⟨20566188250266952230300821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13710792166844634820200547 20566188250266952230300821)
            ·
              refine ⟨964040074231263385795351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20566188250266952230300821 964040074231263385795351)
              ·
                refine ⟨1446060111346895078693027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964040074231263385795351 1446060111346895078693027)
                ·
                  refine ⟨2169090167020342618039541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446060111346895078693027 2169090167020342618039541)
                  ·
                    refine ⟨203352203158157120441207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2169090167020342618039541 203352203158157120441207)
                    ·
                      rfl

theorem cell23_1188081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_1188081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188081 prefixEnd_1188081 := by exact prefixLift 1188081
  have htrace : WordTrace (prefixWord ++ tailWord_1188081) baseStart_1188081 baseEnd_1188081 := by
    simpa [prefixWord, tailWord_1188081, baseEnd_1188081] using wordTrace_append hprefix tailTrace_1188081
  have hstable : (prefixWord ++ tailWord_1188081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188081).length < 2 ^ (prefixWord ++ tailWord_1188081).sum := by decide
  have hdescent : baseEnd_1188081 < baseStart_1188081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188104 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1188104 : Nat := 118140960795 + 1188104 * 2 ^ 59
def prefixEnd_1188104 : Nat := 4983230072969 + 3 ^ 40 * 1188104 * 2
def baseEnd_1188104 : Nat := 610068419529524771336015

theorem tailTrace_1188104 : CollatzResearch.WordTrace tailWord_1188104 prefixEnd_1188104 610068419529524771336015 := by
  unfold tailWord_1188104
  simp only [CollatzResearch.WordTrace]
  refine ⟨21666856443854797426829683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28889141925139729902439577 21666856443854797426829683)
  ·
    refine ⟨32500284665782196140244525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21666856443854797426829683 32500284665782196140244525)
    ·
      refine ⟨12187606749668323552591697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32500284665782196140244525 12187606749668323552591697)
      ·
        refine ⟨9140705062251242664443773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12187606749668323552591697 9140705062251242664443773)
        ·
          refine ⟨3427764398344215999166415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9140705062251242664443773 3427764398344215999166415)
          ·
            refine ⟨5141646597516323998749623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427764398344215999166415 5141646597516323998749623)
            ·
              refine ⟨7712469896274485998124435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141646597516323998749623 7712469896274485998124435)
              ·
                refine ⟨11568704844411728997186653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7712469896274485998124435 11568704844411728997186653)
                ·
                  refine ⟨4338264316654398373944995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11568704844411728997186653 4338264316654398373944995)
                  ·
                    refine ⟨6507396474981597560917493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4338264316654398373944995 6507396474981597560917493)
                    ·
                      refine ⟨610068419529524771336015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6507396474981597560917493 610068419529524771336015)
                      ·
                        rfl

theorem cell23_1188104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1188104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188104 prefixEnd_1188104 := by exact prefixLift 1188104
  have htrace : WordTrace (prefixWord ++ tailWord_1188104) baseStart_1188104 baseEnd_1188104 := by
    simpa [prefixWord, tailWord_1188104, baseEnd_1188104] using wordTrace_append hprefix tailTrace_1188104
  have hstable : (prefixWord ++ tailWord_1188104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188104).length < 2 ^ (prefixWord ++ tailWord_1188104).sum := by decide
  have hdescent : baseEnd_1188104 < baseStart_1188104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188107 : List Nat := [1, 1, 1, 1, 5, 2, 2, 10]
def baseStart_1188107 : Nat := 118140960795 + 1188107 * 2 ^ 59
def prefixEnd_1188107 : Nat := 4983230072969 + 3 ^ 40 * 1188107 * 2
def baseEnd_1188107 : Nat := 22595183702647713318463

theorem tailTrace_1188107 : CollatzResearch.WordTrace tailWord_1188107 prefixEnd_1188107 22595183702647713318463 := by
  unfold tailWord_1188107
  simp only [CollatzResearch.WordTrace]
  refine ⟨43333822306698726366018575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28889214871132484244012383 43333822306698726366018575)
  ·
    refine ⟨65000733460048089549027863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43333822306698726366018575 65000733460048089549027863)
    ·
      refine ⟨97501100190072134323541795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65000733460048089549027863 97501100190072134323541795)
      ·
        refine ⟨146251650285108201485312693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97501100190072134323541795 146251650285108201485312693)
        ·
          refine ⟨13711092214228893889248065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146251650285108201485312693 13711092214228893889248065)
          ·
            refine ⟨10283319160671670416936049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13711092214228893889248065 10283319160671670416936049)
            ·
              refine ⟨7712489370503752812702037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10283319160671670416936049 7712489370503752812702037)
              ·
                refine ⟨22595183702647713318463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7712489370503752812702037 22595183702647713318463)
                ·
                  rfl

theorem cell23_1188107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 10].length) (baseStart_1188107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188107 prefixEnd_1188107 := by exact prefixLift 1188107
  have htrace : WordTrace (prefixWord ++ tailWord_1188107) baseStart_1188107 baseEnd_1188107 := by
    simpa [prefixWord, tailWord_1188107, baseEnd_1188107] using wordTrace_append hprefix tailTrace_1188107
  have hstable : (prefixWord ++ tailWord_1188107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188107).length < 2 ^ (prefixWord ++ tailWord_1188107).sum := by decide
  have hdescent : baseEnd_1188107 < baseStart_1188107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188138 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1188138 : Nat := 118140960795 + 1188138 * 2 ^ 59
def prefixEnd_1188138 : Nat := 4983230072969 + 3 ^ 40 * 1188138 * 2
def baseEnd_1188138 : Nat := 610085877871777638310859

theorem tailTrace_1188138 : CollatzResearch.WordTrace tailWord_1188138 prefixEnd_1188138 610085877871777638310859 := by
  unfold tailWord_1188138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10833738242396604665099267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28889968646390945773598045 10833738242396604665099267)
  ·
    refine ⟨16250607363594906997648901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10833738242396604665099267 16250607363594906997648901)
    ·
      refine ⟨3046988880674045062059169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16250607363594906997648901 3046988880674045062059169)
      ·
        refine ⟨2285241660505533796544377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3046988880674045062059169 2285241660505533796544377)
        ·
          refine ⟨1713931245379150347408283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2285241660505533796544377 1713931245379150347408283)
          ·
            refine ⟨2570896868068725521112425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713931245379150347408283 2570896868068725521112425)
            ·
              refine ⟨1928172651051544140834319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570896868068725521112425 1928172651051544140834319)
              ·
                refine ⟨2892258976577316211251479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928172651051544140834319 2892258976577316211251479)
                ·
                  refine ⟨4338388464865974316877219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892258976577316211251479 4338388464865974316877219)
                  ·
                    refine ⟨6507582697298961475315829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4338388464865974316877219 6507582697298961475315829)
                    ·
                      refine ⟨610085877871777638310859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6507582697298961475315829 610085877871777638310859)
                      ·
                        rfl

theorem cell23_1188138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1188138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188138 prefixEnd_1188138 := by exact prefixLift 1188138
  have htrace : WordTrace (prefixWord ++ tailWord_1188138) baseStart_1188138 baseEnd_1188138 := by
    simpa [prefixWord, tailWord_1188138, baseEnd_1188138] using wordTrace_append hprefix tailTrace_1188138
  have hstable : (prefixWord ++ tailWord_1188138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188138).length < 2 ^ (prefixWord ++ tailWord_1188138).sum := by decide
  have hdescent : baseEnd_1188138 < baseStart_1188138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188174 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_1188174 : Nat := 118140960795 + 1188174 * 2 ^ 59
def prefixEnd_1188174 : Nat := 4983230072969 + 3 ^ 40 * 1188174 * 2
def baseEnd_1188174 : Nat := 610104363175339497460693

theorem tailTrace_1188174 : CollatzResearch.WordTrace tailWord_1188174 prefixEnd_1188174 610104363175339497460693 := by
  unfold tailWord_1188174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417033249681999601088447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28890843998303997872471717 5417033249681999601088447)
  ·
    refine ⟨8125549874522999401632671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5417033249681999601088447 8125549874522999401632671)
    ·
      refine ⟨12188324811784499102449007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8125549874522999401632671 12188324811784499102449007)
      ·
        refine ⟨18282487217676748653673511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12188324811784499102449007 18282487217676748653673511)
        ·
          refine ⟨27423730826515122980510267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18282487217676748653673511 27423730826515122980510267)
          ·
            refine ⟨41135596239772684470765401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27423730826515122980510267 41135596239772684470765401)
            ·
              refine ⟨30851697179829513353074051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41135596239772684470765401 30851697179829513353074051)
              ·
                refine ⟨46277545769744270029611077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30851697179829513353074051 46277545769744270029611077)
                ·
                  refine ⟨8677039831827050630552077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46277545769744270029611077 8677039831827050630552077)
                  ·
                    refine ⟨3253889936935143986457029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8677039831827050630552077 3253889936935143986457029)
                    ·
                      refine ⟨610104363175339497460693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3253889936935143986457029 610104363175339497460693)
                      ·
                        rfl

theorem cell23_1188174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_1188174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188174 prefixEnd_1188174 := by exact prefixLift 1188174
  have htrace : WordTrace (prefixWord ++ tailWord_1188174) baseStart_1188174 baseEnd_1188174 := by
    simpa [prefixWord, tailWord_1188174, baseEnd_1188174] using wordTrace_append hprefix tailTrace_1188174
  have hstable : (prefixWord ++ tailWord_1188174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188174).length < 2 ^ (prefixWord ++ tailWord_1188174).sum := by decide
  have hdescent : baseEnd_1188174 < baseStart_1188174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188191 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 3, 4, 2]
def baseStart_1188191 : Nat := 118140960795 + 1188191 * 2 ^ 59
def prefixEnd_1188191 : Nat := 4983230072969 + 3 ^ 40 * 1188191 * 2
def baseEnd_1188191 : Nat := 610113092346465930948115

theorem tailTrace_1188191 : CollatzResearch.WordTrace tailWord_1188191 prefixEnd_1188191 610113092346465930948115 := by
  unfold tailWord_1188191
  simp only [CollatzResearch.WordTrace]
  refine ⟨43336886038394408712076427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28891257358929605808050951 43336886038394408712076427)
  ·
    refine ⟨65005329057591613068114641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43336886038394408712076427 65005329057591613068114641)
    ·
      refine ⟨48753996793193709801085981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65005329057591613068114641 48753996793193709801085981)
      ·
        refine ⟨18282748797447641175407243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48753996793193709801085981 18282748797447641175407243)
        ·
          refine ⟨27424123196171461763110865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18282748797447641175407243 27424123196171461763110865)
          ·
            refine ⟨20568092397128596322333149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27424123196171461763110865 20568092397128596322333149)
            ·
              refine ⟨7713034648923223620874931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20568092397128596322333149 7713034648923223620874931)
              ·
                refine ⟨11569551973384835431312397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7713034648923223620874931 11569551973384835431312397)
                ·
                  refine ⟨4338581990019313286742149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11569551973384835431312397 4338581990019313286742149)
                  ·
                    refine ⟨813484123128621241264153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338581990019313286742149 813484123128621241264153)
                    ·
                      refine ⟨610113092346465930948115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813484123128621241264153 610113092346465930948115)
                      ·
                        rfl

theorem cell23_1188191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_1188191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188191 prefixEnd_1188191 := by exact prefixLift 1188191
  have htrace : WordTrace (prefixWord ++ tailWord_1188191) baseStart_1188191 baseEnd_1188191 := by
    simpa [prefixWord, tailWord_1188191, baseEnd_1188191] using wordTrace_append hprefix tailTrace_1188191
  have hstable : (prefixWord ++ tailWord_1188191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188191).length < 2 ^ (prefixWord ++ tailWord_1188191).sum := by decide
  have hdescent : baseEnd_1188191 < baseStart_1188191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188195 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 1, 3, 2]
def baseStart_1188195 : Nat := 118140960795 + 1188195 * 2 ^ 59
def prefixEnd_1188195 : Nat := 4983230072969 + 3 ^ 40 * 1188195 * 2
def baseEnd_1188195 : Nat := 610115146269083915298097

theorem tailTrace_1188195 : CollatzResearch.WordTrace tailWord_1188195 prefixEnd_1188195 610115146269083915298097 := by
  unfold tailWord_1188195
  simp only [CollatzResearch.WordTrace]
  refine ⟨43337031930379917395222039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28891354620253278263481359 43337031930379917395222039)
  ·
    refine ⟨65005547895569876092833059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43337031930379917395222039 65005547895569876092833059)
    ·
      refine ⟨97508321843354814139249589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65005547895569876092833059 97508321843354814139249589)
      ·
        refine ⟨9141405172814513825554649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97508321843354814139249589 9141405172814513825554649)
        ·
          refine ⟨6856053879610885369165987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9141405172814513825554649 6856053879610885369165987)
          ·
            refine ⟨10284080819416328053748981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856053879610885369165987 10284080819416328053748981)
            ·
              refine ⟨964132576820280755038967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10284080819416328053748981 964132576820280755038967)
              ·
                refine ⟨1446198865230421132558451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964132576820280755038967 1446198865230421132558451)
                ·
                  refine ⟨2169298297845631698837677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446198865230421132558451 2169298297845631698837677)
                  ·
                    refine ⟨813486861692111887064129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169298297845631698837677 813486861692111887064129)
                    ·
                      refine ⟨610115146269083915298097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813486861692111887064129 610115146269083915298097)
                      ·
                        rfl

theorem cell23_1188195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_1188195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188195 prefixEnd_1188195 := by exact prefixLift 1188195
  have htrace : WordTrace (prefixWord ++ tailWord_1188195) baseStart_1188195 baseEnd_1188195 := by
    simpa [prefixWord, tailWord_1188195, baseEnd_1188195] using wordTrace_append hprefix tailTrace_1188195
  have hstable : (prefixWord ++ tailWord_1188195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188195).length < 2 ^ (prefixWord ++ tailWord_1188195).sum := by decide
  have hdescent : baseEnd_1188195 < baseStart_1188195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188221 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1188221 : Nat := 118140960795 + 1188221 * 2 ^ 59
def prefixEnd_1188221 : Nat := 4983230072969 + 3 ^ 40 * 1188221 * 2
def baseEnd_1188221 : Nat := 610128496766100813572977

theorem tailTrace_1188221 : CollatzResearch.WordTrace tailWord_1188221 prefixEnd_1188221 610128496766100813572977 := by
  unfold tailWord_1188221
  simp only [CollatzResearch.WordTrace]
  refine ⟨43337980228285723835668517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28891986818857149223779011 43337980228285723835668517)
  ·
    refine ⟨8125871292803573219187847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43337980228285723835668517 8125871292803573219187847)
    ·
      refine ⟨12188806939205359828781771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8125871292803573219187847 12188806939205359828781771)
      ·
        refine ⟨18283210408808039743172657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12188806939205359828781771 18283210408808039743172657)
        ·
          refine ⟨13712407806606029807379493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18283210408808039743172657 13712407806606029807379493)
          ·
            refine ⟨2571076463738630588883655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13712407806606029807379493 2571076463738630588883655)
            ·
              refine ⟨3856614695607945883325483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571076463738630588883655 3856614695607945883325483)
              ·
                refine ⟨5784922043411918824988225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3856614695607945883325483 5784922043411918824988225)
                ·
                  refine ⟨4338691532558939118741169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5784922043411918824988225 4338691532558939118741169)
                  ·
                    refine ⟨3254018649419204339055877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4338691532558939118741169 3254018649419204339055877)
                    ·
                      refine ⟨610128496766100813572977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3254018649419204339055877 610128496766100813572977)
                      ·
                        rfl

theorem cell23_1188221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1188221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188221 prefixEnd_1188221 := by exact prefixLift 1188221
  have htrace : WordTrace (prefixWord ++ tailWord_1188221) baseStart_1188221 baseEnd_1188221 := by
    simpa [prefixWord, tailWord_1188221, baseEnd_1188221] using wordTrace_append hprefix tailTrace_1188221
  have hstable : (prefixWord ++ tailWord_1188221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188221).length < 2 ^ (prefixWord ++ tailWord_1188221).sum := by decide
  have hdescent : baseEnd_1188221 < baseStart_1188221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188225 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_1188225 : Nat := 118140960795 + 1188225 * 2 ^ 59
def prefixEnd_1188225 : Nat := 4983230072969 + 3 ^ 40 * 1188225 * 2
def baseEnd_1188225 : Nat := 610130550688718797922959

theorem tailTrace_1188225 : CollatzResearch.WordTrace tailWord_1188225 prefixEnd_1188225 610130550688718797922959 := by
  unfold tailWord_1188225
  simp only [CollatzResearch.WordTrace]
  refine ⟨43338126120271232518814129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28892084080180821679209419 43338126120271232518814129)
  ·
    refine ⟨32503594590203424389110597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43338126120271232518814129 32503594590203424389110597)
    ·
      refine ⟨6094423985663142072958237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32503594590203424389110597 6094423985663142072958237)
      ·
        refine ⟨2285408994623678277359339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6094423985663142072958237 2285408994623678277359339)
        ·
          refine ⟨3428113491935517416039009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285408994623678277359339 3428113491935517416039009)
          ·
            refine ⟨2571085118951638062029257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3428113491935517416039009 2571085118951638062029257)
            ·
              refine ⟨1928313839213728546521943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571085118951638062029257 1928313839213728546521943)
              ·
                refine ⟨2892470758820592819782915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928313839213728546521943 2892470758820592819782915)
                ·
                  refine ⟨4338706138230889229674373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892470758820592819782915 4338706138230889229674373)
                  ·
                    refine ⟨813507400918291730563945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338706138230889229674373 813507400918291730563945)
                    ·
                      refine ⟨610130550688718797922959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813507400918291730563945 610130550688718797922959)
                      ·
                        rfl

theorem cell23_1188225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_1188225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188225 prefixEnd_1188225 := by exact prefixLift 1188225
  have htrace : WordTrace (prefixWord ++ tailWord_1188225) baseStart_1188225 baseEnd_1188225 := by
    simpa [prefixWord, tailWord_1188225, baseEnd_1188225] using wordTrace_append hprefix tailTrace_1188225
  have hstable : (prefixWord ++ tailWord_1188225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188225).length < 2 ^ (prefixWord ++ tailWord_1188225).sum := by decide
  have hdescent : baseEnd_1188225 < baseStart_1188225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188246 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1188246 : Nat := 118140960795 + 1188246 * 2 ^ 59
def prefixEnd_1188246 : Nat := 4983230072969 + 3 ^ 40 * 1188246 * 2
def baseEnd_1188246 : Nat := 610141333782463215760363

theorem tailTrace_1188246 : CollatzResearch.WordTrace tailWord_1188246 prefixEnd_1188246 610141333782463215760363 := by
  unfold tailWord_1188246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708680753324697069083037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28892594702130102070219061 2708680753324697069083037)
  ·
    refine ⟨1015755282496761400906139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2708680753324697069083037 1015755282496761400906139)
    ·
      refine ⟨1523632923745142101359209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015755282496761400906139 1523632923745142101359209)
      ·
        refine ⟨1142724692808856576019407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1523632923745142101359209 1142724692808856576019407)
        ·
          refine ⟨1714087039213284864029111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142724692808856576019407 1714087039213284864029111)
          ·
            refine ⟨2571130558819927296043667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714087039213284864029111 2571130558819927296043667)
            ·
              refine ⟨3856695838229890944065501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571130558819927296043667 3856695838229890944065501)
              ·
                refine ⟨1446260939336209104024563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3856695838229890944065501 1446260939336209104024563)
                ·
                  refine ⟨2169391409004313656036845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446260939336209104024563 2169391409004313656036845)
                  ·
                    refine ⟨813521778376617621013817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2169391409004313656036845 813521778376617621013817)
                    ·
                      refine ⟨610141333782463215760363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813521778376617621013817 610141333782463215760363)
                      ·
                        rfl

theorem cell23_1188246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1188246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188246 prefixEnd_1188246 := by exact prefixLift 1188246
  have htrace : WordTrace (prefixWord ++ tailWord_1188246) baseStart_1188246 baseEnd_1188246 := by
    simpa [prefixWord, tailWord_1188246, baseEnd_1188246] using wordTrace_append hprefix tailTrace_1188246
  have hstable : (prefixWord ++ tailWord_1188246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188246).length < 2 ^ (prefixWord ++ tailWord_1188246).sum := by decide
  have hdescent : baseEnd_1188246 < baseStart_1188246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188248 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 5]
def baseStart_1188248 : Nat := 118140960795 + 1188248 * 2 ^ 59
def prefixEnd_1188248 : Nat := 4983230072969 + 3 ^ 40 * 1188248 * 2
def baseEnd_1188248 : Nat := 67793595638196911992817

theorem tailTrace_1188248 : CollatzResearch.WordTrace tailWord_1188248 prefixEnd_1188248 67793595638196911992817 := by
  unfold tailWord_1188248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669482499593953723450699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28892643332791938297934265 21669482499593953723450699)
  ·
    refine ⟨32504223749390930585176049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21669482499593953723450699 32504223749390930585176049)
    ·
      refine ⟨24378167812043197938882037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32504223749390930585176049 24378167812043197938882037)
      ·
        refine ⟨2285453232379049806770191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24378167812043197938882037 2285453232379049806770191)
        ·
          refine ⟨3428179848568574710155287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285453232379049806770191 3428179848568574710155287)
          ·
            refine ⟨5142269772852862065232931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428179848568574710155287 5142269772852862065232931)
            ·
              refine ⟨7713404659279293097849397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142269772852862065232931 7713404659279293097849397)
              ·
                refine ⟨723131686807433727923381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7713404659279293097849397 723131686807433727923381)
                ·
                  refine ⟨67793595638196911992817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723131686807433727923381 67793595638196911992817)
                  ·
                    rfl

theorem cell23_1188248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 5].length) (baseStart_1188248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188248 prefixEnd_1188248 := by exact prefixLift 1188248
  have htrace : WordTrace (prefixWord ++ tailWord_1188248) baseStart_1188248 baseEnd_1188248 := by
    simpa [prefixWord, tailWord_1188248, baseEnd_1188248] using wordTrace_append hprefix tailTrace_1188248
  have hstable : (prefixWord ++ tailWord_1188248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188248).length < 2 ^ (prefixWord ++ tailWord_1188248).sum := by decide
  have hdescent : baseEnd_1188248 < baseStart_1188248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188276 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1188276 : Nat := 118140960795 + 1188276 * 2 ^ 59
def prefixEnd_1188276 : Nat := 4983230072969 + 3 ^ 40 * 1188276 * 2
def baseEnd_1188276 : Nat := 610156738202098098385225

theorem tailTrace_1188276 : CollatzResearch.WordTrace tailWord_1188276 prefixEnd_1188276 610156738202098098385225 := by
  unfold tailWord_1188276
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669993121543234114460341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28893324162057645485947121 21669993121543234114460341)
  ·
    refine ⟨2031561855144678198230657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21669993121543234114460341 2031561855144678198230657)
    ·
      refine ⟨1523671391358508648672993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2031561855144678198230657 1523671391358508648672993)
      ·
        refine ⟨1142753543518881486504745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1523671391358508648672993 1142753543518881486504745)
        ·
          refine ⟨857065157639161114878559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142753543518881486504745 857065157639161114878559)
          ·
            refine ⟨1285597736458741672317839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857065157639161114878559 1285597736458741672317839)
            ·
              refine ⟨1928396604688112508476759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285597736458741672317839 1928396604688112508476759)
              ·
                refine ⟨2892594907032168762715139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928396604688112508476759 2892594907032168762715139)
                ·
                  refine ⟨4338892360548253144072709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2892594907032168762715139 4338892360548253144072709)
                  ·
                    refine ⟨813542317602797464513633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4338892360548253144072709 813542317602797464513633)
                    ·
                      refine ⟨610156738202098098385225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813542317602797464513633 610156738202098098385225)
                      ·
                        rfl

theorem cell23_1188276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1188276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188276 prefixEnd_1188276 := by exact prefixLift 1188276
  have htrace : WordTrace (prefixWord ++ tailWord_1188276) baseStart_1188276 baseEnd_1188276 := by
    simpa [prefixWord, tailWord_1188276, baseEnd_1188276] using wordTrace_append hprefix tailTrace_1188276
  have hstable : (prefixWord ++ tailWord_1188276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188276).length < 2 ^ (prefixWord ++ tailWord_1188276).sum := by decide
  have hdescent : baseEnd_1188276 < baseStart_1188276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188281 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1188281 : Nat := 118140960795 + 1188281 * 2 ^ 59
def prefixEnd_1188281 : Nat := 4983230072969 + 3 ^ 40 * 1188281 * 2
def baseEnd_1188281 : Nat := 610159305605370578822701

theorem tailTrace_1188281 : CollatzResearch.WordTrace tailWord_1188281 prefixEnd_1188281 610159305605370578822701 := by
  unfold tailWord_1188281
  simp only [CollatzResearch.WordTrace]
  refine ⟨43340168608068354082852697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28893445738712236055235131 43340168608068354082852697)
  ·
    refine ⟨32505126456051265562139523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43340168608068354082852697 32505126456051265562139523)
    ·
      refine ⟨48757689684076898343209285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32505126456051265562139523 48757689684076898343209285)
      ·
        refine ⟨9142066815764418439351741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48757689684076898343209285 9142066815764418439351741)
        ·
          refine ⟨3428275055911656914756903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9142066815764418439351741 3428275055911656914756903)
          ·
            refine ⟨5142412583867485372135355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428275055911656914756903 5142412583867485372135355)
            ·
              refine ⟨7713618875801228058203033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5142412583867485372135355 7713618875801228058203033)
              ·
                refine ⟨5785214156850921043652275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7713618875801228058203033 5785214156850921043652275)
                ·
                  refine ⟨8677821235276381565478413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785214156850921043652275 8677821235276381565478413)
                  ·
                    refine ⟨3254182963228643087054405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8677821235276381565478413 3254182963228643087054405)
                    ·
                      refine ⟨610159305605370578822701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3254182963228643087054405 610159305605370578822701)
                      ·
                        rfl

theorem cell23_1188281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1188281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188281 prefixEnd_1188281 := by exact prefixLift 1188281
  have htrace : WordTrace (prefixWord ++ tailWord_1188281) baseStart_1188281 baseEnd_1188281 := by
    simpa [prefixWord, tailWord_1188281, baseEnd_1188281] using wordTrace_append hprefix tailTrace_1188281
  have hstable : (prefixWord ++ tailWord_1188281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188281).length < 2 ^ (prefixWord ++ tailWord_1188281).sum := by decide
  have hdescent : baseEnd_1188281 < baseStart_1188281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188321 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 6]
def baseStart_1188321 : Nat := 118140960795 + 1188321 * 2 ^ 59
def prefixEnd_1188321 : Nat := 4983230072969 + 3 ^ 40 * 1188321 * 2
def baseEnd_1188321 : Nat := 67797760536838935813613

theorem tailTrace_1188321 : CollatzResearch.WordTrace tailWord_1188321 prefixEnd_1188321 67797760536838935813613 := by
  unfold tailWord_1188321
  simp only [CollatzResearch.WordTrace]
  refine ⟨43341627527923440914308817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28894418351948960609539211 43341627527923440914308817)
  ·
    refine ⟨32506220645942580685731613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43341627527923440914308817 32506220645942580685731613)
    ·
      refine ⟨12189832742228467757149355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32506220645942580685731613 12189832742228467757149355)
      ·
        refine ⟨18284749113342701635724033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12189832742228467757149355 18284749113342701635724033)
        ·
          refine ⟨13713561835007026226793025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18284749113342701635724033 13713561835007026226793025)
          ·
            refine ⟨10285171376255269670094769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13713561835007026226793025 10285171376255269670094769)
            ·
              refine ⟨7713878532191452252571077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10285171376255269670094769 7713878532191452252571077)
              ·
                refine ⟨1446352224785897297357077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7713878532191452252571077 1446352224785897297357077)
                ·
                  refine ⟨67797760536838935813613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1446352224785897297357077 67797760536838935813613)
                  ·
                    rfl

theorem cell23_1188321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 6].length) (baseStart_1188321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188321 prefixEnd_1188321 := by exact prefixLift 1188321
  have htrace : WordTrace (prefixWord ++ tailWord_1188321) baseStart_1188321 baseEnd_1188321 := by
    simpa [prefixWord, tailWord_1188321, baseEnd_1188321] using wordTrace_append hprefix tailTrace_1188321
  have hstable : (prefixWord ++ tailWord_1188321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188321).length < 2 ^ (prefixWord ++ tailWord_1188321).sum := by decide
  have hdescent : baseEnd_1188321 < baseStart_1188321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188348 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_1188348 : Nat := 118140960795 + 1188348 * 2 ^ 59
def prefixEnd_1188348 : Nat := 4983230072969 + 3 ^ 40 * 1188348 * 2
def baseEnd_1188348 : Nat := 610193708809221816684893

theorem tailTrace_1188348 : CollatzResearch.WordTrace tailWord_1188348 prefixEnd_1188348 610193708809221816684893 := by
  unfold tailWord_1188348
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671306149412812262770849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28895074865883749683694465 21671306149412812262770849)
  ·
    refine ⟨16253479612059609197078137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21671306149412812262770849 16253479612059609197078137)
    ·
      refine ⟨12190109709044706897808603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16253479612059609197078137 12190109709044706897808603)
      ·
        refine ⟨18285164563567060346712905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12190109709044706897808603 18285164563567060346712905)
        ·
          refine ⟨13713873422675295260034679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18285164563567060346712905 13713873422675295260034679)
          ·
            refine ⟨20570810134012942890052019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13713873422675295260034679 20570810134012942890052019)
            ·
              refine ⟨30856215201019414335078029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20570810134012942890052019 30856215201019414335078029)
              ·
                refine ⟨11571080700382280375654261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30856215201019414335078029 11571080700382280375654261)
                ·
                  refine ⟨1084788815660838785217587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11571080700382280375654261 1084788815660838785217587)
                  ·
                    refine ⟨1627183223491258177826381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1084788815660838785217587 1627183223491258177826381)
                    ·
                      refine ⟨610193708809221816684893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1627183223491258177826381 610193708809221816684893)
                      ·
                        rfl

theorem cell23_1188348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_1188348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188348 prefixEnd_1188348 := by exact prefixLift 1188348
  have htrace : WordTrace (prefixWord ++ tailWord_1188348) baseStart_1188348 baseEnd_1188348 := by
    simpa [prefixWord, tailWord_1188348, baseEnd_1188348] using wordTrace_append hprefix tailTrace_1188348
  have hstable : (prefixWord ++ tailWord_1188348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188348).length < 2 ^ (prefixWord ++ tailWord_1188348).sum := by decide
  have hdescent : baseEnd_1188348 < baseStart_1188348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188351 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 3, 5]
def baseStart_1188351 : Nat := 118140960795 + 1188351 * 2 ^ 59
def prefixEnd_1188351 : Nat := 4983230072969 + 3 ^ 40 * 1188351 * 2
def baseEnd_1188351 : Nat := 203398416417061768315793

theorem tailTrace_1188351 : CollatzResearch.WordTrace tailWord_1188351 prefixEnd_1188351 203398416417061768315793 := by
  unfold tailWord_1188351
  simp only [CollatzResearch.WordTrace]
  refine ⟨43342721717814756037900907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28895147811876504025267271 43342721717814756037900907)
  ·
    refine ⟨65014082576722134056851361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43342721717814756037900907 65014082576722134056851361)
    ·
      refine ⟨48760561932541600542638521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65014082576722134056851361 48760561932541600542638521)
      ·
        refine ⟨36570421449406200406978891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48760561932541600542638521 36570421449406200406978891)
        ·
          refine ⟨54855632174109300610468337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36570421449406200406978891 54855632174109300610468337)
          ·
            refine ⟨41141724130581975457851253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54855632174109300610468337 41141724130581975457851253)
            ·
              refine ⟨3857036637242060199173555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41141724130581975457851253 3857036637242060199173555)
              ·
                refine ⟨5785554955863090298760333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857036637242060199173555 5785554955863090298760333)
                ·
                  refine ⟨2169583108448658862035125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5785554955863090298760333 2169583108448658862035125)
                  ·
                    refine ⟨203398416417061768315793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2169583108448658862035125 203398416417061768315793)
                    ·
                      rfl

theorem cell23_1188351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_1188351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188351 prefixEnd_1188351 := by exact prefixLift 1188351
  have htrace : WordTrace (prefixWord ++ tailWord_1188351) baseStart_1188351 baseEnd_1188351 := by
    simpa [prefixWord, tailWord_1188351, baseEnd_1188351] using wordTrace_append hprefix tailTrace_1188351
  have hstable : (prefixWord ++ tailWord_1188351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188351).length < 2 ^ (prefixWord ++ tailWord_1188351).sum := by decide
  have hdescent : baseEnd_1188351 < baseStart_1188351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188401 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1188401 : Nat := 118140960795 + 1188401 * 2 ^ 59
def prefixEnd_1188401 : Nat := 4983230072969 + 3 ^ 40 * 1188401 * 2
def baseEnd_1188401 : Nat := 610220923283910109322149

theorem tailTrace_1188401 : CollatzResearch.WordTrace tailWord_1188401 prefixEnd_1188401 610220923283910109322149 := by
  unfold tailWord_1188401
  simp only [CollatzResearch.WordTrace]
  refine ⟨43344545367633614577221057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28896363578422409718147371 43344545367633614577221057)
  ·
    refine ⟨32508409025725210932915793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43344545367633614577221057 32508409025725210932915793)
    ·
      refine ⟨24381306769293908199686845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32508409025725210932915793 24381306769293908199686845)
      ·
        refine ⟨9142990038485215574882567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24381306769293908199686845 9142990038485215574882567)
        ·
          refine ⟨13714485057727823362323851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9142990038485215574882567 13714485057727823362323851)
          ·
            refine ⟨20571727586591735043485777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13714485057727823362323851 20571727586591735043485777)
            ·
              refine ⟨15428795689943801282614333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20571727586591735043485777 15428795689943801282614333)
              ·
                refine ⟨5785798383728925480980375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15428795689943801282614333 5785798383728925480980375)
                ·
                  refine ⟨8678697575593388221470563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5785798383728925480980375 8678697575593388221470563)
                  ·
                    refine ⟨13018046363390082332205845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8678697575593388221470563 13018046363390082332205845)
                    ·
                      refine ⟨610220923283910109322149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13018046363390082332205845 610220923283910109322149)
                      ·
                        rfl

theorem cell23_1188401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1188401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188401 prefixEnd_1188401 := by exact prefixLift 1188401
  have htrace : WordTrace (prefixWord ++ tailWord_1188401) baseStart_1188401 baseEnd_1188401 := by
    simpa [prefixWord, tailWord_1188401, baseEnd_1188401] using wordTrace_append hprefix tailTrace_1188401
  have hstable : (prefixWord ++ tailWord_1188401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188401).length < 2 ^ (prefixWord ++ tailWord_1188401).sum := by decide
  have hdescent : baseEnd_1188401 < baseStart_1188401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188408 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_1188408 : Nat := 118140960795 + 1188408 * 2 ^ 59
def prefixEnd_1188408 : Nat := 4983230072969 + 3 ^ 40 * 1188408 * 2
def baseEnd_1188408 : Nat := 610224517648491581934617

theorem tailTrace_1188408 : CollatzResearch.WordTrace tailWord_1188408 prefixEnd_1188408 610224517648491581934617 := by
  unfold tailWord_1188408
  simp only [CollatzResearch.WordTrace]
  refine ⟨21672400339304127386362939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28896533785738836515150585 21672400339304127386362939)
  ·
    refine ⟨32508600508956191079544409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21672400339304127386362939 32508600508956191079544409)
    ·
      refine ⟨24381450381717143309658307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32508600508956191079544409 24381450381717143309658307)
      ·
        refine ⟨36572175572575714964487461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24381450381717143309658307 36572175572575714964487461)
        ·
          refine ⟨6857282919857946555841399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36572175572575714964487461 6857282919857946555841399)
          ·
            refine ⟨10285924379786919833762099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6857282919857946555841399 10285924379786919833762099)
            ·
              refine ⟨15428886569680379750643149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10285924379786919833762099 15428886569680379750643149)
              ·
                refine ⟨5785832463630142406491181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15428886569680379750643149 5785832463630142406491181)
                ·
                  refine ⟨2169687173861303402434193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5785832463630142406491181 2169687173861303402434193)
                  ·
                    refine ⟨1627265380395977551825645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2169687173861303402434193 1627265380395977551825645)
                    ·
                      refine ⟨610224517648491581934617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1627265380395977551825645 610224517648491581934617)
                      ·
                        rfl

theorem cell23_1188408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_1188408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188408 prefixEnd_1188408 := by exact prefixLift 1188408
  have htrace : WordTrace (prefixWord ++ tailWord_1188408) baseStart_1188408 baseEnd_1188408 := by
    simpa [prefixWord, tailWord_1188408, baseEnd_1188408] using wordTrace_append hprefix tailTrace_1188408
  have hstable : (prefixWord ++ tailWord_1188408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188408).length < 2 ^ (prefixWord ++ tailWord_1188408).sum := by decide
  have hdescent : baseEnd_1188408 < baseStart_1188408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188471 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 8]
def baseStart_1188471 : Nat := 118140960795 + 1188471 * 2 ^ 59
def prefixEnd_1188471 : Nat := 4983230072969 + 3 ^ 40 * 1188471 * 2
def baseEnd_1188471 : Nat := 203418955643241611815609

theorem tailTrace_1188471 : CollatzResearch.WordTrace tailWord_1188471 prefixEnd_1188471 203418955643241611815609 := by
  unfold tailWord_1188471
  simp only [CollatzResearch.WordTrace]
  refine ⟨43347098477380016532269267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28898065651586677688179511 43347098477380016532269267)
  ·
    refine ⟨65020647716070024798403901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43347098477380016532269267 65020647716070024798403901)
    ·
      refine ⟨24382742893526259299401463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65020647716070024798403901 24382742893526259299401463)
      ·
        refine ⟨36574114340289388949102195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24382742893526259299401463 36574114340289388949102195)
        ·
          refine ⟨54861171510434083423653293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36574114340289388949102195 54861171510434083423653293)
          ·
            refine ⟨20572939316412781283869985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54861171510434083423653293 20572939316412781283869985)
            ·
              refine ⟨15429704487309585962902489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20572939316412781283869985 15429704487309585962902489)
              ·
                refine ⟨11572278365482189472176867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15429704487309585962902489 11572278365482189472176867)
                ·
                  refine ⟨17358417548223284208265301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11572278365482189472176867 17358417548223284208265301)
                  ·
                    refine ⟨203418955643241611815609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17358417548223284208265301 203418955643241611815609)
                    ·
                      rfl

theorem cell23_1188471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_1188471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188471 prefixEnd_1188471 := by exact prefixLift 1188471
  have htrace : WordTrace (prefixWord ++ tailWord_1188471) baseStart_1188471 baseEnd_1188471 := by
    simpa [prefixWord, tailWord_1188471, baseEnd_1188471] using wordTrace_append hprefix tailTrace_1188471
  have hstable : (prefixWord ++ tailWord_1188471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188471).length < 2 ^ (prefixWord ++ tailWord_1188471).sum := by decide
  have hdescent : baseEnd_1188471 < baseStart_1188471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188491 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_1188491 : Nat := 118140960795 + 1188491 * 2 ^ 59
def prefixEnd_1188491 : Nat := 4983230072969 + 3 ^ 40 * 1188491 * 2
def baseEnd_1188491 : Nat := 610267136542814757196735

theorem tailTrace_1188491 : CollatzResearch.WordTrace tailWord_1188491 prefixEnd_1188491 610267136542814757196735 := by
  unfold tailWord_1188491
  simp only [CollatzResearch.WordTrace]
  refine ⟨43347827937307559947997327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28898551958205039965331551 43347827937307559947997327)
  ·
    refine ⟨65021741905961339921995991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43347827937307559947997327 65021741905961339921995991)
    ·
      refine ⟨97532612858942009882993987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65021741905961339921995991 97532612858942009882993987)
      ·
        refine ⟨146298919288413014824490981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97532612858942009882993987 146298919288413014824490981)
        ·
          refine ⟨27431047366577440279592059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146298919288413014824490981 27431047366577440279592059)
          ·
            refine ⟨41146571049866160419388089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27431047366577440279592059 41146571049866160419388089)
            ·
              refine ⟨30859928287399620314541067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41146571049866160419388089 30859928287399620314541067)
              ·
                refine ⟨46289892431099430471811601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30859928287399620314541067 46289892431099430471811601)
                ·
                  refine ⟨34717419323324572853858701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46289892431099430471811601 34717419323324572853858701)
                  ·
                    refine ⟨13019032246246714820197013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34717419323324572853858701 13019032246246714820197013)
                    ·
                      refine ⟨610267136542814757196735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13019032246246714820197013 610267136542814757196735)
                      ·
                        rfl

theorem cell23_1188491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_1188491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188491 prefixEnd_1188491 := by exact prefixLift 1188491
  have htrace : WordTrace (prefixWord ++ tailWord_1188491) baseStart_1188491 baseEnd_1188491 := by
    simpa [prefixWord, tailWord_1188491, baseEnd_1188491] using wordTrace_append hprefix tailTrace_1188491
  have hstable : (prefixWord ++ tailWord_1188491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188491).length < 2 ^ (prefixWord ++ tailWord_1188491).sum := by decide
  have hdescent : baseEnd_1188491 < baseStart_1188491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188528 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_1188528 : Nat := 118140960795 + 1188528 * 2 ^ 59
def prefixEnd_1188528 : Nat := 4983230072969 + 3 ^ 40 * 1188528 * 2
def baseEnd_1188528 : Nat := 610286135327031112434065

theorem tailTrace_1188528 : CollatzResearch.WordTrace tailWord_1188528 prefixEnd_1188528 610286135327031112434065 := by
  unfold tailWord_1188528
  simp only [CollatzResearch.WordTrace]
  refine ⟨21674588719086757633547119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28899451625449010178062825 21674588719086757633547119)
  ·
    refine ⟨32511883078630136450320679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21674588719086757633547119 32511883078630136450320679)
    ·
      refine ⟨48767824617945204675481019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32511883078630136450320679 48767824617945204675481019)
      ·
        refine ⟨73151736926917807013221529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48767824617945204675481019 73151736926917807013221529)
        ·
          refine ⟨54863802695188355259916147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73151736926917807013221529 54863802695188355259916147)
          ·
            refine ⟨82295704042782532889874221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54863802695188355259916147 82295704042782532889874221)
            ·
              refine ⟨30860889016043449833702833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82295704042782532889874221 30860889016043449833702833)
              ·
                refine ⟨23145666762032587375277125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30860889016043449833702833 23145666762032587375277125)
                ·
                  refine ⟨4339812517881110132864461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23145666762032587375277125 4339812517881110132864461)
                  ·
                    refine ⟨1627429694205416299824173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4339812517881110132864461 1627429694205416299824173)
                    ·
                      refine ⟨610286135327031112434065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1627429694205416299824173 610286135327031112434065)
                      ·
                        rfl

theorem cell23_1188528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_1188528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188528 prefixEnd_1188528 := by exact prefixLift 1188528
  have htrace : WordTrace (prefixWord ++ tailWord_1188528) baseStart_1188528 baseEnd_1188528 := by
    simpa [prefixWord, tailWord_1188528, baseEnd_1188528] using wordTrace_append hprefix tailTrace_1188528
  have hstable : (prefixWord ++ tailWord_1188528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188528).length < 2 ^ (prefixWord ++ tailWord_1188528).sum := by decide
  have hdescent : baseEnd_1188528 < baseStart_1188528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188529 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1188529 : Nat := 118140960795 + 1188529 * 2 ^ 59
def prefixEnd_1188529 : Nat := 4983230072969 + 3 ^ 40 * 1188529 * 2
def baseEnd_1188529 : Nat := 610286648807685608521561

theorem tailTrace_1188529 : CollatzResearch.WordTrace tailWord_1188529 prefixEnd_1188529 610286648807685608521561 := by
  unfold tailWord_1188529
  simp only [CollatzResearch.WordTrace]
  refine ⟨43349213911169892437880641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28899475940779928291920427 43349213911169892437880641)
  ·
    refine ⟨32511910433377419328410481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43349213911169892437880641 32511910433377419328410481)
    ·
      refine ⟨24383932825033064496307861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32511910433377419328410481 24383932825033064496307861)
      ·
        refine ⟨1142996851173424898264431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24383932825033064496307861 1142996851173424898264431)
        ·
          refine ⟨1714495276760137347396647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142996851173424898264431 1714495276760137347396647)
          ·
            refine ⟨2571742915140206021094971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714495276760137347396647 2571742915140206021094971)
            ·
              refine ⟨3857614372710309031642457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571742915140206021094971 3857614372710309031642457)
              ·
                refine ⟨2893210779532731773731843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3857614372710309031642457 2893210779532731773731843)
                ·
                  refine ⟨4339816169299097660597765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893210779532731773731843 4339816169299097660597765)
                  ·
                    refine ⟨813715531743580811362081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4339816169299097660597765 813715531743580811362081)
                    ·
                      refine ⟨610286648807685608521561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813715531743580811362081 610286648807685608521561)
                      ·
                        rfl

theorem cell23_1188529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1188529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188529 prefixEnd_1188529 := by exact prefixLift 1188529
  have htrace : WordTrace (prefixWord ++ tailWord_1188529) baseStart_1188529 baseEnd_1188529 := by
    simpa [prefixWord, tailWord_1188529, baseEnd_1188529] using wordTrace_append hprefix tailTrace_1188529
  have hstable : (prefixWord ++ tailWord_1188529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188529).length < 2 ^ (prefixWord ++ tailWord_1188529).sum := by decide
  have hdescent : baseEnd_1188529 < baseStart_1188529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188552 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 5]
def baseStart_1188552 : Nat := 118140960795 + 1188552 * 2 ^ 59
def prefixEnd_1188552 : Nat := 4983230072969 + 3 ^ 40 * 1188552 * 2
def baseEnd_1188552 : Nat := 67810939873637668725995

theorem tailTrace_1188552 : CollatzResearch.WordTrace tailWord_1188552 prefixEnd_1188552 67810939873637668725995 := by
  unfold tailWord_1188552
  simp only [CollatzResearch.WordTrace]
  refine ⟨21675026395043283682983955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28900035193391044910645273 21675026395043283682983955)
  ·
    refine ⟨32512539592564925524475933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21675026395043283682983955 32512539592564925524475933)
    ·
      refine ⟨12192202347211847071678475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32512539592564925524475933 12192202347211847071678475)
      ·
        refine ⟨18288303520817770607517713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12192202347211847071678475 18288303520817770607517713)
        ·
          refine ⟨13716227640613327955638285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18288303520817770607517713 13716227640613327955638285)
          ·
            refine ⟨5143585365229997983364357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13716227640613327955638285 5143585365229997983364357)
            ·
              refine ⟨964422255980624621880817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5143585365229997983364357 964422255980624621880817)
              ·
                refine ⟨723316691985468466410613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964422255980624621880817 723316691985468466410613)
                ·
                  refine ⟨67810939873637668725995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723316691985468466410613 67810939873637668725995)
                  ·
                    rfl

theorem cell23_1188552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 5].length) (baseStart_1188552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188552 prefixEnd_1188552 := by exact prefixLift 1188552
  have htrace : WordTrace (prefixWord ++ tailWord_1188552) baseStart_1188552 baseEnd_1188552 := by
    simpa [prefixWord, tailWord_1188552, baseEnd_1188552] using wordTrace_append hprefix tailTrace_1188552
  have hstable : (prefixWord ++ tailWord_1188552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188552).length < 2 ^ (prefixWord ++ tailWord_1188552).sum := by decide
  have hdescent : baseEnd_1188552 < baseStart_1188552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188562 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1188562 : Nat := 118140960795 + 1188562 * 2 ^ 59
def prefixEnd_1188562 : Nat := 4983230072969 + 3 ^ 40 * 1188562 * 2
def baseEnd_1188562 : Nat := 610303593669283979408909

theorem tailTrace_1188562 : CollatzResearch.WordTrace tailWord_1188562 prefixEnd_1188562 610303593669283979408909 := by
  unfold tailWord_1188562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10837604380012584768457985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28900278346700226049221293 10837604380012584768457985)
  ·
    refine ⟨8128203285009438576343489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10837604380012584768457985 8128203285009438576343489)
    ·
      refine ⟨6096152463757078932257617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8128203285009438576343489 6096152463757078932257617)
      ·
        refine ⟨4572114347817809199193213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6096152463757078932257617 4572114347817809199193213)
        ·
          refine ⟨1714542880431678449697455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4572114347817809199193213 1714542880431678449697455)
          ·
            refine ⟨2571814320647517674546183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714542880431678449697455 2571814320647517674546183)
            ·
              refine ⟨3857721480971276511819275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571814320647517674546183 3857721480971276511819275)
              ·
                refine ⟨5786582221456914767728913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857721480971276511819275 5786582221456914767728913)
                ·
                  refine ⟨4339936666092686075796685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5786582221456914767728913 4339936666092686075796685)
                  ·
                    refine ⟨1627476249784757278423757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4339936666092686075796685 1627476249784757278423757)
                    ·
                      refine ⟨610303593669283979408909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1627476249784757278423757 610303593669283979408909)
                      ·
                        rfl

theorem cell23_1188562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1188562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188562 prefixEnd_1188562 := by exact prefixLift 1188562
  have htrace : WordTrace (prefixWord ++ tailWord_1188562) baseStart_1188562 baseEnd_1188562 := by
    simpa [prefixWord, tailWord_1188562, baseEnd_1188562] using wordTrace_append hprefix tailTrace_1188562
  have hstable : (prefixWord ++ tailWord_1188562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188562).length < 2 ^ (prefixWord ++ tailWord_1188562).sum := by decide
  have hdescent : baseEnd_1188562 < baseStart_1188562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188585 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_1188585 : Nat := 118140960795 + 1188585 * 2 ^ 59
def prefixEnd_1188585 : Nat := 4983230072969 + 3 ^ 40 * 1188585 * 2
def baseEnd_1188585 : Nat := 610315403724337389421303

theorem tailTrace_1188585 : CollatzResearch.WordTrace tailWord_1188585 prefixEnd_1188585 610315403724337389421303 := by
  unfold tailWord_1188585
  simp only [CollatzResearch.WordTrace]
  refine ⟨43351256398967014001919209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28900837599311342667946139 43351256398967014001919209)
  ·
    refine ⟨32513442299225260501439407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43351256398967014001919209 32513442299225260501439407)
    ·
      refine ⟨48770163448837890752159111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32513442299225260501439407 48770163448837890752159111)
      ·
        refine ⟨73155245173256836128238667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48770163448837890752159111 73155245173256836128238667)
        ·
          refine ⟨109732867759885254192358001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73155245173256836128238667 109732867759885254192358001)
          ·
            refine ⟨82299650819913940644268501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109732867759885254192358001 82299650819913940644268501)
            ·
              refine ⟨1928898066091732983850043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82299650819913940644268501 1928898066091732983850043)
              ·
                refine ⟨2893347099137599475775065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928898066091732983850043 2893347099137599475775065)
                ·
                  refine ⟨2170010324353199606831299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2893347099137599475775065 2170010324353199606831299)
                  ·
                    refine ⟨3255015486529799410246949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170010324353199606831299 3255015486529799410246949)
                    ·
                      refine ⟨610315403724337389421303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3255015486529799410246949 610315403724337389421303)
                      ·
                        rfl

theorem cell23_1188585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_1188585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188585 prefixEnd_1188585 := by exact prefixLift 1188585
  have htrace : WordTrace (prefixWord ++ tailWord_1188585) baseStart_1188585 baseEnd_1188585 := by
    simpa [prefixWord, tailWord_1188585, baseEnd_1188585] using wordTrace_append hprefix tailTrace_1188585
  have hstable : (prefixWord ++ tailWord_1188585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188585).length < 2 ^ (prefixWord ++ tailWord_1188585).sum := by decide
  have hdescent : baseEnd_1188585 < baseStart_1188585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188597 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1188597 : Nat := 118140960795 + 1188597 * 2 ^ 59
def prefixEnd_1188597 : Nat := 4983230072969 + 3 ^ 40 * 1188597 * 2
def baseEnd_1188597 : Nat := 610321565492191342471249

theorem tailTrace_1188597 : CollatzResearch.WordTrace tailWord_1188597 prefixEnd_1188597 610321565492191342471249 := by
  unfold tailWord_1188597
  simp only [CollatzResearch.WordTrace]
  refine ⟨43351694074923540051356045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28901129383282360034237363 43351694074923540051356045)
  ·
    refine ⟨16256885278096327519258517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43351694074923540051356045 16256885278096327519258517)
    ·
      refine ⟨762041497410765352465243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16256885278096327519258517 762041497410765352465243)
      ·
        refine ⟨1143062246116148028697865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762041497410765352465243 1143062246116148028697865)
        ·
          refine ⟨857296684587111021523399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1143062246116148028697865 857296684587111021523399)
          ·
            refine ⟨1285945026880666532285099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857296684587111021523399 1285945026880666532285099)
            ·
              refine ⟨1928917540320999798427649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285945026880666532285099 1928917540320999798427649)
              ·
                refine ⟨1446688155240749848820737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928917540320999798427649 1446688155240749848820737)
                ·
                  refine ⟨1085016116430562386615553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1446688155240749848820737 1085016116430562386615553)
                  ·
                    refine ⟨813762087322921789961665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1085016116430562386615553 813762087322921789961665)
                    ·
                      refine ⟨610321565492191342471249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813762087322921789961665 610321565492191342471249)
                      ·
                        rfl

theorem cell23_1188597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1188597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188597 prefixEnd_1188597 := by exact prefixLift 1188597
  have htrace : WordTrace (prefixWord ++ tailWord_1188597) baseStart_1188597 baseEnd_1188597 := by
    simpa [prefixWord, tailWord_1188597, baseEnd_1188597] using wordTrace_append hprefix tailTrace_1188597
  have hstable : (prefixWord ++ tailWord_1188597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188597).length < 2 ^ (prefixWord ++ tailWord_1188597).sum := by decide
  have hdescent : baseEnd_1188597 < baseStart_1188597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188605 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_1188605 : Nat := 118140960795 + 1188605 * 2 ^ 59
def prefixEnd_1188605 : Nat := 4983230072969 + 3 ^ 40 * 1188605 * 2
def baseEnd_1188605 : Nat := 610325673337427311171211

theorem tailTrace_1188605 : CollatzResearch.WordTrace tailWord_1188605 prefixEnd_1188605 610325673337427311171211 := by
  unfold tailWord_1188605
  simp only [CollatzResearch.WordTrace]
  refine ⟨43351985858894557417647269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28901323905929704945098179 43351985858894557417647269)
  ·
    refine ⟨8128497348542729515808863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43351985858894557417647269 8128497348542729515808863)
    ·
      refine ⟨12192746022814094273713295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8128497348542729515808863 12192746022814094273713295)
      ·
        refine ⟨18289119034221141410569943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12192746022814094273713295 18289119034221141410569943)
        ·
          refine ⟨27433678551331712115854915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18289119034221141410569943 27433678551331712115854915)
          ·
            refine ⟨41150517826997568173782373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27433678551331712115854915 41150517826997568173782373)
            ·
              refine ⟨7715722092562044032584195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41150517826997568173782373 7715722092562044032584195)
              ·
                refine ⟨11573583138843066048876293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7715722092562044032584195 11573583138843066048876293)
                ·
                  refine ⟨2170046838533074884164305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11573583138843066048876293 2170046838533074884164305)
                  ·
                    refine ⟨1627535128899806163123229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2170046838533074884164305 1627535128899806163123229)
                    ·
                      refine ⟨610325673337427311171211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1627535128899806163123229 610325673337427311171211)
                      ·
                        rfl

theorem cell23_1188605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_1188605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188605 prefixEnd_1188605 := by exact prefixLift 1188605
  have htrace : WordTrace (prefixWord ++ tailWord_1188605) baseStart_1188605 baseEnd_1188605 := by
    simpa [prefixWord, tailWord_1188605, baseEnd_1188605] using wordTrace_append hprefix tailTrace_1188605
  have hstable : (prefixWord ++ tailWord_1188605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188605).length < 2 ^ (prefixWord ++ tailWord_1188605).sum := by decide
  have hdescent : baseEnd_1188605 < baseStart_1188605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188612 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_1188612 : Nat := 118140960795 + 1188612 * 2 ^ 59
def prefixEnd_1188612 : Nat := 4983230072969 + 3 ^ 40 * 1188612 * 2
def baseEnd_1188612 : Nat := 203443089234002927927893

theorem tailTrace_1188612 : CollatzResearch.WordTrace tailWord_1188612 prefixEnd_1188612 203443089234002927927893 := by
  unfold tailWord_1188612
  simp only [CollatzResearch.WordTrace]
  refine ⟨21676120584934598806576045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28901494113246131742101393 21676120584934598806576045)
  ·
    refine ⟨8128545219350474552466017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21676120584934598806576045 8128545219350474552466017)
    ·
      refine ⟨6096408914512855914349513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8128545219350474552466017 6096408914512855914349513)
      ·
        refine ⟨4572306685884641935762135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6096408914512855914349513 4572306685884641935762135)
        ·
          refine ⟨6858460028826962903643203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572306685884641935762135 6858460028826962903643203)
          ·
            refine ⟨10287690043240444355464805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6858460028826962903643203 10287690043240444355464805)
            ·
              refine ⟨1928941883107583316649651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10287690043240444355464805 1928941883107583316649651)
              ·
                refine ⟨2893412824661374974974477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928941883107583316649651 2893412824661374974974477)
                ·
                  refine ⟨1085029809248015615615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2893412824661374974974477 1085029809248015615615429)
                  ·
                    refine ⟨203443089234002927927893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085029809248015615615429 203443089234002927927893)
                    ·
                      rfl

theorem cell23_1188612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_1188612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188612 prefixEnd_1188612 := by exact prefixLift 1188612
  have htrace : WordTrace (prefixWord ++ tailWord_1188612) baseStart_1188612 baseEnd_1188612 := by
    simpa [prefixWord, tailWord_1188612, baseEnd_1188612] using wordTrace_append hprefix tailTrace_1188612
  have hstable : (prefixWord ++ tailWord_1188612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188612).length < 2 ^ (prefixWord ++ tailWord_1188612).sum := by decide
  have hdescent : baseEnd_1188612 < baseStart_1188612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188675 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 4]
def baseStart_1188675 : Nat := 118140960795 + 1188675 * 2 ^ 59
def prefixEnd_1188675 : Nat := 4983230072969 + 3 ^ 40 * 1188675 * 2
def baseEnd_1188675 : Nat := 610361616983242037295889

theorem tailTrace_1188675 : CollatzResearch.WordTrace tailWord_1188675 prefixEnd_1188675 610361616983242037295889 := by
  unfold tailWord_1188675
  simp only [CollatzResearch.WordTrace]
  refine ⟨43354538968640959372695479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28903025979093972915130319 43354538968640959372695479)
  ·
    refine ⟨65031808452961439059043219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43354538968640959372695479 65031808452961439059043219)
    ·
      refine ⟨97547712679442158588564829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65031808452961439059043219 97547712679442158588564829)
      ·
        refine ⟨36580392254790809470711811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97547712679442158588564829 36580392254790809470711811)
        ·
          refine ⟨54870588382186214206067717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36580392254790809470711811 54870588382186214206067717)
          ·
            refine ⟨10288235321659915163637697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54870588382186214206067717 10288235321659915163637697)
            ·
              refine ⟨7716176491244936372728273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10288235321659915163637697 7716176491244936372728273)
              ·
                refine ⟨5787132368433702279546205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7716176491244936372728273 5787132368433702279546205)
                ·
                  refine ⟨2170174638162638354829827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5787132368433702279546205 2170174638162638354829827)
                  ·
                    refine ⟨3255261957243957532244741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170174638162638354829827 3255261957243957532244741)
                    ·
                      refine ⟨610361616983242037295889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3255261957243957532244741 610361616983242037295889)
                      ·
                        rfl

theorem cell23_1188675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_1188675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188675 prefixEnd_1188675 := by exact prefixLift 1188675
  have htrace : WordTrace (prefixWord ++ tailWord_1188675) baseStart_1188675 baseEnd_1188675 := by
    simpa [prefixWord, tailWord_1188675, baseEnd_1188675] using wordTrace_append hprefix tailTrace_1188675
  have hstable : (prefixWord ++ tailWord_1188675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188675).length < 2 ^ (prefixWord ++ tailWord_1188675).sum := by decide
  have hdescent : baseEnd_1188675 < baseStart_1188675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188689 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 1, 5]
def baseStart_1188689 : Nat := 118140960795 + 1188689 * 2 ^ 59
def prefixEnd_1188689 : Nat := 4983230072969 + 3 ^ 40 * 1188689 * 2
def baseEnd_1188689 : Nat := 203456268570801660840275

theorem tailTrace_1188689 : CollatzResearch.WordTrace tailWord_1188689 prefixEnd_1188689 203456268570801660840275 := by
  unfold tailWord_1188689
  simp only [CollatzResearch.WordTrace]
  refine ⟨43355049590590239763705121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28903366393726826509136747 43355049590590239763705121)
  ·
    refine ⟨32516287192942679822778841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43355049590590239763705121 32516287192942679822778841)
    ·
      refine ⟨24387215394707009867084131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32516287192942679822778841 24387215394707009867084131)
      ·
        refine ⟨36580823092060514800626197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24387215394707009867084131 36580823092060514800626197)
        ·
          refine ⟨1714726082440336631279353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36580823092060514800626197 1714726082440336631279353)
          ·
            refine ⟨1286044561830252473459515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1714726082440336631279353 1286044561830252473459515)
            ·
              refine ⟨1929066842745378710189273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286044561830252473459515 1929066842745378710189273)
              ·
                refine ⟨1446800132059034032641955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929066842745378710189273 1446800132059034032641955)
                ·
                  refine ⟨2170200198088551048962933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446800132059034032641955 2170200198088551048962933)
                  ·
                    refine ⟨203456268570801660840275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2170200198088551048962933 203456268570801660840275)
                    ·
                      rfl

theorem cell23_1188689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_1188689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188689 prefixEnd_1188689 := by exact prefixLift 1188689
  have htrace : WordTrace (prefixWord ++ tailWord_1188689) baseStart_1188689 baseEnd_1188689 := by
    simpa [prefixWord, tailWord_1188689, baseEnd_1188689] using wordTrace_append hprefix tailTrace_1188689
  have hstable : (prefixWord ++ tailWord_1188689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188689).length < 2 ^ (prefixWord ++ tailWord_1188689).sum := by decide
  have hdescent : baseEnd_1188689 < baseStart_1188689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188706 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1188706 : Nat := 118140960795 + 1188706 * 2 ^ 59
def prefixEnd_1188706 : Nat := 4983230072969 + 3 ^ 40 * 1188706 * 2
def baseEnd_1188706 : Nat := 203459178294510472002749

theorem tailTrace_1188706 : CollatzResearch.WordTrace tailWord_1188706 prefixEnd_1188706 203459178294510472002749 := by
  unfold tailWord_1188706
  simp only [CollatzResearch.WordTrace]
  refine ⟨10838917407882162916768493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28903779754352434444715981 10838917407882162916768493)
  ·
    refine ⟨4064594027955811093788185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10838917407882162916768493 4064594027955811093788185)
    ·
      refine ⟨3048445520966858320341139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4064594027955811093788185 3048445520966858320341139)
      ·
        refine ⟨4572668281450287480511709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048445520966858320341139 4572668281450287480511709)
        ·
          refine ⟨1714750605543857805191891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4572668281450287480511709 1714750605543857805191891)
          ·
            refine ⟨2572125908315786707787837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714750605543857805191891 2572125908315786707787837)
            ·
              refine ⟨964547215618420015420439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2572125908315786707787837 964547215618420015420439)
              ·
                refine ⟨1446820823427630023130659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964547215618420015420439 1446820823427630023130659)
                ·
                  refine ⟨2170231235141445034695989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1446820823427630023130659 2170231235141445034695989)
                  ·
                    refine ⟨203459178294510472002749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2170231235141445034695989 203459178294510472002749)
                    ·
                      rfl

theorem cell23_1188706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1188706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188706 prefixEnd_1188706 := by exact prefixLift 1188706
  have htrace : WordTrace (prefixWord ++ tailWord_1188706) baseStart_1188706 baseEnd_1188706 := by
    simpa [prefixWord, tailWord_1188706, baseEnd_1188706] using wordTrace_append hprefix tailTrace_1188706
  have hstable : (prefixWord ++ tailWord_1188706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188706).length < 2 ^ (prefixWord ++ tailWord_1188706).sum := by decide
  have hdescent : baseEnd_1188706 < baseStart_1188706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188712 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1188712 : Nat := 118140960795 + 1188712 * 2 ^ 59
def prefixEnd_1188712 : Nat := 4983230072969 + 3 ^ 40 * 1188712 * 2
def baseEnd_1188712 : Nat := 610380615767458392533219

theorem tailTrace_1188712 : CollatzResearch.WordTrace tailWord_1188712 prefixEnd_1188712 610380615767458392533219 := by
  unfold tailWord_1188712
  simp only [CollatzResearch.WordTrace]
  refine ⟨21677944234753457345896195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28903925646337943127861593 21677944234753457345896195)
  ·
    refine ⟨32516916352130186018844293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21677944234753457345896195 32516916352130186018844293)
    ·
      refine ⟨6096921816024409878533305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32516916352130186018844293 6096921816024409878533305)
      ·
        refine ⟨4572691362018307408899979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6096921816024409878533305 4572691362018307408899979)
        ·
          refine ⟨6859037043027461113349969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572691362018307408899979 6859037043027461113349969)
          ·
            refine ⟨5144277782270595835012477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6859037043027461113349969 5144277782270595835012477)
            ·
              refine ⟨1929104168351473438129679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5144277782270595835012477 1929104168351473438129679)
              ·
                refine ⟨2893656252527210157194519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929104168351473438129679 2893656252527210157194519)
                ·
                  refine ⟨4340484378790815235791779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893656252527210157194519 4340484378790815235791779)
                  ·
                    refine ⟨6510726568186222853687669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4340484378790815235791779 6510726568186222853687669)
                    ·
                      refine ⟨610380615767458392533219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6510726568186222853687669 610380615767458392533219)
                      ·
                        rfl

theorem cell23_1188712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1188712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188712 prefixEnd_1188712 := by exact prefixLift 1188712
  have htrace : WordTrace (prefixWord ++ tailWord_1188712) baseStart_1188712 baseEnd_1188712 := by
    simpa [prefixWord, tailWord_1188712, baseEnd_1188712] using wordTrace_append hprefix tailTrace_1188712
  have hstable : (prefixWord ++ tailWord_1188712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188712).length < 2 ^ (prefixWord ++ tailWord_1188712).sum := by decide
  have hdescent : baseEnd_1188712 < baseStart_1188712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188752 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 7, 3, 2]
def baseStart_1188752 : Nat := 118140960795 + 1188752 * 2 ^ 59
def prefixEnd_1188752 : Nat := 4983230072969 + 3 ^ 40 * 1188752 * 2
def baseEnd_1188752 : Nat := 610401154993638236033035

theorem tailTrace_1188752 : CollatzResearch.WordTrace tailWord_1188752 prefixEnd_1188752 610401154993638236033035 := by
  unfold tailWord_1188752
  simp only [CollatzResearch.WordTrace]
  refine ⟨21678673694681000761624255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28904898259574667682165673 21678673694681000761624255)
  ·
    refine ⟨32518010542021501142436383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21678673694681000761624255 32518010542021501142436383)
    ·
      refine ⟨48777015813032251713654575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32518010542021501142436383 48777015813032251713654575)
      ·
        refine ⟨73165523719548377570481863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48777015813032251713654575 73165523719548377570481863)
        ·
          refine ⟨109748285579322566355722795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73165523719548377570481863 109748285579322566355722795)
          ·
            refine ⟨164622428368983849533584193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109748285579322566355722795 164622428368983849533584193)
            ·
              refine ⟨123466821276737887150188145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164622428368983849533584193 123466821276737887150188145)
              ·
                refine ⟨92600115957553415362641109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123466821276737887150188145 92600115957553415362641109)
                ·
                  refine ⟨2170315217755158172561901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92600115957553415362641109 2170315217755158172561901)
                  ·
                    refine ⟨813868206658184314710713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2170315217755158172561901 813868206658184314710713)
                    ·
                      refine ⟨610401154993638236033035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813868206658184314710713 610401154993638236033035)
                      ·
                        rfl

theorem cell23_1188752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 3, 2].length) (baseStart_1188752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188752 prefixEnd_1188752 := by exact prefixLift 1188752
  have htrace : WordTrace (prefixWord ++ tailWord_1188752) baseStart_1188752 baseEnd_1188752 := by
    simpa [prefixWord, tailWord_1188752, baseEnd_1188752] using wordTrace_append hprefix tailTrace_1188752
  have hstable : (prefixWord ++ tailWord_1188752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188752).length < 2 ^ (prefixWord ++ tailWord_1188752).sum := by decide
  have hdescent : baseEnd_1188752 < baseStart_1188752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188790 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1188790 : Nat := 118140960795 + 1188790 * 2 ^ 59
def prefixEnd_1188790 : Nat := 4983230072969 + 3 ^ 40 * 1188790 * 2
def baseEnd_1188790 : Nat := 610420667258509087357861

theorem tailTrace_1188790 : CollatzResearch.WordTrace tailWord_1188790 prefixEnd_1188790 610420667258509087357861 := by
  unfold tailWord_1188790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709920835201520875820739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28905822242149556008754549 2709920835201520875820739)
  ·
    refine ⟨4064881252802281313731109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709920835201520875820739 4064881252802281313731109)
    ·
      refine ⟨762165234900427746324583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4064881252802281313731109 762165234900427746324583)
      ·
        refine ⟨1143247852350641619486875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762165234900427746324583 1143247852350641619486875)
        ·
          refine ⟨1714871778525962429230313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143247852350641619486875 1714871778525962429230313)
          ·
            refine ⟨1286153833894471821922735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1714871778525962429230313 1286153833894471821922735)
            ·
              refine ⟨1929230750841707732884103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286153833894471821922735 1929230750841707732884103)
              ·
                refine ⟨2893846126262561599326155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929230750841707732884103 2893846126262561599326155)
                ·
                  refine ⟨4340769189393842398989233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2893846126262561599326155 4340769189393842398989233)
                  ·
                    refine ⟨3255576892045381799241925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340769189393842398989233 3255576892045381799241925)
                    ·
                      refine ⟨610420667258509087357861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3255576892045381799241925 610420667258509087357861)
                      ·
                        rfl

theorem cell23_1188790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1188790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188790 prefixEnd_1188790 := by exact prefixLift 1188790
  have htrace : WordTrace (prefixWord ++ tailWord_1188790) baseStart_1188790 baseEnd_1188790 := by
    simpa [prefixWord, tailWord_1188790, baseEnd_1188790] using wordTrace_append hprefix tailTrace_1188790
  have hstable : (prefixWord ++ tailWord_1188790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188790).length < 2 ^ (prefixWord ++ tailWord_1188790).sum := by decide
  have hdescent : baseEnd_1188790 < baseStart_1188790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188795 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4]
def baseStart_1188795 : Nat := 118140960795 + 1188795 * 2 ^ 59
def prefixEnd_1188795 : Nat := 4983230072969 + 3 ^ 40 * 1188795 * 2
def baseEnd_1188795 : Nat := 610423234661781567795337

theorem tailTrace_1188795 : CollatzResearch.WordTrace tailWord_1188795 prefixEnd_1188795 610423234661781567795337 := by
  unfold tailWord_1188795
  simp only [CollatzResearch.WordTrace]
  refine ⟨43358915728206219867063839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28905943818804146578042559 43358915728206219867063839)
  ·
    refine ⟨65038373592309329800595759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43358915728206219867063839 65038373592309329800595759)
    ·
      refine ⟨97557560388463994700893639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65038373592309329800595759 97557560388463994700893639)
      ·
        refine ⟨146336340582695992051340459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97557560388463994700893639 146336340582695992051340459)
        ·
          refine ⟨219504510874043988077010689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146336340582695992051340459 219504510874043988077010689)
          ·
            refine ⟨164628383155532991057758017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219504510874043988077010689 164628383155532991057758017)
            ·
              refine ⟨123471287366649743293318513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164628383155532991057758017 123471287366649743293318513)
              ·
                refine ⟨92603465524987307469988885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123471287366649743293318513 92603465524987307469988885)
                ·
                  refine ⟨4340787446483780037655729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92603465524987307469988885 4340787446483780037655729)
                  ·
                    refine ⟨3255590584862835028241797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4340787446483780037655729 3255590584862835028241797)
                    ·
                      refine ⟨610423234661781567795337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3255590584862835028241797 610423234661781567795337)
                      ·
                        rfl

theorem cell23_1188795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_1188795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188795 prefixEnd_1188795 := by exact prefixLift 1188795
  have htrace : WordTrace (prefixWord ++ tailWord_1188795) baseStart_1188795 baseEnd_1188795 := by
    simpa [prefixWord, tailWord_1188795, baseEnd_1188795] using wordTrace_append hprefix tailTrace_1188795
  have hstable : (prefixWord ++ tailWord_1188795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188795).length < 2 ^ (prefixWord ++ tailWord_1188795).sum := by decide
  have hdescent : baseEnd_1188795 < baseStart_1188795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188839 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 7]
def baseStart_1188839 : Nat := 118140960795 + 1188839 * 2 ^ 59
def prefixEnd_1188839 : Nat := 4983230072969 + 3 ^ 40 * 1188839 * 2
def baseEnd_1188839 : Nat := 67827314201175488405015

theorem tailTrace_1188839 : CollatzResearch.WordTrace tailWord_1188839 prefixEnd_1188839 67827314201175488405015 := by
  unfold tailWord_1188839
  simp only [CollatzResearch.WordTrace]
  refine ⟨43360520540046815381665571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28907013693364543587777047 43360520540046815381665571)
  ·
    refine ⟨65040780810070223072498357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43360520540046815381665571 65040780810070223072498357)
    ·
      refine ⟨6097573200944083413046721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65040780810070223072498357 6097573200944083413046721)
      ·
        refine ⟨4573179900708062559785041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6097573200944083413046721 4573179900708062559785041)
        ·
          refine ⟨3429884925531046919838781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4573179900708062559785041 3429884925531046919838781)
          ·
            refine ⟨1286206847074142594939543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3429884925531046919838781 1286206847074142594939543)
            ·
              refine ⟨1929310270611213892409315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286206847074142594939543 1929310270611213892409315)
              ·
                refine ⟨2893965405916820838613973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929310270611213892409315 2893965405916820838613973)
                ·
                  refine ⟨67827314201175488405015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2893965405916820838613973 67827314201175488405015)
                  ·
                    rfl

theorem cell23_1188839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 7].length) (baseStart_1188839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188839 prefixEnd_1188839 := by exact prefixLift 1188839
  have htrace : WordTrace (prefixWord ++ tailWord_1188839) baseStart_1188839 baseEnd_1188839 := by
    simpa [prefixWord, tailWord_1188839, baseEnd_1188839] using wordTrace_append hprefix tailTrace_1188839
  have hstable : (prefixWord ++ tailWord_1188839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188839).length < 2 ^ (prefixWord ++ tailWord_1188839).sum := by decide
  have hdescent : baseEnd_1188839 < baseStart_1188839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188850 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1188850 : Nat := 118140960795 + 1188850 * 2 ^ 59
def prefixEnd_1188850 : Nat := 4983230072969 + 3 ^ 40 * 1188850 * 2
def baseEnd_1188850 : Nat := 610451476097778852607585

theorem tailTrace_1188850 : CollatzResearch.WordTrace tailWord_1188850 prefixEnd_1188850 610451476097778852607585 := by
  unfold tailWord_1188850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10840230435751741065079001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28907281162004642840210669 10840230435751741065079001)
  ·
    refine ⟨8130172826813805798809251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10840230435751741065079001 8130172826813805798809251)
    ·
      refine ⟨12195259240220708698213877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8130172826813805798809251 12195259240220708698213877)
      ·
        refine ⟨1143305553770691440457551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12195259240220708698213877 1143305553770691440457551)
        ·
          refine ⟨1714958330656037160686327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143305553770691440457551 1714958330656037160686327)
          ·
            refine ⟨2572437495984055741029491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714958330656037160686327 2572437495984055741029491)
            ·
              refine ⟨3858656243976083611544237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572437495984055741029491 3858656243976083611544237)
              ·
                refine ⟨1446996091491031354329089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3858656243976083611544237 1446996091491031354329089)
                ·
                  refine ⟨1085247068618273515746817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1446996091491031354329089 1085247068618273515746817)
                  ·
                    refine ⟨813935301463705136810113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1085247068618273515746817 813935301463705136810113)
                    ·
                      refine ⟨610451476097778852607585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 813935301463705136810113 610451476097778852607585)
                      ·
                        rfl

theorem cell23_1188850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1188850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188850 prefixEnd_1188850 := by exact prefixLift 1188850
  have htrace : WordTrace (prefixWord ++ tailWord_1188850) baseStart_1188850 baseEnd_1188850 := by
    simpa [prefixWord, tailWord_1188850, baseEnd_1188850] using wordTrace_append hprefix tailTrace_1188850
  have hstable : (prefixWord ++ tailWord_1188850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188850).length < 2 ^ (prefixWord ++ tailWord_1188850).sum := by decide
  have hdescent : baseEnd_1188850 < baseStart_1188850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188912 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 6]
def baseStart_1188912 : Nat := 118140960795 + 1188912 * 2 ^ 59
def prefixEnd_1188912 : Nat := 4983230072969 + 3 ^ 40 * 1188912 * 2
def baseEnd_1188912 : Nat := 67831479099817512225811

theorem tailTrace_1188912 : CollatzResearch.WordTrace tailWord_1188912 prefixEnd_1188912 67831479099817512225811 := by
  unfold tailWord_1188912
  simp only [CollatzResearch.WordTrace]
  refine ⟨21681591534391174424536495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28908788712521565899381993 21681591534391174424536495)
  ·
    refine ⟨32522387301586761636804743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21681591534391174424536495 32522387301586761636804743)
    ·
      refine ⟨48783580952380142455207115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32522387301586761636804743 48783580952380142455207115)
      ·
        refine ⟨73175371428570213682810673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48783580952380142455207115 73175371428570213682810673)
        ·
          refine ⟨54881528571427660262108005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73175371428570213682810673 54881528571427660262108005)
          ·
            refine ⟨10290286607142686299145251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54881528571427660262108005 10290286607142686299145251)
            ·
              refine ⟨15435429910714029448717877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10290286607142686299145251 15435429910714029448717877)
              ·
                refine ⟨1447071554129440260817301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15435429910714029448717877 1447071554129440260817301)
                ·
                  refine ⟨67831479099817512225811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1447071554129440260817301 67831479099817512225811)
                  ·
                    rfl

theorem cell23_1188912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_1188912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188912 prefixEnd_1188912 := by exact prefixLift 1188912
  have htrace : WordTrace (prefixWord ++ tailWord_1188912) baseStart_1188912 baseEnd_1188912 := by
    simpa [prefixWord, tailWord_1188912, baseEnd_1188912] using wordTrace_append hprefix tailTrace_1188912
  have hstable : (prefixWord ++ tailWord_1188912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188912).length < 2 ^ (prefixWord ++ tailWord_1188912).sum := by decide
  have hdescent : baseEnd_1188912 < baseStart_1188912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188916 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1188916 : Nat := 118140960795 + 1188916 * 2 ^ 59
def prefixEnd_1188916 : Nat := 4983230072969 + 3 ^ 40 * 1188916 * 2
def baseEnd_1188916 : Nat := 203495121940325198127427

theorem tailTrace_1188916 : CollatzResearch.WordTrace tailWord_1188916 prefixEnd_1188916 203495121940325198127427 := by
  unfold tailWord_1188916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21681664480383928766109301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28908885973845238354812401 21681664480383928766109301)
  ·
    refine ⟨2032656045035993321822747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21681664480383928766109301 2032656045035993321822747)
    ·
      refine ⟨3048984067553989982734121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032656045035993321822747 3048984067553989982734121)
      ·
        refine ⟨2286738050665492487050591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3048984067553989982734121 2286738050665492487050591)
        ·
          refine ⟨3430107075998238730575887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286738050665492487050591 3430107075998238730575887)
          ·
            refine ⟨5145160613997358095863831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430107075998238730575887 5145160613997358095863831)
            ·
              refine ⟨7717740920996037143795747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5145160613997358095863831 7717740920996037143795747)
              ·
                refine ⟨11576611381494055715693621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7717740920996037143795747 11576611381494055715693621)
                ·
                  refine ⟨1085307317015067723346277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11576611381494055715693621 1085307317015067723346277)
                  ·
                    refine ⟨203495121940325198127427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085307317015067723346277 203495121940325198127427)
                    ·
                      rfl

theorem cell23_1188916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1188916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188916 prefixEnd_1188916 := by exact prefixLift 1188916
  have htrace : WordTrace (prefixWord ++ tailWord_1188916) baseStart_1188916 baseEnd_1188916 := by
    simpa [prefixWord, tailWord_1188916, baseEnd_1188916] using wordTrace_append hprefix tailTrace_1188916
  have hstable : (prefixWord ++ tailWord_1188916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188916).length < 2 ^ (prefixWord ++ tailWord_1188916).sum := by decide
  have hdescent : baseEnd_1188916 < baseStart_1188916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188926 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1188926 : Nat := 118140960795 + 1188926 * 2 ^ 59
def prefixEnd_1188926 : Nat := 4983230072969 + 3 ^ 40 * 1188926 * 2
def baseEnd_1188926 : Nat := 610490500627520555257235

theorem tailTrace_1188926 : CollatzResearch.WordTrace tailWord_1188926 prefixEnd_1188926 610490500627520555257235 := by
  unfold tailWord_1188926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420461711341453655010329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28909129127154419493388421 5420461711341453655010329)
  ·
    refine ⟨4065346283506090241257747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5420461711341453655010329 4065346283506090241257747)
    ·
      refine ⟨6098019425259135361886621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4065346283506090241257747 6098019425259135361886621)
      ·
        refine ⟨2286757284472175760707483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6098019425259135361886621 2286757284472175760707483)
        ·
          refine ⟨3430135926708263641061225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286757284472175760707483 3430135926708263641061225)
          ·
            refine ⟨2572601945031197730795919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3430135926708263641061225 2572601945031197730795919)
            ·
              refine ⟨3858902917546796596193879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572601945031197730795919 3858902917546796596193879)
              ·
                refine ⟨5788354376320194894290819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3858902917546796596193879 5788354376320194894290819)
                ·
                  refine ⟨8682531564480292341436229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5788354376320194894290819 8682531564480292341436229)
                  ·
                    refine ⟨1627974668340054814019293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8682531564480292341436229 1627974668340054814019293)
                    ·
                      refine ⟨610490500627520555257235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1627974668340054814019293 610490500627520555257235)
                      ·
                        rfl

theorem cell23_1188926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1188926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188926 prefixEnd_1188926 := by exact prefixLift 1188926
  have htrace : WordTrace (prefixWord ++ tailWord_1188926) baseStart_1188926 baseEnd_1188926 := by
    simpa [prefixWord, tailWord_1188926, baseEnd_1188926] using wordTrace_append hprefix tailTrace_1188926
  have hstable : (prefixWord ++ tailWord_1188926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188926).length < 2 ^ (prefixWord ++ tailWord_1188926).sum := by decide
  have hdescent : baseEnd_1188926 < baseStart_1188926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188946 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_1188946 : Nat := 118140960795 + 1188946 * 2 ^ 59
def prefixEnd_1188946 : Nat := 4983230072969 + 3 ^ 40 * 1188946 * 2
def baseEnd_1188946 : Nat := 67833418915623386334127

theorem tailTrace_1188946 : CollatzResearch.WordTrace tailWord_1188946 prefixEnd_1188946 67833418915623386334127 := by
  unfold tailWord_1188946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10841105787664793163952673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28909615433772781770540461 10841105787664793163952673)
  ·
    refine ⟨8130829340748594872964505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10841105787664793163952673 8130829340748594872964505)
    ·
      refine ⟨6098122005561446154723379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8130829340748594872964505 6098122005561446154723379)
      ·
        refine ⟨9147183008342169232085069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6098122005561446154723379 9147183008342169232085069)
        ·
          refine ⟨3430193628128313462031901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9147183008342169232085069 3430193628128313462031901)
          ·
            refine ⟨1286322610548117548261963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3430193628128313462031901 1286322610548117548261963)
            ·
              refine ⟨1929483915822176322392945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286322610548117548261963 1929483915822176322392945)
              ·
                refine ⟨1447112936866632241794709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929483915822176322392945 1447112936866632241794709)
                ·
                  refine ⟨67833418915623386334127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1447112936866632241794709 67833418915623386334127)
                  ·
                    rfl

theorem cell23_1188946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_1188946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188946 prefixEnd_1188946 := by exact prefixLift 1188946
  have htrace : WordTrace (prefixWord ++ tailWord_1188946) baseStart_1188946 baseEnd_1188946 := by
    simpa [prefixWord, tailWord_1188946, baseEnd_1188946] using wordTrace_append hprefix tailTrace_1188946
  have hstable : (prefixWord ++ tailWord_1188946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188946).length < 2 ^ (prefixWord ++ tailWord_1188946).sum := by decide
  have hdescent : baseEnd_1188946 < baseStart_1188946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188950 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1188950 : Nat := 118140960795 + 1188950 * 2 ^ 59
def prefixEnd_1188950 : Nat := 4983230072969 + 3 ^ 40 * 1188950 * 2
def baseEnd_1188950 : Nat := 203500941387742820452375

theorem tailTrace_1188950 : CollatzResearch.WordTrace tailWord_1188950 prefixEnd_1188950 203500941387742820452375 := by
  unfold tailWord_1188950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710285565165292583684769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28909712695096454225970869 2710285565165292583684769)
  ·
    refine ⟨2032714173873969437763577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2710285565165292583684769 2032714173873969437763577)
    ·
      refine ⟨1524535630405477078322683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2032714173873969437763577 1524535630405477078322683)
      ·
        refine ⟨2286803445608215617484025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524535630405477078322683 2286803445608215617484025)
        ·
          refine ⟨1715102584206161713113019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2286803445608215617484025 1715102584206161713113019)
          ·
            refine ⟨2572653876309242569669529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715102584206161713113019 2572653876309242569669529)
            ·
              refine ⟨1929490407231931927252147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572653876309242569669529 1929490407231931927252147)
              ·
                refine ⟨2894235610847897890878221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929490407231931927252147 2894235610847897890878221)
                ·
                  refine ⟨1085338354067961709079333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2894235610847897890878221 1085338354067961709079333)
                  ·
                    refine ⟨203500941387742820452375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085338354067961709079333 203500941387742820452375)
                    ·
                      rfl

theorem cell23_1188950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1188950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188950 prefixEnd_1188950 := by exact prefixLift 1188950
  have htrace : WordTrace (prefixWord ++ tailWord_1188950) baseStart_1188950 baseEnd_1188950 := by
    simpa [prefixWord, tailWord_1188950, baseEnd_1188950] using wordTrace_append hprefix tailTrace_1188950
  have hstable : (prefixWord ++ tailWord_1188950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188950).length < 2 ^ (prefixWord ++ tailWord_1188950).sum := by decide
  have hdescent : baseEnd_1188950 < baseStart_1188950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188989 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1188989 : Nat := 118140960795 + 1188989 * 2 ^ 59
def prefixEnd_1188989 : Nat := 4983230072969 + 3 ^ 40 * 1188989 * 2
def baseEnd_1188989 : Nat := 203507616636251269589815

theorem tailTrace_1188989 : CollatzResearch.WordTrace tailWord_1188989 prefixEnd_1188989 203507616636251269589815 := by
  unfold tailWord_1188989
  simp only [CollatzResearch.WordTrace]
  refine ⟨43365991489503390999626021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28910660993002260666417347 43365991489503390999626021)
  ·
    refine ⟨8131123404281885812429879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43365991489503390999626021 8131123404281885812429879)
    ·
      refine ⟨12196685106422828718644819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8131123404281885812429879 12196685106422828718644819)
      ·
        refine ⟨18295027659634243077967229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12196685106422828718644819 18295027659634243077967229)
        ·
          refine ⟨6860635372362841154237711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18295027659634243077967229 6860635372362841154237711)
          ·
            refine ⟨10290953058544261731356567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6860635372362841154237711 10290953058544261731356567)
            ·
              refine ⟨15436429587816392597034851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10290953058544261731356567 15436429587816392597034851)
              ·
                refine ⟨23154644381724588895552277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15436429587816392597034851 23154644381724588895552277)
                ·
                  refine ⟨1085373955393340104479013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23154644381724588895552277 1085373955393340104479013)
                  ·
                    refine ⟨203507616636251269589815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085373955393340104479013 203507616636251269589815)
                    ·
                      rfl

theorem cell23_1188989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1188989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188989 prefixEnd_1188989 := by exact prefixLift 1188989
  have htrace : WordTrace (prefixWord ++ tailWord_1188989) baseStart_1188989 baseEnd_1188989 := by
    simpa [prefixWord, tailWord_1188989, baseEnd_1188989] using wordTrace_append hprefix tailTrace_1188989
  have hstable : (prefixWord ++ tailWord_1188989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188989).length < 2 ^ (prefixWord ++ tailWord_1188989).sum := by decide
  have hdescent : baseEnd_1188989 < baseStart_1188989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188996 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_1188996 : Nat := 118140960795 + 1188996 * 2 ^ 59
def prefixEnd_1188996 : Nat := 4983230072969 + 3 ^ 40 * 1188996 * 2
def baseEnd_1188996 : Nat := 610526444273335281381913

theorem tailTrace_1188996 : CollatzResearch.WordTrace tailWord_1188996 prefixEnd_1188996 610526444273335281381913 := by
  unfold tailWord_1188996
  simp only [CollatzResearch.WordTrace]
  refine ⟨21683123400239015597565421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28910831200318687463420561 21683123400239015597565421)
  ·
    refine ⟨8131171275089630849087033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21683123400239015597565421 8131171275089630849087033)
    ·
      refine ⟨6098378456317223136815275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8131171275089630849087033 6098378456317223136815275)
      ·
        refine ⟨9147567684475834705222913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6098378456317223136815275 9147567684475834705222913)
        ·
          refine ⟨6860675763356876028917185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9147567684475834705222913 6860675763356876028917185)
          ·
            refine ⟨5145506822517657021687889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6860675763356876028917185 5145506822517657021687889)
            ·
              refine ⟨3859130116888242766265917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5145506822517657021687889 3859130116888242766265917)
              ·
                refine ⟨1447173793833091037349719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859130116888242766265917 1447173793833091037349719)
                ·
                  refine ⟨2170760690749636556024579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447173793833091037349719 2170760690749636556024579)
                  ·
                    refine ⟨3256141036124454834036869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2170760690749636556024579 3256141036124454834036869)
                    ·
                      refine ⟨610526444273335281381913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3256141036124454834036869 610526444273335281381913)
                      ·
                        rfl

theorem cell23_1188996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_1188996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188996 prefixEnd_1188996 := by exact prefixLift 1188996
  have htrace : WordTrace (prefixWord ++ tailWord_1188996) baseStart_1188996 baseEnd_1188996 := by
    simpa [prefixWord, tailWord_1188996, baseEnd_1188996] using wordTrace_append hprefix tailTrace_1188996
  have hstable : (prefixWord ++ tailWord_1188996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188996).length < 2 ^ (prefixWord ++ tailWord_1188996).sum := by decide
  have hdescent : baseEnd_1188996 < baseStart_1188996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188999 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1188999 : Nat := 118140960795 + 1188999 * 2 ^ 59
def prefixEnd_1188999 : Nat := 4983230072969 + 3 ^ 40 * 1188999 * 2
def baseEnd_1188999 : Nat := 610527984715298769644399

theorem tailTrace_1188999 : CollatzResearch.WordTrace tailWord_1188999 prefixEnd_1188999 610527984715298769644399 := by
  unfold tailWord_1188999
  simp only [CollatzResearch.WordTrace]
  refine ⟨43366356219467162707490051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28910904146311441804993367 43366356219467162707490051)
  ·
    refine ⟨65049534329200744061235077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43366356219467162707490051 65049534329200744061235077)
    ·
      refine ⟨12196787686725139511481577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65049534329200744061235077 12196787686725139511481577)
      ·
        refine ⟨9147590765043854633611183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12196787686725139511481577 9147590765043854633611183)
        ·
          refine ⟨13721386147565781950416775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9147590765043854633611183 13721386147565781950416775)
          ·
            refine ⟨20582079221348672925625163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13721386147565781950416775 20582079221348672925625163)
            ·
              refine ⟨30873118832023009388437745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20582079221348672925625163 30873118832023009388437745)
              ·
                refine ⟨23154839124017257041328309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30873118832023009388437745 23154839124017257041328309)
                ·
                  refine ⟨2170766167876617847624529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23154839124017257041328309 2170766167876617847624529)
                  ·
                    refine ⟨1628074625907463385718397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2170766167876617847624529 1628074625907463385718397)
                    ·
                      refine ⟨610527984715298769644399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1628074625907463385718397 610527984715298769644399)
                      ·
                        rfl

theorem cell23_1188999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1188999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1188999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1188999 prefixEnd_1188999 := by exact prefixLift 1188999
  have htrace : WordTrace (prefixWord ++ tailWord_1188999) baseStart_1188999 baseEnd_1188999 := by
    simpa [prefixWord, tailWord_1188999, baseEnd_1188999] using wordTrace_append hprefix tailTrace_1188999
  have hstable : (prefixWord ++ tailWord_1188999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188999).length < 2 ^ (prefixWord ++ tailWord_1188999).sum := by decide
  have hdescent : baseEnd_1188999 < baseStart_1188999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189006 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_1189006 : Nat := 118140960795 + 1189006 * 2 ^ 59
def prefixEnd_1189006 : Nat := 4983230072969 + 3 ^ 40 * 1189006 * 2
def baseEnd_1189006 : Nat := 203510526359960080752289

theorem tailTrace_1189006 : CollatzResearch.WordTrace tailWord_1189006 prefixEnd_1189006 203510526359960080752289 := by
  unfold tailWord_1189006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420826441305225362874359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28911074353627868601996581 5420826441305225362874359)
  ·
    refine ⟨8131239661957838044311539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5420826441305225362874359 8131239661957838044311539)
    ·
      refine ⟨12196859492936757066467309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8131239661957838044311539 12196859492936757066467309)
      ·
        refine ⟨4573822309851283899925241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12196859492936757066467309 4573822309851283899925241)
        ·
          refine ⟨3430366732388462924943931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4573822309851283899925241 3430366732388462924943931)
          ·
            refine ⟨5145550098582694387415897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430366732388462924943931 5145550098582694387415897)
            ·
              refine ⟨3859162573937020790561923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5145550098582694387415897 3859162573937020790561923)
              ·
                refine ⟨5788743860905531185842885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3859162573937020790561923 5788743860905531185842885)
                ·
                  refine ⟨1085389473919787097345541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5788743860905531185842885 1085389473919787097345541)
                  ·
                    refine ⟨203510526359960080752289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085389473919787097345541 203510526359960080752289)
                    ·
                      rfl

theorem cell23_1189006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_1189006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189006 prefixEnd_1189006 := by exact prefixLift 1189006
  have htrace : WordTrace (prefixWord ++ tailWord_1189006) baseStart_1189006 baseEnd_1189006 := by
    simpa [prefixWord, tailWord_1189006, baseEnd_1189006] using wordTrace_append hprefix tailTrace_1189006
  have hstable : (prefixWord ++ tailWord_1189006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189006).length < 2 ^ (prefixWord ++ tailWord_1189006).sum := by decide
  have hdescent : baseEnd_1189006 < baseStart_1189006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189023 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 2, 4]
def baseStart_1189023 : Nat := 118140960795 + 1189023 * 2 ^ 59
def prefixEnd_1189023 : Nat := 4983230072969 + 3 ^ 40 * 1189023 * 2
def baseEnd_1189023 : Nat := 203513436083668891914763

theorem tailTrace_1189023 : CollatzResearch.WordTrace tailWord_1189023 prefixEnd_1189023 203513436083668891914763 := by
  unfold tailWord_1189023
  simp only [CollatzResearch.WordTrace]
  refine ⟨43367231571380214806363723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28911487714253476537575815 43367231571380214806363723)
  ·
    refine ⟨65050847357070322209545585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43367231571380214806363723 65050847357070322209545585)
    ·
      refine ⟨48788135517802741657159189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65050847357070322209545585 48788135517802741657159189)
      ·
        refine ⟨2286943852397003515179337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48788135517802741657159189 2286943852397003515179337)
        ·
          refine ⟨1715207889297752636384503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2286943852397003515179337 1715207889297752636384503)
          ·
            refine ⟨2572811833946628954576755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715207889297752636384503 2572811833946628954576755)
            ·
              refine ⟨3859217750919943431865133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572811833946628954576755 3859217750919943431865133)
              ·
                refine ⟨1447206656594978786949425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859217750919943431865133 1447206656594978786949425)
                ·
                  refine ⟨1085404992446234090212069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1447206656594978786949425 1085404992446234090212069)
                  ·
                    refine ⟨203513436083668891914763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085404992446234090212069 203513436083668891914763)
                    ·
                      rfl

theorem cell23_1189023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_1189023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189023 prefixEnd_1189023 := by exact prefixLift 1189023
  have htrace : WordTrace (prefixWord ++ tailWord_1189023) baseStart_1189023 baseEnd_1189023 := by
    simpa [prefixWord, tailWord_1189023, baseEnd_1189023] using wordTrace_append hprefix tailTrace_1189023
  have hstable : (prefixWord ++ tailWord_1189023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189023).length < 2 ^ (prefixWord ++ tailWord_1189023).sum := by decide
  have hdescent : baseEnd_1189023 < baseStart_1189023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189058 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_1189058 : Nat := 118140960795 + 1189058 * 2 ^ 59
def prefixEnd_1189058 : Nat := 4983230072969 + 3 ^ 40 * 1189058 * 2
def baseEnd_1189058 : Nat := 610558280073914038806629

theorem tailTrace_1189058 : CollatzResearch.WordTrace tailWord_1189058 prefixEnd_1189058 610558280073914038806629 := by
  unfold tailWord_1189058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10842127031563353945971957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28912338750835610522591885 10842127031563353945971957)
  ·
    refine ⟨1016449409209064432434871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10842127031563353945971957 1016449409209064432434871)
    ·
      refine ⟨1524674113813596648652307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016449409209064432434871 1524674113813596648652307)
      ·
        refine ⟨2287011170720394972978461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524674113813596648652307 2287011170720394972978461)
        ·
          refine ⟨857629189020148114866923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2287011170720394972978461 857629189020148114866923)
          ·
            refine ⟨1286443783530222172300385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857629189020148114866923 1286443783530222172300385)
            ·
              refine ⟨964832837647666629225289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286443783530222172300385 964832837647666629225289)
              ·
                refine ⟨723624628235749971918967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964832837647666629225289 723624628235749971918967)
                ·
                  refine ⟨1085436942353624957878451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723624628235749971918967 1085436942353624957878451)
                  ·
                    refine ⟨1628155413530437436817677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1085436942353624957878451 1628155413530437436817677)
                    ·
                      refine ⟨610558280073914038806629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1628155413530437436817677 610558280073914038806629)
                      ·
                        rfl

theorem cell23_1189058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_1189058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189058 prefixEnd_1189058 := by exact prefixLift 1189058
  have htrace : WordTrace (prefixWord ++ tailWord_1189058) baseStart_1189058 baseEnd_1189058 := by
    simpa [prefixWord, tailWord_1189058, baseEnd_1189058] using wordTrace_append hprefix tailTrace_1189058
  have hstable : (prefixWord ++ tailWord_1189058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189058).length < 2 ^ (prefixWord ++ tailWord_1189058).sum := by decide
  have hdescent : baseEnd_1189058 < baseStart_1189058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189156 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_1189156 : Nat := 118140960795 + 1189156 * 2 ^ 59
def prefixEnd_1189156 : Nat := 4983230072969 + 3 ^ 40 * 1189156 * 2
def baseEnd_1189156 : Nat := 203536200392684885127059

theorem tailTrace_1189156 : CollatzResearch.WordTrace tailWord_1189156 prefixEnd_1189156 203536200392684885127059 := by
  unfold tailWord_1189156
  simp only [CollatzResearch.WordTrace]
  refine ⟨21686041239949189260477661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28914721653265585680636881 21686041239949189260477661)
  ·
    refine ⟨8132265464980945972679123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21686041239949189260477661 8132265464980945972679123)
    ·
      refine ⟨12198398197471418959018685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8132265464980945972679123 12198398197471418959018685)
      ·
        refine ⟨4574399324051782109632007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12198398197471418959018685 4574399324051782109632007)
        ·
          refine ⟨6861598986077673164448011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574399324051782109632007 6861598986077673164448011)
          ·
            refine ⟨10292398479116509746672017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861598986077673164448011 10292398479116509746672017)
            ·
              refine ⟨7719298859337382310004013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10292398479116509746672017 7719298859337382310004013)
              ·
                refine ⟨2894737072251518366251505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7719298859337382310004013 2894737072251518366251505)
                ·
                  refine ⟨2171052804188638774688629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2894737072251518366251505 2171052804188638774688629)
                  ·
                    refine ⟨203536200392684885127059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2171052804188638774688629 203536200392684885127059)
                    ·
                      rfl

theorem cell23_1189156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_1189156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189156 prefixEnd_1189156 := by exact prefixLift 1189156
  have htrace : WordTrace (prefixWord ++ tailWord_1189156) baseStart_1189156 baseEnd_1189156 := by
    simpa [prefixWord, tailWord_1189156, baseEnd_1189156] using wordTrace_append hprefix tailTrace_1189156
  have hstable : (prefixWord ++ tailWord_1189156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189156).length < 2 ^ (prefixWord ++ tailWord_1189156).sum := by decide
  have hdescent : baseEnd_1189156 < baseStart_1189156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189160 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 5]
def baseStart_1189160 : Nat := 118140960795 + 1189160 * 2 ^ 59
def prefixEnd_1189160 : Nat := 4983230072969 + 3 ^ 40 * 1189160 * 2
def baseEnd_1189160 : Nat := 67845628344519182192351

theorem tailTrace_1189160 : CollatzResearch.WordTrace tailWord_1189160 prefixEnd_1189160 67845628344519182192351 := by
  unfold tailWord_1189160
  simp only [CollatzResearch.WordTrace]
  refine ⟨21686114185941943602050467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28914818914589258136067289 21686114185941943602050467)
  ·
    refine ⟨32529171278912915403075701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21686114185941943602050467 32529171278912915403075701)
    ·
      refine ⟨3049609807398085819038347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32529171278912915403075701 3049609807398085819038347)
      ·
        refine ⟨4574414711097128728557521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049609807398085819038347 4574414711097128728557521)
        ·
          refine ⟨3430811033322846546418141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4574414711097128728557521 3430811033322846546418141)
          ·
            refine ⟨1286554137496067454906803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3430811033322846546418141 1286554137496067454906803)
            ·
              refine ⟨1929831206244101182360205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286554137496067454906803 1929831206244101182360205)
              ·
                refine ⟨723686702341537943385077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929831206244101182360205 723686702341537943385077)
                ·
                  refine ⟨67845628344519182192351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723686702341537943385077 67845628344519182192351)
                  ·
                    rfl

theorem cell23_1189160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 5].length) (baseStart_1189160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189160 prefixEnd_1189160 := by exact prefixLift 1189160
  have htrace : WordTrace (prefixWord ++ tailWord_1189160) baseStart_1189160 baseEnd_1189160 := by
    simpa [prefixWord, tailWord_1189160, baseEnd_1189160] using wordTrace_append hprefix tailTrace_1189160
  have hstable : (prefixWord ++ tailWord_1189160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189160).length < 2 ^ (prefixWord ++ tailWord_1189160).sum := by decide
  have hdescent : baseEnd_1189160 < baseStart_1189160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189189 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_1189189 : Nat := 118140960795 + 1189189 * 2 ^ 59
def prefixEnd_1189189 : Nat := 4983230072969 + 3 ^ 40 * 1189189 * 2
def baseEnd_1189189 : Nat := 610625546039653026268525

theorem tailTrace_1189189 : CollatzResearch.WordTrace tailWord_1189189 prefixEnd_1189189 610625546039653026268525 := by
  unfold tailWord_1189189
  simp only [CollatzResearch.WordTrace]
  refine ⟨43373286088778825156906621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28915524059185883437937747 43373286088778825156906621)
  ·
    refine ⟨16264982283292059433839983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43373286088778825156906621 16264982283292059433839983)
    ·
      refine ⟨24397473424938089150759975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16264982283292059433839983 24397473424938089150759975)
      ·
        refine ⟨36596210137407133726139963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24397473424938089150759975 36596210137407133726139963)
        ·
          refine ⟨54894315206110700589209945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36596210137407133726139963 54894315206110700589209945)
          ·
            refine ⟨41170736404583025441907459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54894315206110700589209945 41170736404583025441907459)
            ·
              refine ⟨61756104606874538162861189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41170736404583025441907459 61756104606874538162861189)
              ·
                refine ⟨11579269613788975905536473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61756104606874538162861189 11579269613788975905536473)
                ·
                  refine ⟨8684452210341731929152355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11579269613788975905536473 8684452210341731929152355)
                  ·
                    refine ⟨13026678315512597893728533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8684452210341731929152355 13026678315512597893728533)
                    ·
                      refine ⟨610625546039653026268525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13026678315512597893728533 610625546039653026268525)
                      ·
                        rfl

theorem cell23_1189189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_1189189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189189 prefixEnd_1189189 := by exact prefixLift 1189189
  have htrace : WordTrace (prefixWord ++ tailWord_1189189) baseStart_1189189 baseEnd_1189189 := by
    simpa [prefixWord, tailWord_1189189, baseEnd_1189189] using wordTrace_append hprefix tailTrace_1189189
  have hstable : (prefixWord ++ tailWord_1189189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189189).length < 2 ^ (prefixWord ++ tailWord_1189189).sum := by decide
  have hdescent : baseEnd_1189189 < baseStart_1189189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189237 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1189237 : Nat := 118140960795 + 1189237 * 2 ^ 59
def prefixEnd_1189237 : Nat := 4983230072969 + 3 ^ 40 * 1189237 * 2
def baseEnd_1189237 : Nat := 203550064370356279489435

theorem tailTrace_1189237 : CollatzResearch.WordTrace tailWord_1189237 prefixEnd_1189237 203550064370356279489435 := by
  unfold tailWord_1189237
  simp only [CollatzResearch.WordTrace]
  refine ⟨43375036792604929354653965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28916691195069952903102643 43375036792604929354653965)
  ·
    refine ⟨16265638797226848507995237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43375036792604929354653965 16265638797226848507995237)
    ·
      refine ⟨3049807274480034095249107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16265638797226848507995237 3049807274480034095249107)
      ·
        refine ⟨4574710911720051142873661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049807274480034095249107 4574710911720051142873661)
        ·
          refine ⟨1715516591895019178577623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4574710911720051142873661 1715516591895019178577623)
          ·
            refine ⟨2573274887842528767866435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715516591895019178577623 2573274887842528767866435)
            ·
              refine ⟨3859912331763793151799653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573274887842528767866435 3859912331763793151799653)
              ·
                refine ⟨723733562205711215962435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3859912331763793151799653 723733562205711215962435)
                ·
                  refine ⟨1085600343308566823943653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723733562205711215962435 1085600343308566823943653)
                  ·
                    refine ⟨203550064370356279489435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085600343308566823943653 203550064370356279489435)
                    ·
                      rfl

theorem cell23_1189237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1189237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189237 prefixEnd_1189237 := by exact prefixLift 1189237
  have htrace : WordTrace (prefixWord ++ tailWord_1189237) baseStart_1189237 baseEnd_1189237 := by
    simpa [prefixWord, tailWord_1189237, baseEnd_1189237] using wordTrace_append hprefix tailTrace_1189237
  have hstable : (prefixWord ++ tailWord_1189237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189237).length < 2 ^ (prefixWord ++ tailWord_1189237).sum := by decide
  have hdescent : baseEnd_1189237 < baseStart_1189237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189243 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 3]
def baseStart_1189243 : Nat := 118140960795 + 1189243 * 2 ^ 59
def prefixEnd_1189243 : Nat := 4983230072969 + 3 ^ 40 * 1189243 * 2
def baseEnd_1189243 : Nat := 610653273994995814993277

theorem tailTrace_1189243 : CollatzResearch.WordTrace tailWord_1189243 prefixEnd_1189243 610653273994995814993277 := by
  unfold tailWord_1189243
  simp only [CollatzResearch.WordTrace]
  refine ⟨43375255630583192379372383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28916837087055461586248255 43375255630583192379372383)
  ·
    refine ⟨65062883445874788569058575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43375255630583192379372383 65062883445874788569058575)
    ·
      refine ⟨97594325168812182853587863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65062883445874788569058575 97594325168812182853587863)
      ·
        refine ⟨146391487753218274280381795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97594325168812182853587863 146391487753218274280381795)
        ·
          refine ⟨219587231629827411420572693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146391487753218274280381795 219587231629827411420572693)
          ·
            refine ⟨10293151482648159910339345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219587231629827411420572693 10293151482648159910339345)
            ·
              refine ⟨7719863611986119932754509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10293151482648159910339345 7719863611986119932754509)
              ·
                refine ⟨2894948854494794974782941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7719863611986119932754509 2894948854494794974782941)
                ·
                  refine ⟨1085605820435548115543603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2894948854494794974782941 1085605820435548115543603)
                  ·
                    refine ⟨1628408730653322173315405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1085605820435548115543603 1628408730653322173315405)
                    ·
                      refine ⟨610653273994995814993277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1628408730653322173315405 610653273994995814993277)
                      ·
                        rfl

theorem cell23_1189243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 3].length) (baseStart_1189243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189243 prefixEnd_1189243 := by exact prefixLift 1189243
  have htrace : WordTrace (prefixWord ++ tailWord_1189243) baseStart_1189243 baseEnd_1189243 := by
    simpa [prefixWord, tailWord_1189243, baseEnd_1189243] using wordTrace_append hprefix tailTrace_1189243
  have hstable : (prefixWord ++ tailWord_1189243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189243).length < 2 ^ (prefixWord ++ tailWord_1189243).sum := by decide
  have hdescent : baseEnd_1189243 < baseStart_1189243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189250 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1189250 : Nat := 118140960795 + 1189250 * 2 ^ 59
def prefixEnd_1189250 : Nat := 4983230072969 + 3 ^ 40 * 1189250 * 2
def baseEnd_1189250 : Nat := 67850763151064143067305

theorem tailTrace_1189250 : CollatzResearch.WordTrace tailWord_1189250 prefixEnd_1189250 67850763151064143067305 := by
  unfold tailWord_1189250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10843877735389458143719301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28917007294371888383251469 10843877735389458143719301)
  ·
    refine ⟨2033227075385523401947369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10843877735389458143719301 2033227075385523401947369)
    ·
      refine ⟨1524920306539142551460527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2033227075385523401947369 1524920306539142551460527)
      ·
        refine ⟨2287380459808713827190791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524920306539142551460527 2287380459808713827190791)
        ·
          refine ⟨3431070689713070740786187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287380459808713827190791 3431070689713070740786187)
          ·
            refine ⟨5146606034569606111179281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431070689713070740786187 5146606034569606111179281)
            ·
              refine ⟨3859954525927204583384461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146606034569606111179281 3859954525927204583384461)
              ·
                refine ⟨1447482947222701718769173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859954525927204583384461 1447482947222701718769173)
                ·
                  refine ⟨67850763151064143067305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1447482947222701718769173 67850763151064143067305)
                  ·
                    rfl

theorem cell23_1189250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1189250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189250 prefixEnd_1189250 := by exact prefixLift 1189250
  have htrace : WordTrace (prefixWord ++ tailWord_1189250) baseStart_1189250 baseEnd_1189250 := by
    simpa [prefixWord, tailWord_1189250, baseEnd_1189250] using wordTrace_append hprefix tailTrace_1189250
  have hstable : (prefixWord ++ tailWord_1189250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189250).length < 2 ^ (prefixWord ++ tailWord_1189250).sum := by decide
  have hdescent : baseEnd_1189250 < baseStart_1189250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189253 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 4, 3, 2]
def baseStart_1189253 : Nat := 118140960795 + 1189253 * 2 ^ 59
def prefixEnd_1189253 : Nat := 4983230072969 + 3 ^ 40 * 1189253 * 2
def baseEnd_1189253 : Nat := 610658408801540775868231

theorem tailTrace_1189253 : CollatzResearch.WordTrace tailWord_1189253 prefixEnd_1189253 610658408801540775868231 := by
  unfold tailWord_1189253
  simp only [CollatzResearch.WordTrace]
  refine ⟨43375620360546964087236413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28917080240364642724824275 43375620360546964087236413)
  ·
    refine ⟨16265857635205111532713655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43375620360546964087236413 16265857635205111532713655)
    ·
      refine ⟨24398786452807667299070483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16265857635205111532713655 24398786452807667299070483)
      ·
        refine ⟨36598179679211500948605725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24398786452807667299070483 36598179679211500948605725)
        ·
          refine ⟨13724317379704312855727147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36598179679211500948605725 13724317379704312855727147)
          ·
            refine ⟨20586476069556469283590721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13724317379704312855727147 20586476069556469283590721)
            ·
              refine ⟨15439857052167351962693041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20586476069556469283590721 15439857052167351962693041)
              ·
                refine ⟨11579892789125513972019781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15439857052167351962693041 11579892789125513972019781)
                ·
                  refine ⟨2171229897961033869753709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11579892789125513972019781 2171229897961033869753709)
                  ·
                    refine ⟨814211211735387701157641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171229897961033869753709 814211211735387701157641)
                    ·
                      refine ⟨610658408801540775868231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814211211735387701157641 610658408801540775868231)
                      ·
                        rfl

theorem cell23_1189253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_1189253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189253 prefixEnd_1189253 := by exact prefixLift 1189253
  have htrace : WordTrace (prefixWord ++ tailWord_1189253) baseStart_1189253 baseEnd_1189253 := by
    simpa [prefixWord, tailWord_1189253, baseEnd_1189253] using wordTrace_append hprefix tailTrace_1189253
  have hstable : (prefixWord ++ tailWord_1189253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189253).length < 2 ^ (prefixWord ++ tailWord_1189253).sum := by decide
  have hdescent : baseEnd_1189253 < baseStart_1189253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189277 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_1189277 : Nat := 118140960795 + 1189277 * 2 ^ 59
def prefixEnd_1189277 : Nat := 4983230072969 + 3 ^ 40 * 1189277 * 2
def baseEnd_1189277 : Nat := 610670732337248681968121

theorem tailTrace_1189277 : CollatzResearch.WordTrace tailWord_1189277 prefixEnd_1189277 610670732337248681968121 := by
  unfold tailWord_1189277
  simp only [CollatzResearch.WordTrace]
  refine ⟨43376495712460016186110085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28917663808306677457406723 43376495712460016186110085)
  ·
    refine ⟨8133092946086253034895641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43376495712460016186110085 8133092946086253034895641)
    ·
      refine ⟨6099819709564689776171731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8133092946086253034895641 6099819709564689776171731)
      ·
        refine ⟨9149729564347034664257597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6099819709564689776171731 9149729564347034664257597)
        ·
          refine ⟨3431148586630137999096599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9149729564347034664257597 3431148586630137999096599)
          ·
            refine ⟨5146722879945206998644899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431148586630137999096599 5146722879945206998644899)
            ·
              refine ⟨7720084319917810497967349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146722879945206998644899 7720084319917810497967349)
              ·
                refine ⟨723757904992294734184439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7720084319917810497967349 723757904992294734184439)
                ·
                  refine ⟨1085636857488442101276659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723757904992294734184439 1085636857488442101276659)
                  ·
                    refine ⟨1628455286232663151914989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1085636857488442101276659 1628455286232663151914989)
                    ·
                      refine ⟨610670732337248681968121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1628455286232663151914989 610670732337248681968121)
                      ·
                        rfl

theorem cell23_1189277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_1189277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189277 prefixEnd_1189277 := by exact prefixLift 1189277
  have htrace : WordTrace (prefixWord ++ tailWord_1189277) baseStart_1189277 baseEnd_1189277 := by
    simpa [prefixWord, tailWord_1189277, baseEnd_1189277] using wordTrace_append hprefix tailTrace_1189277
  have hstable : (prefixWord ++ tailWord_1189277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189277).length < 2 ^ (prefixWord ++ tailWord_1189277).sum := by decide
  have hdescent : baseEnd_1189277 < baseStart_1189277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189283 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 4]
def baseStart_1189283 : Nat := 118140960795 + 1189283 * 2 ^ 59
def prefixEnd_1189283 : Nat := 4983230072969 + 3 ^ 40 * 1189283 * 2
def baseEnd_1189283 : Nat := 610673813221175658493093

theorem tailTrace_1189283 : CollatzResearch.WordTrace tailWord_1189283 prefixEnd_1189283 610673813221175658493093 := by
  unfold tailWord_1189283
  simp only [CollatzResearch.WordTrace]
  refine ⟨43376714550438279210828503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28917809700292186140552335 43376714550438279210828503)
  ·
    refine ⟨65065071825657418816242755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43376714550438279210828503 65065071825657418816242755)
    ·
      refine ⟨97597607738486128224364133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65065071825657418816242755 97597607738486128224364133)
      ·
        refine ⟨18299551450966149042068275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97597607738486128224364133 18299551450966149042068275)
        ·
          refine ⟨27449327176449223563102413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18299551450966149042068275 27449327176449223563102413)
          ·
            refine ⟨10293497691168458836163405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27449327176449223563102413 10293497691168458836163405)
            ·
              refine ⟨3860061634188172063561277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10293497691168458836163405 3860061634188172063561277)
              ·
                refine ⟨1447523112820564523835479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3860061634188172063561277 1447523112820564523835479)
                ·
                  refine ⟨2171284669230846785753219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447523112820564523835479 2171284669230846785753219)
                  ·
                    refine ⟨3256927003846270178629829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2171284669230846785753219 3256927003846270178629829)
                    ·
                      refine ⟨610673813221175658493093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3256927003846270178629829 610673813221175658493093)
                      ·
                        rfl

theorem cell23_1189283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_1189283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189283 prefixEnd_1189283 := by exact prefixLift 1189283
  have htrace : WordTrace (prefixWord ++ tailWord_1189283) baseStart_1189283 baseEnd_1189283 := by
    simpa [prefixWord, tailWord_1189283, baseEnd_1189283] using wordTrace_append hprefix tailTrace_1189283
  have hstable : (prefixWord ++ tailWord_1189283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189283).length < 2 ^ (prefixWord ++ tailWord_1189283).sum := by decide
  have hdescent : baseEnd_1189283 < baseStart_1189283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189320 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_1189320 : Nat := 118140960795 + 1189320 * 2 ^ 59
def prefixEnd_1189320 : Nat := 4983230072969 + 3 ^ 40 * 1189320 * 2
def baseEnd_1189320 : Nat := 610692812005392013730423

theorem tailTrace_1189320 : CollatzResearch.WordTrace tailWord_1189320 prefixEnd_1189320 610692812005392013730423 := by
  unfold tailWord_1189320
  simp only [CollatzResearch.WordTrace]
  refine ⟨21689032025652117264962707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28918709367536156353283609 21689032025652117264962707)
  ·
    refine ⟨32533548038478175897444061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21689032025652117264962707 32533548038478175897444061)
    ·
      refine ⟨12200080514429315961541523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32533548038478175897444061 12200080514429315961541523)
      ·
        refine ⟨18300120771643973942312285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12200080514429315961541523 18300120771643973942312285)
        ·
          refine ⟨6862545289366490228367107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18300120771643973942312285 6862545289366490228367107)
          ·
            refine ⟨10293817934049735342550661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862545289366490228367107 10293817934049735342550661)
            ·
              refine ⟨1930090862634325376728249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10293817934049735342550661 1930090862634325376728249)
              ·
                refine ⟨1447568146975744032546187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930090862634325376728249 1447568146975744032546187)
                ·
                  refine ⟨2171352220463616048819281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447568146975744032546187 2171352220463616048819281)
                  ·
                    refine ⟨1628514165347712036614461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171352220463616048819281 1628514165347712036614461)
                    ·
                      refine ⟨610692812005392013730423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1628514165347712036614461 610692812005392013730423)
                      ·
                        rfl

theorem cell23_1189320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_1189320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189320 prefixEnd_1189320 := by exact prefixLift 1189320
  have htrace : WordTrace (prefixWord ++ tailWord_1189320) baseStart_1189320 baseEnd_1189320 := by
    simpa [prefixWord, tailWord_1189320, baseEnd_1189320] using wordTrace_append hprefix tailTrace_1189320
  have hstable : (prefixWord ++ tailWord_1189320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189320).length < 2 ^ (prefixWord ++ tailWord_1189320).sum := by decide
  have hdescent : baseEnd_1189320 < baseStart_1189320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189333 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1189333 : Nat := 118140960795 + 1189333 * 2 ^ 59
def prefixEnd_1189333 : Nat := 4983230072969 + 3 ^ 40 * 1189333 * 2
def baseEnd_1189333 : Nat := 610699487253900462867863

theorem tailTrace_1189333 : CollatzResearch.WordTrace tailWord_1189333 prefixEnd_1189333 610699487253900462867863 := by
  unfold tailWord_1189333
  simp only [CollatzResearch.WordTrace]
  refine ⟨43378538200257137750148653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28919025466838091833432435 43378538200257137750148653)
  ·
    refine ⟨16266951825096426656305745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43378538200257137750148653 16266951825096426656305745)
    ·
      refine ⟨12200213868822319992229309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16266951825096426656305745 12200213868822319992229309)
      ·
        refine ⟨4575080200808369997085991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12200213868822319992229309 4575080200808369997085991)
        ·
          refine ⟨6862620301212554995628987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575080200808369997085991 6862620301212554995628987)
          ·
            refine ⟨10293930451818832493443481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862620301212554995628987 10293930451818832493443481)
            ·
              refine ⟨7720447838864124370082611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10293930451818832493443481 7720447838864124370082611)
              ·
                refine ⟨11580671758296186555123917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7720447838864124370082611 11580671758296186555123917)
                ·
                  refine ⟨4342751909361069958171469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11580671758296186555123917 4342751909361069958171469)
                  ·
                    refine ⟨1628531966010401234314301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4342751909361069958171469 1628531966010401234314301)
                    ·
                      refine ⟨610699487253900462867863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1628531966010401234314301 610699487253900462867863)
                      ·
                        rfl

theorem cell23_1189333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1189333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189333 prefixEnd_1189333 := by exact prefixLift 1189333
  have htrace : WordTrace (prefixWord ++ tailWord_1189333) baseStart_1189333 baseEnd_1189333 := by
    simpa [prefixWord, tailWord_1189333, baseEnd_1189333] using wordTrace_append hprefix tailTrace_1189333
  have hstable : (prefixWord ++ tailWord_1189333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189333).length < 2 ^ (prefixWord ++ tailWord_1189333).sum := by decide
  have hdescent : baseEnd_1189333 < baseStart_1189333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189351 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1189351 : Nat := 118140960795 + 1189351 * 2 ^ 59
def prefixEnd_1189351 : Nat := 4983230072969 + 3 ^ 40 * 1189351 * 2
def baseEnd_1189351 : Nat := 610708729905681392442781

theorem tailTrace_1189351 : CollatzResearch.WordTrace tailWord_1189351 prefixEnd_1189351 610708729905681392442781 := by
  unfold tailWord_1189351
  simp only [CollatzResearch.WordTrace]
  refine ⟨43379194714191926824303907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28919463142794617882869271 43379194714191926824303907)
  ·
    refine ⟨65068792071287890236455861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43379194714191926824303907 65068792071287890236455861)
    ·
      refine ⟨6100199256683239709667737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65068792071287890236455861 6100199256683239709667737)
      ·
        refine ⟨4575149442512429782250803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6100199256683239709667737 4575149442512429782250803)
        ·
          refine ⟨6862724163768644673376205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4575149442512429782250803 6862724163768644673376205)
          ·
            refine ⟨2573521561413241752516077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6862724163768644673376205 2573521561413241752516077)
            ·
              refine ⟨965070585529965657193529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2573521561413241752516077 965070585529965657193529)
              ·
                refine ⟨723802939147474242895147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965070585529965657193529 723802939147474242895147)
                ·
                  refine ⟨1085704408721211364342721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723802939147474242895147 1085704408721211364342721)
                  ·
                    refine ⟨814278306540908523257041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1085704408721211364342721 814278306540908523257041)
                    ·
                      refine ⟨610708729905681392442781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814278306540908523257041 610708729905681392442781)
                      ·
                        rfl

theorem cell23_1189351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1189351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189351 prefixEnd_1189351 := by exact prefixLift 1189351
  have htrace : WordTrace (prefixWord ++ tailWord_1189351) baseStart_1189351 baseEnd_1189351 := by
    simpa [prefixWord, tailWord_1189351, baseEnd_1189351] using wordTrace_append hprefix tailTrace_1189351
  have hstable : (prefixWord ++ tailWord_1189351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189351).length < 2 ^ (prefixWord ++ tailWord_1189351).sum := by decide
  have hdescent : baseEnd_1189351 < baseStart_1189351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189377 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_1189377 : Nat := 118140960795 + 1189377 * 2 ^ 59
def prefixEnd_1189377 : Nat := 4983230072969 + 3 ^ 40 * 1189377 * 2
def baseEnd_1189377 : Nat := 610722080402698290717661

theorem tailTrace_1189377 : CollatzResearch.WordTrace tailWord_1189377 prefixEnd_1189377 610722080402698290717661 := by
  unfold tailWord_1189377
  simp only [CollatzResearch.WordTrace]
  refine ⟨43380143012097733264750385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28920095341398488843166923 43380143012097733264750385)
  ·
    refine ⟨32535107259073299948562789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43380143012097733264750385 32535107259073299948562789)
    ·
      refine ⟨6100332611076243740355523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32535107259073299948562789 6100332611076243740355523)
      ·
        refine ⟨9150498916614365610533285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6100332611076243740355523 9150498916614365610533285)
        ·
          refine ⟨1715718546865193551974991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9150498916614365610533285 1715718546865193551974991)
          ·
            refine ⟨2573577820297790327962487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715718546865193551974991 2573577820297790327962487)
            ·
              refine ⟨3860366730446685491943731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573577820297790327962487 3860366730446685491943731)
              ·
                refine ⟨5790550095670028237915597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3860366730446685491943731 5790550095670028237915597)
                ·
                  refine ⟨2171456285876260589218349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5790550095670028237915597 2171456285876260589218349)
                  ·
                    refine ⟨814296107203597720956881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171456285876260589218349 814296107203597720956881)
                    ·
                      refine ⟨610722080402698290717661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814296107203597720956881 610722080402698290717661)
                      ·
                        rfl

theorem cell23_1189377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_1189377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189377 prefixEnd_1189377 := by exact prefixLift 1189377
  have htrace : WordTrace (prefixWord ++ tailWord_1189377) baseStart_1189377 baseEnd_1189377 := by
    simpa [prefixWord, tailWord_1189377, baseEnd_1189377] using wordTrace_append hprefix tailTrace_1189377
  have hstable : (prefixWord ++ tailWord_1189377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189377).length < 2 ^ (prefixWord ++ tailWord_1189377).sum := by decide
  have hdescent : baseEnd_1189377 < baseStart_1189377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189407 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 2, 2, 2]
def baseStart_1189407 : Nat := 118140960795 + 1189407 * 2 ^ 59
def prefixEnd_1189407 : Nat := 4983230072969 + 3 ^ 40 * 1189407 * 2
def baseEnd_1189407 : Nat := 610737484822333173342523

theorem tailTrace_1189407 : CollatzResearch.WordTrace tailWord_1189407 prefixEnd_1189407 610737484822333173342523 := by
  unfold tailWord_1189407
  simp only [CollatzResearch.WordTrace]
  refine ⟨43381237201989048388342475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28920824801326032258894983 43381237201989048388342475)
  ·
    refine ⟨65071855802983572582513713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43381237201989048388342475 65071855802983572582513713)
    ·
      refine ⟨48803891852237679436885285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65071855802983572582513713 48803891852237679436885285)
      ·
        refine ⟨9150729722294564894415991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48803891852237679436885285 9150729722294564894415991)
        ·
          refine ⟨13726094583441847341623987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9150729722294564894415991 13726094583441847341623987)
          ·
            refine ⟨20589141875162771012435981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13726094583441847341623987 20589141875162771012435981)
            ·
              refine ⟨7720928203186039129663493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20589141875162771012435981 7720928203186039129663493)
              ·
                refine ⟨1447674038097382336811905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7720928203186039129663493 1447674038097382336811905)
                ·
                  refine ⟨1085755528573036752608929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1447674038097382336811905 1085755528573036752608929)
                  ·
                    refine ⟨814316646429777564456697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1085755528573036752608929 814316646429777564456697)
                    ·
                      refine ⟨610737484822333173342523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814316646429777564456697 610737484822333173342523)
                      ·
                        rfl

theorem cell23_1189407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_1189407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189407 prefixEnd_1189407 := by exact prefixLift 1189407
  have htrace : WordTrace (prefixWord ++ tailWord_1189407) baseStart_1189407 baseEnd_1189407 := by
    simpa [prefixWord, tailWord_1189407, baseEnd_1189407] using wordTrace_append hprefix tailTrace_1189407
  have hstable : (prefixWord ++ tailWord_1189407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189407).length < 2 ^ (prefixWord ++ tailWord_1189407).sum := by decide
  have hdescent : baseEnd_1189407 < baseStart_1189407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189447 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 5]
def baseStart_1189447 : Nat := 118140960795 + 1189447 * 2 ^ 59
def prefixEnd_1189447 : Nat := 4983230072969 + 3 ^ 40 * 1189447 * 2
def baseEnd_1189447 : Nat := 67862002672057001871371

theorem tailTrace_1189447 : CollatzResearch.WordTrace tailWord_1189447 prefixEnd_1189447 67862002672057001871371 := by
  unfold tailWord_1189447
  simp only [CollatzResearch.WordTrace]
  refine ⟨43382696121844135219798595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28921797414562756813199063 43382696121844135219798595)
  ·
    refine ⟨65074044182766202829697893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43382696121844135219798595 65074044182766202829697893)
    ·
      refine ⟨12201383284268663030568355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65074044182766202829697893 12201383284268663030568355)
      ·
        refine ⟨18302074926402994545852533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12201383284268663030568355 18302074926402994545852533)
        ·
          refine ⟨1715819524350280738673675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18302074926402994545852533 1715819524350280738673675)
          ·
            refine ⟨2573729286525421108010513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715819524350280738673675 2573729286525421108010513)
            ·
              refine ⟨1930296964894065831007885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573729286525421108010513 1930296964894065831007885)
              ·
                refine ⟨723861361835274686627957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1930296964894065831007885 723861361835274686627957)
                ·
                  refine ⟨67862002672057001871371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 723861361835274686627957 67862002672057001871371)
                  ·
                    rfl

theorem cell23_1189447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 5].length) (baseStart_1189447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189447 prefixEnd_1189447 := by exact prefixLift 1189447
  have htrace : WordTrace (prefixWord ++ tailWord_1189447) baseStart_1189447 baseEnd_1189447 := by
    simpa [prefixWord, tailWord_1189447, baseEnd_1189447] using wordTrace_append hprefix tailTrace_1189447
  have hstable : (prefixWord ++ tailWord_1189447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189447).length < 2 ^ (prefixWord ++ tailWord_1189447).sum := by decide
  have hdescent : baseEnd_1189447 < baseStart_1189447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189480 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1189480 : Nat := 118140960795 + 1189480 * 2 ^ 59
def prefixEnd_1189480 : Nat := 4983230072969 + 3 ^ 40 * 1189480 * 2
def baseEnd_1189480 : Nat := 610774968910111387729687

theorem tailTrace_1189480 : CollatzResearch.WordTrace tailWord_1189480 prefixEnd_1189480 610774968910111387729687 := by
  unfold tailWord_1189480
  simp only [CollatzResearch.WordTrace]
  refine ⟨21691949865362290927874947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28922599820483054570499929 21691949865362290927874947)
  ·
    refine ⟨32537924798043436391812421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21691949865362290927874947 32537924798043436391812421)
    ·
      refine ⟨6100860899633144323464829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32537924798043436391812421 6100860899633144323464829)
      ·
        refine ⟨2287822837362429121299311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6100860899633144323464829 2287822837362429121299311)
        ·
          refine ⟨3431734256043643681948967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287822837362429121299311 3431734256043643681948967)
          ·
            refine ⟨5147601384065465522923451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431734256043643681948967 5147601384065465522923451)
            ·
              refine ⟨7721402076098198284385177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5147601384065465522923451 7721402076098198284385177)
              ·
                refine ⟨5791051557073648713288883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7721402076098198284385177 5791051557073648713288883)
                ·
                  refine ⟨8686577335610473069933325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5791051557073648713288883 8686577335610473069933325)
                  ·
                    refine ⟨3257466500853927401224997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8686577335610473069933325 3257466500853927401224997)
                    ·
                      refine ⟨610774968910111387729687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3257466500853927401224997 610774968910111387729687)
                      ·
                        rfl

theorem cell23_1189480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1189480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189480 prefixEnd_1189480 := by exact prefixLift 1189480
  have htrace : WordTrace (prefixWord ++ tailWord_1189480) baseStart_1189480 baseEnd_1189480 := by
    simpa [prefixWord, tailWord_1189480, baseEnd_1189480] using wordTrace_append hprefix tailTrace_1189480
  have hstable : (prefixWord ++ tailWord_1189480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189480).length < 2 ^ (prefixWord ++ tailWord_1189480).sum := by decide
  have hdescent : baseEnd_1189480 < baseStart_1189480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189500 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_1189500 : Nat := 118140960795 + 1189500 * 2 ^ 59
def prefixEnd_1189500 : Nat := 4983230072969 + 3 ^ 40 * 1189500 * 2
def baseEnd_1189500 : Nat := 610785238523201309479595

theorem tailTrace_1189500 : CollatzResearch.WordTrace tailWord_1189500 prefixEnd_1189500 610785238523201309479595 := by
  unfold tailWord_1189500
  simp only [CollatzResearch.WordTrace]
  refine ⟨21692314595326062635738977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28923086127101416847651969 21692314595326062635738977)
  ·
    refine ⟨16269235946494546976804233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21692314595326062635738977 16269235946494546976804233)
    ·
      refine ⟨12201926959870910232603175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16269235946494546976804233 12201926959870910232603175)
      ·
        refine ⟨18302890439806365348904763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12201926959870910232603175 18302890439806365348904763)
        ·
          refine ⟨27454335659709548023357145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18302890439806365348904763 27454335659709548023357145)
          ·
            refine ⟨20590751744782161017517859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27454335659709548023357145 20590751744782161017517859)
            ·
              refine ⟨30886127617173241526276789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20590751744782161017517859 30886127617173241526276789)
              ·
                refine ⟨2895574464109991393088449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30886127617173241526276789 2895574464109991393088449)
                ·
                  refine ⟨2171680848082493544816337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2895574464109991393088449 2171680848082493544816337)
                  ·
                    refine ⟨1628760636061870158612253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2171680848082493544816337 1628760636061870158612253)
                    ·
                      refine ⟨610785238523201309479595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1628760636061870158612253 610785238523201309479595)
                      ·
                        rfl

theorem cell23_1189500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_1189500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189500 prefixEnd_1189500 := by exact prefixLift 1189500
  have htrace : WordTrace (prefixWord ++ tailWord_1189500) baseStart_1189500 baseEnd_1189500 := by
    simpa [prefixWord, tailWord_1189500, baseEnd_1189500] using wordTrace_append hprefix tailTrace_1189500
  have hstable : (prefixWord ++ tailWord_1189500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189500).length < 2 ^ (prefixWord ++ tailWord_1189500).sum := by decide
  have hdescent : baseEnd_1189500 < baseStart_1189500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189533 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1189533 : Nat := 118140960795 + 1189533 * 2 ^ 59
def prefixEnd_1189533 : Nat := 4983230072969 + 3 ^ 40 * 1189533 * 2
def baseEnd_1189533 : Nat := 203600727794933226788981

theorem tailTrace_1189533 : CollatzResearch.WordTrace tailWord_1189533 prefixEnd_1189533 203600727794933226788981 := by
  unfold tailWord_1189533
  simp only [CollatzResearch.WordTrace]
  refine ⟨43385832799532571907429253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28923888533021714604952835 43385832799532571907429253)
  ·
    refine ⟨8134843649912357232642985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43385832799532571907429253 8134843649912357232642985)
    ·
      refine ⟨6101132737434267924482239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8134843649912357232642985 6101132737434267924482239)
      ·
        refine ⟨9151699106151401886723359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6101132737434267924482239 9151699106151401886723359)
        ·
          refine ⟨13727548659227102830085039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9151699106151401886723359 13727548659227102830085039)
          ·
            refine ⟨20591322988840654245127559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13727548659227102830085039 20591322988840654245127559)
            ·
              refine ⟨30886984483260981367691339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20591322988840654245127559 30886984483260981367691339)
              ·
                refine ⟨46330476724891472051537009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30886984483260981367691339 46330476724891472051537009)
                ·
                  refine ⟨34747857543668604038652757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46330476724891472051537009 34747857543668604038652757)
                  ·
                    refine ⟨203600727794933226788981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34747857543668604038652757 203600727794933226788981)
                    ·
                      rfl

theorem cell23_1189533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1189533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189533 prefixEnd_1189533 := by exact prefixLift 1189533
  have htrace : WordTrace (prefixWord ++ tailWord_1189533) baseStart_1189533 baseEnd_1189533 := by
    simpa [prefixWord, tailWord_1189533, baseEnd_1189533] using wordTrace_append hprefix tailTrace_1189533
  have hstable : (prefixWord ++ tailWord_1189533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189533).length < 2 ^ (prefixWord ++ tailWord_1189533).sum := by decide
  have hdescent : baseEnd_1189533 < baseStart_1189533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189537 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 6]
def baseStart_1189537 : Nat := 118140960795 + 1189537 * 2 ^ 59
def prefixEnd_1189537 : Nat := 4983230072969 + 3 ^ 40 * 1189537 * 2
def baseEnd_1189537 : Nat := 67867137478601962746325

theorem tailTrace_1189537 : CollatzResearch.WordTrace tailWord_1189537 prefixEnd_1189537 67867137478601962746325 := by
  unfold tailWord_1189537
  simp only [CollatzResearch.WordTrace]
  refine ⟨43385978691518080590574865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28923985794345387060383243 43385978691518080590574865)
  ·
    refine ⟨32539484018638560442931149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43385978691518080590574865 32539484018638560442931149)
    ·
      refine ⟨12202306506989460166099181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32539484018638560442931149 12202306506989460166099181)
      ·
        refine ⟨4575864940121047562287193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12202306506989460166099181 4575864940121047562287193)
        ·
          refine ⟨3431898705090785671715395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4575864940121047562287193 3431898705090785671715395)
          ·
            refine ⟨5147848057636178507573093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431898705090785671715395 5147848057636178507573093)
            ·
              refine ⟨965221510806783470169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5147848057636178507573093 965221510806783470169955)
              ·
                refine ⟨1447832266210175205254933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965221510806783470169955 1447832266210175205254933)
                ·
                  refine ⟨67867137478601962746325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1447832266210175205254933 67867137478601962746325)
                  ·
                    rfl

theorem cell23_1189537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 6].length) (baseStart_1189537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189537 prefixEnd_1189537 := by exact prefixLift 1189537
  have htrace : WordTrace (prefixWord ++ tailWord_1189537) baseStart_1189537 baseEnd_1189537 := by
    simpa [prefixWord, tailWord_1189537, baseEnd_1189537] using wordTrace_append hprefix tailTrace_1189537
  have hstable : (prefixWord ++ tailWord_1189537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189537).length < 2 ^ (prefixWord ++ tailWord_1189537).sum := by decide
  have hdescent : baseEnd_1189537 < baseStart_1189537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189567 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 1, 5]
def baseStart_1189567 : Nat := 118140960795 + 1189567 * 2 ^ 59
def prefixEnd_1189567 : Nat := 4983230072969 + 3 ^ 40 * 1189567 * 2
def baseEnd_1189567 : Nat := 203606547242350849113929

theorem tailTrace_1189567 : CollatzResearch.WordTrace tailWord_1189567 prefixEnd_1189567 203606547242350849113929 := by
  unfold tailWord_1189567
  simp only [CollatzResearch.WordTrace]
  refine ⟨43387072881409395714166955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28924715254272930476111303 43387072881409395714166955)
  ·
    refine ⟨65080609322114093571250433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43387072881409395714166955 65080609322114093571250433)
    ·
      refine ⟨48810456991585570178437825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65080609322114093571250433 48810456991585570178437825)
      ·
        refine ⟨36607842743689177633828369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48810456991585570178437825 36607842743689177633828369)
        ·
          refine ⟨27455882057766883225371277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36607842743689177633828369 27455882057766883225371277)
          ·
            refine ⟨10295955771662581209514229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27455882057766883225371277 10295955771662581209514229)
            ·
              refine ⟨965245853593366988391959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10295955771662581209514229 965245853593366988391959)
              ·
                refine ⟨1447868780390050482587939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965245853593366988391959 1447868780390050482587939)
                ·
                  refine ⟨2171803170585075723881909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1447868780390050482587939 2171803170585075723881909)
                  ·
                    refine ⟨203606547242350849113929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2171803170585075723881909 203606547242350849113929)
                    ·
                      rfl

theorem cell23_1189567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 5].length) (baseStart_1189567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189567 prefixEnd_1189567 := by exact prefixLift 1189567
  have htrace : WordTrace (prefixWord ++ tailWord_1189567) baseStart_1189567 baseEnd_1189567 := by
    simpa [prefixWord, tailWord_1189567, baseEnd_1189567] using wordTrace_append hprefix tailTrace_1189567
  have hstable : (prefixWord ++ tailWord_1189567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189567).length < 2 ^ (prefixWord ++ tailWord_1189567).sum := by decide
  have hdescent : baseEnd_1189567 < baseStart_1189567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189583 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_1189583 : Nat := 118140960795 + 1189583 * 2 ^ 59
def prefixEnd_1189583 : Nat := 4983230072969 + 3 ^ 40 * 1189583 * 2
def baseEnd_1189583 : Nat := 610827857417524484741713

theorem tailTrace_1189583 : CollatzResearch.WordTrace tailWord_1189583 prefixEnd_1189583 610827857417524484741713 := by
  unfold tailWord_1189583
  simp only [CollatzResearch.WordTrace]
  refine ⟨43387656449351430446749403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28925104299567620297832935 43387656449351430446749403)
  ·
    refine ⟨65081484674027145670124105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43387656449351430446749403 65081484674027145670124105)
    ·
      refine ⟨48811113505520359252593079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65081484674027145670124105 48811113505520359252593079)
      ·
        refine ⟨73216670258280538878889619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48811113505520359252593079 73216670258280538878889619)
        ·
          refine ⟨109825005387420808318334429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73216670258280538878889619 109825005387420808318334429)
          ·
            refine ⟨41184377020282803119375411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109825005387420808318334429 41184377020282803119375411)
            ·
              refine ⟨61776565530424204679063117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41184377020282803119375411 61776565530424204679063117)
              ·
                refine ⟨23166212073909076754648669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61776565530424204679063117 23166212073909076754648669)
                ·
                  refine ⟨8687329527715903782993251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23166212073909076754648669 8687329527715903782993251)
                  ·
                    refine ⟨13030994291573855674489877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8687329527715903782993251 13030994291573855674489877)
                    ·
                      refine ⟨610827857417524484741713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13030994291573855674489877 610827857417524484741713)
                      ·
                        rfl

theorem cell23_1189583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_1189583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189583 prefixEnd_1189583 := by exact prefixLift 1189583
  have htrace : WordTrace (prefixWord ++ tailWord_1189583) baseStart_1189583 baseEnd_1189583 := by
    simpa [prefixWord, tailWord_1189583, baseEnd_1189583] using wordTrace_append hprefix tailTrace_1189583
  have hstable : (prefixWord ++ tailWord_1189583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189583).length < 2 ^ (prefixWord ++ tailWord_1189583).sum := by decide
  have hdescent : baseEnd_1189583 < baseStart_1189583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189600 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1189600 : Nat := 118140960795 + 1189600 * 2 ^ 59
def prefixEnd_1189600 : Nat := 4983230072969 + 3 ^ 40 * 1189600 * 2
def baseEnd_1189600 : Nat := 610836586588650918229135

theorem tailTrace_1189600 : CollatzResearch.WordTrace tailWord_1189600 prefixEnd_1189600 610836586588650918229135 := by
  unfold tailWord_1189600
  simp only [CollatzResearch.WordTrace]
  refine ⟨21694138245144921175059127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28925517660193228233412169 21694138245144921175059127)
  ·
    refine ⟨32541207367717381762588691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21694138245144921175059127 32541207367717381762588691)
    ·
      refine ⟨48811811051576072643883037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32541207367717381762588691 48811811051576072643883037)
      ·
        refine ⟨18304429144341027241456139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48811811051576072643883037 18304429144341027241456139)
        ·
          refine ⟨27456643716511540862184209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18304429144341027241456139 27456643716511540862184209)
          ·
            refine ⟨20592482787383655646638157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27456643716511540862184209 20592482787383655646638157)
            ·
              refine ⟨7722181045268870867489309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20592482787383655646638157 7722181045268870867489309)
              ·
                refine ⟨2895817891975826575308491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7722181045268870867489309 2895817891975826575308491)
                ·
                  refine ⟨4343726837963739862962737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2895817891975826575308491 4343726837963739862962737)
                  ·
                    refine ⟨3257795128472804897222053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4343726837963739862962737 3257795128472804897222053)
                    ·
                      refine ⟨610836586588650918229135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3257795128472804897222053 610836586588650918229135)
                      ·
                        rfl

theorem cell23_1189600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1189600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189600 prefixEnd_1189600 := by exact prefixLift 1189600
  have htrace : WordTrace (prefixWord ++ tailWord_1189600) baseStart_1189600 baseEnd_1189600 := by
    simpa [prefixWord, tailWord_1189600, baseEnd_1189600] using wordTrace_append hprefix tailTrace_1189600
  have hstable : (prefixWord ++ tailWord_1189600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189600).length < 2 ^ (prefixWord ++ tailWord_1189600).sum := by decide
  have hdescent : baseEnd_1189600 < baseStart_1189600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189604 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_1189604 : Nat := 118140960795 + 1189604 * 2 ^ 59
def prefixEnd_1189604 : Nat := 4983230072969 + 3 ^ 40 * 1189604 * 2
def baseEnd_1189604 : Nat := 610838640511268902579117

theorem tailTrace_1189604 : CollatzResearch.WordTrace tailWord_1189604 prefixEnd_1189604 610838640511268902579117 := by
  unfold tailWord_1189604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21694211191137675516631933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28925614921516900688842577 21694211191137675516631933)
  ·
    refine ⟨8135329196676628318736975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21694211191137675516631933 8135329196676628318736975)
    ·
      refine ⟨12202993795014942478105463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8135329196676628318736975 12202993795014942478105463)
      ·
        refine ⟨18304490692522413717158195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12202993795014942478105463 18304490692522413717158195)
        ·
          refine ⟨27456736038783620575737293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18304490692522413717158195 27456736038783620575737293)
          ·
            refine ⟨10296276014543857715901485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27456736038783620575737293 10296276014543857715901485)
            ·
              refine ⟨3861103505453946643463057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10296276014543857715901485 3861103505453946643463057)
              ·
                refine ⟨2895827629090459982597293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3861103505453946643463057 2895827629090459982597293)
                ·
                  refine ⟨1085935360908922493473985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2895827629090459982597293 1085935360908922493473985)
                  ·
                    refine ⟨814451520681691870105489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1085935360908922493473985 814451520681691870105489)
                    ·
                      refine ⟨610838640511268902579117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814451520681691870105489 610838640511268902579117)
                      ·
                        rfl

theorem cell23_1189604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_1189604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189604 prefixEnd_1189604 := by exact prefixLift 1189604
  have htrace : WordTrace (prefixWord ++ tailWord_1189604) baseStart_1189604 baseEnd_1189604 := by
    simpa [prefixWord, tailWord_1189604, baseEnd_1189604] using wordTrace_append hprefix tailTrace_1189604
  have hstable : (prefixWord ++ tailWord_1189604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189604).length < 2 ^ (prefixWord ++ tailWord_1189604).sum := by decide
  have hdescent : baseEnd_1189604 < baseStart_1189604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189647 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 3, 3, 2]
def baseStart_1189647 : Nat := 118140960795 + 1189647 * 2 ^ 59
def prefixEnd_1189647 : Nat := 4983230072969 + 3 ^ 40 * 1189647 * 2
def baseEnd_1189647 : Nat := 610860720179412234341419

theorem tailTrace_1189647 : CollatzResearch.WordTrace tailWord_1189647 prefixEnd_1189647 610860720179412234341419 := by
  unfold tailWord_1189647
  simp only [CollatzResearch.WordTrace]
  refine ⟨43389990721119569377079195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28926660480746379584719463 43389990721119569377079195)
  ·
    refine ⟨65084986081679354065618793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43389990721119569377079195 65084986081679354065618793)
    ·
      refine ⟨48813739561259515549214095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65084986081679354065618793 48813739561259515549214095)
      ·
        refine ⟨73220609341889273323821143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48813739561259515549214095 73220609341889273323821143)
        ·
          refine ⟨109830914012833909985731715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73220609341889273323821143 109830914012833909985731715)
          ·
            refine ⟨164746371019250864978597573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109830914012833909985731715 164746371019250864978597573)
            ·
              refine ⟨30889944566109537183487045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164746371019250864978597573 30889944566109537183487045)
              ·
                refine ⟨5791864606145538221903821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30889944566109537183487045 5791864606145538221903821)
                ·
                  refine ⟨2171949227304576833213933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5791864606145538221903821 2171949227304576833213933)
                  ·
                    refine ⟨814480960239216312455225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2171949227304576833213933 814480960239216312455225)
                    ·
                      refine ⟨610860720179412234341419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814480960239216312455225 610860720179412234341419)
                      ·
                        rfl

theorem cell23_1189647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3, 2].length) (baseStart_1189647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189647 prefixEnd_1189647 := by exact prefixLift 1189647
  have htrace : WordTrace (prefixWord ++ tailWord_1189647) baseStart_1189647 baseEnd_1189647 := by
    simpa [prefixWord, tailWord_1189647, baseEnd_1189647] using wordTrace_append hprefix tailTrace_1189647
  have hstable : (prefixWord ++ tailWord_1189647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189647).length < 2 ^ (prefixWord ++ tailWord_1189647).sum := by decide
  have hdescent : baseEnd_1189647 < baseStart_1189647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189680 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_1189680 : Nat := 118140960795 + 1189680 * 2 ^ 59
def prefixEnd_1189680 : Nat := 4983230072969 + 3 ^ 40 * 1189680 * 2
def baseEnd_1189680 : Nat := 610877665041010605228767

theorem tailTrace_1189680 : CollatzResearch.WordTrace tailWord_1189680 prefixEnd_1189680 610877665041010605228767 := by
  unfold tailWord_1189680
  simp only [CollatzResearch.WordTrace]
  refine ⟨21695597165000008006515247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28927462886666677342020329 21695597165000008006515247)
  ·
    refine ⟨32543395747500012009772871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21695597165000008006515247 32543395747500012009772871)
    ·
      refine ⟨48815093621250018014659307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32543395747500012009772871 48815093621250018014659307)
      ·
        refine ⟨73222640431875027021988961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48815093621250018014659307 73222640431875027021988961)
        ·
          refine ⟨54916980323906270266491721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73222640431875027021988961 54916980323906270266491721)
          ·
            refine ⟨41187735242929702699868791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54916980323906270266491721 41187735242929702699868791)
            ·
              refine ⟨61781602864394554049803187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41187735242929702699868791 61781602864394554049803187)
              ·
                refine ⟨92672404296591831074704781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61781602864394554049803187 92672404296591831074704781)
                ·
                  refine ⟨34752151611221936653014293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92672404296591831074704781 34752151611221936653014293)
                  ·
                    refine ⟨1629007106776028280610045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34752151611221936653014293 1629007106776028280610045)
                    ·
                      refine ⟨610877665041010605228767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1629007106776028280610045 610877665041010605228767)
                      ·
                        rfl

theorem cell23_1189680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_1189680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189680 prefixEnd_1189680 := by exact prefixLift 1189680
  have htrace : WordTrace (prefixWord ++ tailWord_1189680) baseStart_1189680 baseEnd_1189680 := by
    simpa [prefixWord, tailWord_1189680, baseEnd_1189680] using wordTrace_append hprefix tailTrace_1189680
  have hstable : (prefixWord ++ tailWord_1189680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189680).length < 2 ^ (prefixWord ++ tailWord_1189680).sum := by decide
  have hdescent : baseEnd_1189680 < baseStart_1189680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189737 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 4, 5, 2]
def baseStart_1189737 : Nat := 118140960795 + 1189737 * 2 ^ 59
def prefixEnd_1189737 : Nat := 4983230072969 + 3 ^ 40 * 1189737 * 2
def baseEnd_1189737 : Nat := 610906933438316882216005

theorem tailTrace_1189737 : CollatzResearch.WordTrace tailWord_1189737 prefixEnd_1189737 610906933438316882216005 := by
  unfold tailWord_1189737
  simp only [CollatzResearch.WordTrace]
  refine ⟨43393273290793514747855465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28928848860529009831903643 43393273290793514747855465)
  ·
    refine ⟨32544954968095136060891599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43393273290793514747855465 32544954968095136060891599)
    ·
      refine ⟨48817432452142704091337399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32544954968095136060891599 48817432452142704091337399)
      ·
        refine ⟨73226148678214056137006099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48817432452142704091337399 73226148678214056137006099)
        ·
          refine ⟨109839223017321084205509149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73226148678214056137006099 109839223017321084205509149)
          ·
            refine ⟨41189708631495406577065931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109839223017321084205509149 41189708631495406577065931)
            ·
              refine ⟨61784562947243109865598897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41189708631495406577065931 61784562947243109865598897)
              ·
                refine ⟨46338422210432332399199173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61784562947243109865598897 46338422210432332399199173)
                ·
                  refine ⟨8688454164456062324849845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46338422210432332399199173 8688454164456062324849845)
                  ·
                    refine ⟨814542577917755842954673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8688454164456062324849845 814542577917755842954673)
                    ·
                      refine ⟨610906933438316882216005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814542577917755842954673 610906933438316882216005)
                      ·
                        rfl

theorem cell23_1189737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 5, 2].length) (baseStart_1189737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189737 prefixEnd_1189737 := by exact prefixLift 1189737
  have htrace : WordTrace (prefixWord ++ tailWord_1189737) baseStart_1189737 baseEnd_1189737 := by
    simpa [prefixWord, tailWord_1189737, baseEnd_1189737] using wordTrace_append hprefix tailTrace_1189737
  have hstable : (prefixWord ++ tailWord_1189737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189737).length < 2 ^ (prefixWord ++ tailWord_1189737).sum := by decide
  have hdescent : baseEnd_1189737 < baseStart_1189737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
