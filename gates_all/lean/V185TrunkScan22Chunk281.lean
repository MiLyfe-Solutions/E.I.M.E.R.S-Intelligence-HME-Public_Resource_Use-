import V185TrunkScan22Chunk280

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2505376 : List Nat := [2, 1, 1, 4, 5, 1, 8]
def baseStart_2505376 : Nat := 118140960795 + 2505376 * 2 ^ 59
def prefixEnd_2505376 : Nat := 4983230072969 + 3 ^ 40 * 2505376 * 2
def baseEnd_2505376 : Nat := 31764496499725800952543

theorem tailTrace_2505376 : CollatzResearch.WordTrace tailWord_2505376 prefixEnd_2505376 31764496499725800952543 := by
  unfold tailWord_2505376
  simp only [CollatzResearch.WordTrace]
  refine ⟨45689284885729055500155991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60919046514305407333541321 45689284885729055500155991)
  ·
    refine ⟨68533927328593583250233987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45689284885729055500155991 68533927328593583250233987)
    ·
      refine ⟨102800890992890374875350981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68533927328593583250233987 102800890992890374875350981)
      ·
        refine ⟨19275167061166945289128309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102800890992890374875350981 19275167061166945289128309)
        ·
          refine ⟨1807046911984401120855779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19275167061166945289128309 1807046911984401120855779)
          ·
            refine ⟨2710570367976601681283669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807046911984401120855779 2710570367976601681283669)
            ·
              refine ⟨31764496499725800952543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2710570367976601681283669 31764496499725800952543)
              ·
                rfl

theorem cell22_2505376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 8].length) (baseStart_2505376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505376 prefixEnd_2505376 := by exact prefixLift 2505376
  have htrace : WordTrace (prefixWord ++ tailWord_2505376) baseStart_2505376 baseEnd_2505376 := by
    simpa [prefixWord, tailWord_2505376, baseEnd_2505376] using wordTrace_append hprefix tailTrace_2505376
  have hstable : (prefixWord ++ tailWord_2505376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505376).length < 2 ^ (prefixWord ++ tailWord_2505376).sum := by decide
  have hdescent : baseEnd_2505376 < baseStart_2505376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505391 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 3, 3]
def baseStart_2505391 : Nat := 118140960795 + 2505391 * 2 ^ 59
def prefixEnd_2505391 : Nat := 4983230072969 + 3 ^ 40 * 2505391 * 2
def baseEnd_2505391 : Nat := 857646540299141586593615

theorem tailTrace_2505391 : CollatzResearch.WordTrace tailWord_2505391 prefixEnd_2505391 857646540299141586593615 := by
  unfold tailWord_2505391
  simp only [CollatzResearch.WordTrace]
  refine ⟨91379116866403768562108027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60919411244269179041405351 91379116866403768562108027)
  ·
    refine ⟨137068675299605652843162041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91379116866403768562108027 137068675299605652843162041)
    ·
      refine ⟨102801506474704239632371531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137068675299605652843162041 102801506474704239632371531)
      ·
        refine ⟨154202259712056359448557297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102801506474704239632371531 154202259712056359448557297)
        ·
          refine ⟨115651694784042269586417973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154202259712056359448557297 115651694784042269586417973)
          ·
            refine ⟨10842346386003962773726685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115651694784042269586417973 10842346386003962773726685)
            ·
              refine ⟨4065879894751486040147507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10842346386003962773726685 4065879894751486040147507)
              ·
                refine ⟨6098819842127229060221261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4065879894751486040147507 6098819842127229060221261)
                ·
                  refine ⟨2287057440797710897582973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6098819842127229060221261 2287057440797710897582973)
                  ·
                    refine ⟨857646540299141586593615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287057440797710897582973 857646540299141586593615)
                    ·
                      rfl

theorem cell22_2505391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_2505391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505391 prefixEnd_2505391 := by exact prefixLift 2505391
  have htrace : WordTrace (prefixWord ++ tailWord_2505391) baseStart_2505391 baseEnd_2505391 := by
    simpa [prefixWord, tailWord_2505391, baseEnd_2505391] using wordTrace_append hprefix tailTrace_2505391
  have hstable : (prefixWord ++ tailWord_2505391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505391).length < 2 ^ (prefixWord ++ tailWord_2505391).sum := by decide
  have hdescent : baseEnd_2505391 < baseStart_2505391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505539 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 9]
def baseStart_2505539 : Nat := 118140960795 + 2505539 * 2 ^ 59
def prefixEnd_2505539 : Nat := 4983230072969 + 3 ^ 40 * 2505539 * 2
def baseEnd_2505539 : Nat := 285899067907906177964387

theorem tailTrace_2505539 : CollatzResearch.WordTrace tailWord_2505539 prefixEnd_2505539 285899067907906177964387 := by
  unfold tailWord_2505539
  simp only [CollatzResearch.WordTrace]
  refine ⟨91384514869867589838495671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60923009913245059892330447 91384514869867589838495671)
  ·
    refine ⟨137076772304801384757743507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91384514869867589838495671 137076772304801384757743507)
    ·
      refine ⟨205615158457202077136615261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137076772304801384757743507 205615158457202077136615261)
      ·
        refine ⟨77105684421450778926230723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205615158457202077136615261 77105684421450778926230723)
        ·
          refine ⟨115658526632176168389346085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77105684421450778926230723 115658526632176168389346085)
          ·
            refine ⟨21685973743533031573002391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115658526632176168389346085 21685973743533031573002391)
            ·
              refine ⟨32528960615299547359503587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21685973743533031573002391 32528960615299547359503587)
              ·
                refine ⟨48793440922949321039255381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32528960615299547359503587 48793440922949321039255381)
                ·
                  refine ⟨285899067907906177964387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48793440922949321039255381 285899067907906177964387)
                  ·
                    rfl

theorem cell22_2505539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_2505539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505539 prefixEnd_2505539 := by exact prefixLift 2505539
  have htrace : WordTrace (prefixWord ++ tailWord_2505539) baseStart_2505539 baseEnd_2505539 := by
    simpa [prefixWord, tailWord_2505539, baseEnd_2505539] using wordTrace_append hprefix tailTrace_2505539
  have hstable : (prefixWord ++ tailWord_2505539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505539).length < 2 ^ (prefixWord ++ tailWord_2505539).sum := by decide
  have hdescent : baseEnd_2505539 < baseStart_2505539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505573 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 5]
def baseStart_2505573 : Nat := 118140960795 + 2505573 * 2 ^ 59
def prefixEnd_2505573 : Nat := 4983230072969 + 3 ^ 40 * 2505573 * 2
def baseEnd_2505573 : Nat := 285902947539517926181019

theorem tailTrace_2505573 : CollatzResearch.WordTrace tailWord_2505573 prefixEnd_2505573 285902947539517926181019 := by
  unfold tailWord_2505573
  simp only [CollatzResearch.WordTrace]
  refine ⟨91385754951744413645233373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60923836634496275763488915 91385754951744413645233373)
  ·
    refine ⟨34269658106904155116962515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91385754951744413645233373 34269658106904155116962515)
    ·
      refine ⟨51404487160356232675443773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34269658106904155116962515 51404487160356232675443773)
      ·
        refine ⟨19276682685133587253291415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51404487160356232675443773 19276682685133587253291415)
        ·
          refine ⟨28915024027700380879937123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19276682685133587253291415 28915024027700380879937123)
          ·
            refine ⟨43372536041550571319905685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28915024027700380879937123 43372536041550571319905685)
            ·
              refine ⟨2033087626947683030620579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43372536041550571319905685 2033087626947683030620579)
              ·
                refine ⟨3049631440421524545930869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033087626947683030620579 3049631440421524545930869)
                ·
                  refine ⟨285902947539517926181019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3049631440421524545930869 285902947539517926181019)
                  ·
                    rfl

theorem cell22_2505573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_2505573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505573 prefixEnd_2505573 := by exact prefixLift 2505573
  have htrace : WordTrace (prefixWord ++ tailWord_2505573) baseStart_2505573 baseEnd_2505573 := by
    simpa [prefixWord, tailWord_2505573, baseEnd_2505573] using wordTrace_append hprefix tailTrace_2505573
  have hstable : (prefixWord ++ tailWord_2505573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505573).length < 2 ^ (prefixWord ++ tailWord_2505573).sum := by decide
  have hdescent : baseEnd_2505573 < baseStart_2505573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505622 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2505622 : Nat := 118140960795 + 2505622 * 2 ^ 59
def prefixEnd_2505622 : Nat := 4983230072969 + 3 ^ 40 * 2505622 * 2
def baseEnd_2505622 : Nat := 857725616319933984067907

theorem tailTrace_2505622 : CollatzResearch.WordTrace tailWord_2505622 prefixEnd_2505622 857725616319933984067907 := by
  unfold tailWord_2505622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5711721383035430938360445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60925028085711263342511413 5711721383035430938360445)
  ·
    refine ⟨2141895518638286601885167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5711721383035430938360445 2141895518638286601885167)
    ·
      refine ⟨3212843277957429902827751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141895518638286601885167 3212843277957429902827751)
      ·
        refine ⟨4819264916936144854241627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212843277957429902827751 4819264916936144854241627)
        ·
          refine ⟨7228897375404217281362441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819264916936144854241627 7228897375404217281362441)
          ·
            refine ⟨5421673031553162961021831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7228897375404217281362441 5421673031553162961021831)
            ·
              refine ⟨8132509547329744441532747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421673031553162961021831 8132509547329744441532747)
              ·
                refine ⟨12198764320994616662299121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132509547329744441532747 12198764320994616662299121)
                ·
                  refine ⟨9149073240745962496724341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12198764320994616662299121 9149073240745962496724341)
                  ·
                    refine ⟨857725616319933984067907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9149073240745962496724341 857725616319933984067907)
                    ·
                      rfl

theorem cell22_2505622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2505622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505622 prefixEnd_2505622 := by exact prefixLift 2505622
  have htrace : WordTrace (prefixWord ++ tailWord_2505622) baseStart_2505622 baseEnd_2505622 := by
    simpa [prefixWord, tailWord_2505622, baseEnd_2505622] using wordTrace_append hprefix tailTrace_2505622
  have hstable : (prefixWord ++ tailWord_2505622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505622).length < 2 ^ (prefixWord ++ tailWord_2505622).sum := by decide
  have hdescent : baseEnd_2505622 < baseStart_2505622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505633 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2505633 : Nat := 118140960795 + 2505633 * 2 ^ 59
def prefixEnd_2505633 : Nat := 4983230072969 + 3 ^ 40 * 2505633 * 2
def baseEnd_2505633 : Nat := 857729381844733622042873

theorem tailTrace_2505633 : CollatzResearch.WordTrace tailWord_2505633 prefixEnd_2505633 857729381844733622042873 := by
  unfold tailWord_2505633
  simp only [CollatzResearch.WordTrace]
  refine ⟨91387943331527043892417553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60925295554351362594945035 91387943331527043892417553)
  ·
    refine ⟨68540957498645282919313165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91387943331527043892417553 68540957498645282919313165)
    ·
      refine ⟨25702859061991981094742437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68540957498645282919313165 25702859061991981094742437)
      ·
        refine ⟨4819286074123496455264207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25702859061991981094742437 4819286074123496455264207)
        ·
          refine ⟨7228929111185244682896311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819286074123496455264207 7228929111185244682896311)
          ·
            refine ⟨10843393666777867024344467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7228929111185244682896311 10843393666777867024344467)
            ·
              refine ⟨16265090500166800536516701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10843393666777867024344467 16265090500166800536516701)
              ·
                refine ⟨6099408937562550201193763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16265090500166800536516701 6099408937562550201193763)
                ·
                  refine ⟨9149113406343825301790645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6099408937562550201193763 9149113406343825301790645)
                  ·
                    refine ⟨857729381844733622042873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9149113406343825301790645 857729381844733622042873)
                    ·
                      rfl

theorem cell22_2505633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2505633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505633 prefixEnd_2505633 := by exact prefixLift 2505633
  have htrace : WordTrace (prefixWord ++ tailWord_2505633) baseStart_2505633 baseEnd_2505633 := by
    simpa [prefixWord, tailWord_2505633, baseEnd_2505633] using wordTrace_append hprefix tailTrace_2505633
  have hstable : (prefixWord ++ tailWord_2505633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505633).length < 2 ^ (prefixWord ++ tailWord_2505633).sum := by decide
  have hdescent : baseEnd_2505633 < baseStart_2505633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505652 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2505652 : Nat := 118140960795 + 2505652 * 2 ^ 59
def prefixEnd_2505652 : Nat := 4983230072969 + 3 ^ 40 * 2505652 * 2
def baseEnd_2505652 : Nat := 285911961977674635272605

theorem tailTrace_2505652 : CollatzResearch.WordTrace tailWord_2505652 prefixEnd_2505652 285911961977674635272605 := by
  unfold tailWord_2505652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45694318159229105068679605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60925757545638806758239473 45694318159229105068679605)
  ·
    refine ⟨4283842327427728600188713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45694318159229105068679605 4283842327427728600188713)
    ·
      refine ⟨3212881745570796450141535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4283842327427728600188713 3212881745570796450141535)
      ·
        refine ⟨4819322618356194675212303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212881745570796450141535 4819322618356194675212303)
        ·
          refine ⟨7228983927534292012818455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819322618356194675212303 7228983927534292012818455)
          ·
            refine ⟨10843475891301438019227683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7228983927534292012818455 10843475891301438019227683)
            ·
              refine ⟨16265213836952157028841525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10843475891301438019227683 16265213836952157028841525)
              ·
                refine ⟨1524863797214264721453893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16265213836952157028841525 1524863797214264721453893)
                ·
                  refine ⟨285911961977674635272605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524863797214264721453893 285911961977674635272605)
                  ·
                    rfl

theorem cell22_2505652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2505652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505652 prefixEnd_2505652 := by exact prefixLift 2505652
  have htrace : WordTrace (prefixWord ++ tailWord_2505652) baseStart_2505652 baseEnd_2505652 := by
    simpa [prefixWord, tailWord_2505652, baseEnd_2505652] using wordTrace_append hprefix tailTrace_2505652
  have hstable : (prefixWord ++ tailWord_2505652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505652).length < 2 ^ (prefixWord ++ tailWord_2505652).sum := by decide
  have hdescent : baseEnd_2505652 < baseStart_2505652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505716 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2505716 : Nat := 118140960795 + 2505716 * 2 ^ 59
def prefixEnd_2505716 : Nat := 4983230072969 + 3 ^ 40 * 2505716 * 2
def baseEnd_2505716 : Nat := 857757794440949072217619

theorem tailTrace_2505716 : CollatzResearch.WordTrace tailWord_2505716 prefixEnd_2505716 857757794440949072217619 := by
  unfold tailWord_2505716
  simp only [CollatzResearch.WordTrace]
  refine ⟨45695485295113174533844501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60927313726817566045126001 45695485295113174533844501)
  ·
    refine ⟨2141975873208430056273961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45695485295113174533844501 2141975873208430056273961)
    ·
      refine ⟨1606481904906322542205471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2141975873208430056273961 1606481904906322542205471)
      ·
        refine ⟨2409722857359483813308207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606481904906322542205471 2409722857359483813308207)
        ·
          refine ⟨3614584286039225719962311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409722857359483813308207 3614584286039225719962311)
          ·
            refine ⟨5421876429058838579943467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614584286039225719962311 5421876429058838579943467)
            ·
              refine ⟨8132814643588257869915201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421876429058838579943467 8132814643588257869915201)
              ·
                refine ⟨6099610982691193402436401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8132814643588257869915201 6099610982691193402436401)
                ·
                  refine ⟨4574708237018395051827301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6099610982691193402436401 4574708237018395051827301)
                  ·
                    refine ⟨857757794440949072217619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4574708237018395051827301 857757794440949072217619)
                    ·
                      rfl

theorem cell22_2505716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2505716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505716 prefixEnd_2505716 := by exact prefixLift 2505716
  have htrace : WordTrace (prefixWord ++ tailWord_2505716) baseStart_2505716 baseEnd_2505716 := by
    simpa [prefixWord, tailWord_2505716, baseEnd_2505716] using wordTrace_append hprefix tailTrace_2505716
  have hstable : (prefixWord ++ tailWord_2505716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505716).length < 2 ^ (prefixWord ++ tailWord_2505716).sum := by decide
  have hdescent : baseEnd_2505716 < baseStart_2505716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505729 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2505729 : Nat := 118140960795 + 2505729 * 2 ^ 59
def prefixEnd_2505729 : Nat := 4983230072969 + 3 ^ 40 * 2505729 * 2
def baseEnd_2505729 : Nat := 857762244606621371642579

theorem tailTrace_2505729 : CollatzResearch.WordTrace tailWord_2505729 prefixEnd_2505729 857762244606621371642579 := by
  unfold tailWord_2505729
  simp only [CollatzResearch.WordTrace]
  refine ⟨91391444739179252287912241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60927629826119501525274827 91391444739179252287912241)
  ·
    refine ⟨68543583554384439215934181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91391444739179252287912241 68543583554384439215934181)
    ·
      refine ⟨12851921916447082352987659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68543583554384439215934181 12851921916447082352987659)
      ·
        refine ⟨19277882874670623529481489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12851921916447082352987659 19277882874670623529481489)
        ·
          refine ⟨14458412156002967647111117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19277882874670623529481489 14458412156002967647111117)
          ·
            refine ⟨5421904558501112867666669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14458412156002967647111117 5421904558501112867666669)
            ·
              refine ⟨2033214209437917325375001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5421904558501112867666669 2033214209437917325375001)
              ·
                refine ⟨1524910657078437994031251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033214209437917325375001 1524910657078437994031251)
                ·
                  refine ⟨2287365985617656991046877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524910657078437994031251 2287365985617656991046877)
                  ·
                    refine ⟨857762244606621371642579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287365985617656991046877 857762244606621371642579)
                    ·
                      rfl

theorem cell22_2505729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2505729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505729 prefixEnd_2505729 := by exact prefixLift 2505729
  have htrace : WordTrace (prefixWord ++ tailWord_2505729) baseStart_2505729 baseEnd_2505729 := by
    simpa [prefixWord, tailWord_2505729, baseEnd_2505729] using wordTrace_append hprefix tailTrace_2505729
  have hstable : (prefixWord ++ tailWord_2505729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505729).length < 2 ^ (prefixWord ++ tailWord_2505729).sum := by decide
  have hdescent : baseEnd_2505729 < baseStart_2505729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505742 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_2505742 : Nat := 118140960795 + 2505742 * 2 ^ 59
def prefixEnd_2505742 : Nat := 4983230072969 + 3 ^ 40 * 2505742 * 2
def baseEnd_2505742 : Nat := 285922231590764557022513

theorem tailTrace_2505742 : CollatzResearch.WordTrace tailWord_2505742 prefixEnd_2505742 285922231590764557022513 := by
  unfold tailWord_2505742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11423989861016519438516935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60927945925421437005423653 11423989861016519438516935)
  ·
    refine ⟨17135984791524779157775403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11423989861016519438516935 17135984791524779157775403)
    ·
      refine ⟨25703977187287168736663105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17135984791524779157775403 25703977187287168736663105)
      ·
        refine ⟨19277982890465376552497329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25703977187287168736663105 19277982890465376552497329)
        ·
          refine ⟨14458487167849032414372997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19277982890465376552497329 14458487167849032414372997)
          ·
            refine ⟨2710966343971693577694937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14458487167849032414372997 2710966343971693577694937)
            ·
              refine ⟨2033224757978770183271203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2710966343971693577694937 2033224757978770183271203)
              ·
                refine ⟨3049837136968155274906805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033224757978770183271203 3049837136968155274906805)
                ·
                  refine ⟨285922231590764557022513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3049837136968155274906805 285922231590764557022513)
                  ·
                    rfl

theorem cell22_2505742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_2505742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505742 prefixEnd_2505742 := by exact prefixLift 2505742
  have htrace : WordTrace (prefixWord ++ tailWord_2505742) baseStart_2505742 baseEnd_2505742 := by
    simpa [prefixWord, tailWord_2505742, baseEnd_2505742] using wordTrace_append hprefix tailTrace_2505742
  have hstable : (prefixWord ++ tailWord_2505742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505742).length < 2 ^ (prefixWord ++ tailWord_2505742).sum := by decide
  have hdescent : baseEnd_2505742 < baseStart_2505742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505847 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 1, 3]
def baseStart_2505847 : Nat := 118140960795 + 2505847 * 2 ^ 59
def prefixEnd_2505847 : Nat := 4983230072969 + 3 ^ 40 * 2505847 * 2
def baseEnd_2505847 : Nat := 857802638418108397192217

theorem tailTrace_2505847 : CollatzResearch.WordTrace tailWord_2505847 prefixEnd_2505847 857802638418108397192217 := by
  unfold tailWord_2505847
  simp only [CollatzResearch.WordTrace]
  refine ⟨91395748552751758440707795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60930499035167838960471863 91395748552751758440707795)
  ·
    refine ⟨137093622829127637661061693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91395748552751758440707795 137093622829127637661061693)
    ·
      refine ⟨51410108560922864122898135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137093622829127637661061693 51410108560922864122898135)
      ·
        refine ⟨77115162841384296184347203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51410108560922864122898135 77115162841384296184347203)
        ·
          refine ⟨115672744262076444276520805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77115162841384296184347203 115672744262076444276520805)
          ·
            refine ⟨21688639549139333301847651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115672744262076444276520805 21688639549139333301847651)
            ·
              refine ⟨32532959323708999952771477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21688639549139333301847651 32532959323708999952771477)
              ·
                refine ⟨1524982468298859372786163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32532959323708999952771477 1524982468298859372786163)
                ·
                  refine ⟨2287473702448289059179245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524982468298859372786163 2287473702448289059179245)
                  ·
                    refine ⟨857802638418108397192217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287473702448289059179245 857802638418108397192217)
                    ·
                      rfl

theorem cell22_2505847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_2505847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505847 prefixEnd_2505847 := by exact prefixLift 2505847
  have htrace : WordTrace (prefixWord ++ tailWord_2505847) baseStart_2505847 baseEnd_2505847 := by
    simpa [prefixWord, tailWord_2505847, baseEnd_2505847] using wordTrace_append hprefix tailTrace_2505847
  have hstable : (prefixWord ++ tailWord_2505847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505847).length < 2 ^ (prefixWord ++ tailWord_2505847).sum := by decide
  have hdescent : baseEnd_2505847 < baseStart_2505847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505898 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2505898 : Nat := 118140960795 + 2505898 * 2 ^ 59
def prefixEnd_2505898 : Nat := 4983230072969 + 3 ^ 40 * 2505898 * 2
def baseEnd_2505898 : Nat := 857820096760361264167061

theorem tailTrace_2505898 : CollatzResearch.WordTrace tailWord_2505898 prefixEnd_2505898 857820096760361264167061 := by
  unfold tailWord_2505898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22849402168891748537703587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60931739117044662767209565 22849402168891748537703587)
  ·
    refine ⟨34274103253337622806555381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22849402168891748537703587 34274103253337622806555381)
    ·
      refine ⟨3213197180000402138114567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34274103253337622806555381 3213197180000402138114567)
      ·
        refine ⟨4819795770000603207171851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3213197180000402138114567 4819795770000603207171851)
        ·
          refine ⟨7229693655000904810757777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819795770000603207171851 7229693655000904810757777)
          ·
            refine ⟨5422270241250678608068333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7229693655000904810757777 5422270241250678608068333)
            ·
              refine ⟨2033351340469004478025625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5422270241250678608068333 2033351340469004478025625)
              ·
                refine ⟨1525013505351753358519219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033351340469004478025625 1525013505351753358519219)
                ·
                  refine ⟨2287520258027630037778829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525013505351753358519219 2287520258027630037778829)
                  ·
                    refine ⟨857820096760361264167061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287520258027630037778829 857820096760361264167061)
                    ·
                      rfl

theorem cell22_2505898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2505898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505898 prefixEnd_2505898 := by exact prefixLift 2505898
  have htrace : WordTrace (prefixWord ++ tailWord_2505898) baseStart_2505898 baseEnd_2505898 := by
    simpa [prefixWord, tailWord_2505898, baseEnd_2505898] using wordTrace_append hprefix tailTrace_2505898
  have hstable : (prefixWord ++ tailWord_2505898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505898).length < 2 ^ (prefixWord ++ tailWord_2505898).sum := by decide
  have hdescent : baseEnd_2505898 < baseStart_2505898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505967 : List Nat := [1, 1, 2, 1, 7, 2, 1, 7]
def baseStart_2505967 : Nat := 118140960795 + 2505967 * 2 ^ 59
def prefixEnd_2505967 : Nat := 4983230072969 + 3 ^ 40 * 2505967 * 2
def baseEnd_2505967 : Nat := 95315968541163120465761

theorem tailTrace_2505967 : CollatzResearch.WordTrace tailWord_2505967 prefixEnd_2505967 95315968541163120465761 := by
  unfold tailWord_2505967
  simp only [CollatzResearch.WordTrace]
  refine ⟨91400125312317018935076155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60933416874878012623384103 91400125312317018935076155)
  ·
    refine ⟨137100187968475528402614233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91400125312317018935076155 137100187968475528402614233)
    ·
      refine ⟨102825140976356646301960675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137100187968475528402614233 102825140976356646301960675)
      ·
        refine ⟨154237711464534969452941013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102825140976356646301960675 154237711464534969452941013)
        ·
          refine ⟨3614946362450038346553305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 154237711464534969452941013 3614946362450038346553305)
          ·
            refine ⟨2711209771837528759914979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3614946362450038346553305 2711209771837528759914979)
            ·
              refine ⟨4066814657756293139872469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711209771837528759914979 4066814657756293139872469)
              ·
                refine ⟨95315968541163120465761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4066814657756293139872469 95315968541163120465761)
                ·
                  rfl

theorem cell22_2505967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 7].length) (baseStart_2505967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505967 prefixEnd_2505967 := by exact prefixLift 2505967
  have htrace : WordTrace (prefixWord ++ tailWord_2505967) baseStart_2505967 baseEnd_2505967 := by
    simpa [prefixWord, tailWord_2505967, baseEnd_2505967] using wordTrace_append hprefix tailTrace_2505967
  have hstable : (prefixWord ++ tailWord_2505967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505967).length < 2 ^ (prefixWord ++ tailWord_2505967).sum := by decide
  have hdescent : baseEnd_2505967 < baseStart_2505967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505986 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2505986 : Nat := 118140960795 + 2505986 * 2 ^ 59
def prefixEnd_2505986 : Nat := 4983230072969 + 3 ^ 40 * 2505986 * 2
def baseEnd_2505986 : Nat := 857850220958758367966791

theorem tailTrace_2505986 : CollatzResearch.WordTrace tailWord_2505986 prefixEnd_2505986 857850220958758367966791 := by
  unfold tailWord_2505986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850204574812046295004453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60933878866165456786678541 22850204574812046295004453)
  ·
    refine ⟨4284413357777258680313335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22850204574812046295004453 4284413357777258680313335)
    ·
      refine ⟨6426620036665888020470003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284413357777258680313335 6426620036665888020470003)
      ·
        refine ⟨9639930054998832030705005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426620036665888020470003 9639930054998832030705005)
        ·
          refine ⟨3614973770624562011514377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9639930054998832030705005 3614973770624562011514377)
          ·
            refine ⟨2711230327968421508635783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3614973770624562011514377 2711230327968421508635783)
            ·
              refine ⟨4066845491952632262953675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711230327968421508635783 4066845491952632262953675)
              ·
                refine ⟨6100268237928948394430513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066845491952632262953675 6100268237928948394430513)
                ·
                  refine ⟨4575201178446711295822885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6100268237928948394430513 4575201178446711295822885)
                  ·
                    refine ⟨857850220958758367966791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575201178446711295822885 857850220958758367966791)
                    ·
                      rfl

theorem cell22_2505986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2505986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505986 prefixEnd_2505986 := by exact prefixLift 2505986
  have htrace : WordTrace (prefixWord ++ tailWord_2505986) baseStart_2505986 baseEnd_2505986 := by
    simpa [prefixWord, tailWord_2505986, baseEnd_2505986] using wordTrace_append hprefix tailTrace_2505986
  have hstable : (prefixWord ++ tailWord_2505986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505986).length < 2 ^ (prefixWord ++ tailWord_2505986).sum := by decide
  have hdescent : baseEnd_2505986 < baseStart_2505986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506012 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_2506012 : Nat := 118140960795 + 2506012 * 2 ^ 59
def prefixEnd_2506012 : Nat := 4983230072969 + 3 ^ 40 * 2506012 * 2
def baseEnd_2506012 : Nat := 285953040430034322272237

theorem tailTrace_2506012 : CollatzResearch.WordTrace tailWord_2506012 prefixEnd_2506012 285953040430034322272237 := by
  unfold tailWord_2506012
  simp only [CollatzResearch.WordTrace]
  refine ⟨45700883298576995810232145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60934511064769327746976193 45700883298576995810232145)
  ·
    refine ⟨34275662473932746857674109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45700883298576995810232145 34275662473932746857674109)
    ·
      refine ⟨12853373427724780071627791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34275662473932746857674109 12853373427724780071627791)
      ·
        refine ⟨19280060141587170107441687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12853373427724780071627791 19280060141587170107441687)
        ·
          refine ⟨28920090212380755161162531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19280060141587170107441687 28920090212380755161162531)
          ·
            refine ⟨43380135318571132741743797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28920090212380755161162531 43380135318571132741743797)
            ·
              refine ⟨4066887686116043694538481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43380135318571132741743797 4066887686116043694538481)
              ·
                refine ⟨3050165764587032770903861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4066887686116043694538481 3050165764587032770903861)
                ·
                  refine ⟨285953040430034322272237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050165764587032770903861 285953040430034322272237)
                  ·
                    rfl

theorem cell22_2506012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_2506012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506012 prefixEnd_2506012 := by exact prefixLift 2506012
  have htrace : WordTrace (prefixWord ++ tailWord_2506012) baseStart_2506012 baseEnd_2506012 := by
    simpa [prefixWord, tailWord_2506012, baseEnd_2506012] using wordTrace_append hprefix tailTrace_2506012
  have hstable : (prefixWord ++ tailWord_2506012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506012).length < 2 ^ (prefixWord ++ tailWord_2506012).sum := by decide
  have hdescent : baseEnd_2506012 < baseStart_2506012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506072 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_2506072 : Nat := 118140960795 + 2506072 * 2 ^ 59
def prefixEnd_2506072 : Nat := 4983230072969 + 3 ^ 40 * 2506072 * 2
def baseEnd_2506072 : Nat := 857879660516282810316527

theorem tailTrace_2506072 : CollatzResearch.WordTrace tailWord_2506072 prefixEnd_2506072 857879660516282810316527 := by
  unfold tailWord_2506072
  simp only [CollatzResearch.WordTrace]
  refine ⟨45701977488468310933824235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60935969984624414578432313 45701977488468310933824235)
  ·
    refine ⟨68552966232702466400736353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45701977488468310933824235 68552966232702466400736353)
    ·
      refine ⟨51414724674526849800552265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68552966232702466400736353 51414724674526849800552265)
      ·
        refine ⟨38561043505895137350414199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51414724674526849800552265 38561043505895137350414199)
        ·
          refine ⟨57841565258842706025621299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38561043505895137350414199 57841565258842706025621299)
          ·
            refine ⟨86762347888264059038431949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57841565258842706025621299 86762347888264059038431949)
            ·
              refine ⟨32535880458099022139411981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86762347888264059038431949 32535880458099022139411981)
              ·
                refine ⟨12200955171787133302279493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32535880458099022139411981 12200955171787133302279493)
                ·
                  refine ⟨2287679094710087494177405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12200955171787133302279493 2287679094710087494177405)
                  ·
                    refine ⟨857879660516282810316527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287679094710087494177405 857879660516282810316527)
                    ·
                      rfl

theorem cell22_2506072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_2506072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506072 prefixEnd_2506072 := by exact prefixLift 2506072
  have htrace : WordTrace (prefixWord ++ tailWord_2506072) baseStart_2506072 baseEnd_2506072 := by
    simpa [prefixWord, tailWord_2506072, baseEnd_2506072] using wordTrace_append hprefix tailTrace_2506072
  have hstable : (prefixWord ++ tailWord_2506072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506072).length < 2 ^ (prefixWord ++ tailWord_2506072).sum := by decide
  have hdescent : baseEnd_2506072 < baseStart_2506072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506110 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2506110 : Nat := 118140960795 + 2506110 * 2 ^ 59
def prefixEnd_2506110 : Nat := 4983230072969 + 3 ^ 40 * 2506110 * 2
def baseEnd_2506110 : Nat := 857892668692863377866411

theorem tailTrace_2506110 : CollatzResearch.WordTrace tailWord_2506110 prefixEnd_2506110 857892668692863377866411 := by
  unfold tailWord_2506110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425667618849869294691473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60936893967199302905021189 11425667618849869294691473)
  ·
    refine ⟨8569250714137401971018605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11425667618849869294691473 8569250714137401971018605)
    ·
      refine ⟨3213469017801525739131977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8569250714137401971018605 3213469017801525739131977)
      ·
        refine ⟨2410101763351144304348983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3213469017801525739131977 2410101763351144304348983)
        ·
          refine ⟨3615152645026716456523475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410101763351144304348983 3615152645026716456523475)
          ·
            refine ⟨5422728967540074684785213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615152645026716456523475 5422728967540074684785213)
            ·
              refine ⟨2033523362827528006794455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5422728967540074684785213 2033523362827528006794455)
              ·
                refine ⟨3050285044241292010191683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033523362827528006794455 3050285044241292010191683)
                ·
                  refine ⟨4575427566361938015287525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050285044241292010191683 4575427566361938015287525)
                  ·
                    refine ⟨857892668692863377866411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575427566361938015287525 857892668692863377866411)
                    ·
                      rfl

theorem cell22_2506110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2506110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506110 prefixEnd_2506110 := by exact prefixLift 2506110
  have htrace : WordTrace (prefixWord ++ tailWord_2506110) baseStart_2506110 baseEnd_2506110 := by
    simpa [prefixWord, tailWord_2506110, baseEnd_2506110] using wordTrace_append hprefix tailTrace_2506110
  have hstable : (prefixWord ++ tailWord_2506110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506110).length < 2 ^ (prefixWord ++ tailWord_2506110).sum := by decide
  have hdescent : baseEnd_2506110 < baseStart_2506110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506136 : List Nat := [2, 1, 2, 5, 3, 1, 1, 7]
def baseStart_2506136 : Nat := 118140960795 + 2506136 * 2 ^ 59
def prefixEnd_2506136 : Nat := 4983230072969 + 3 ^ 40 * 2506136 * 2
def baseEnd_2506136 : Nat := 95322396558245330746259

theorem tailTrace_2506136 : CollatzResearch.WordTrace tailWord_2506136 prefixEnd_2506136 95322396558245330746259 := by
  unfold tailWord_2506136
  simp only [CollatzResearch.WordTrace]
  refine ⟨45703144624352380398989131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60937526165803173865318841 45703144624352380398989131)
  ·
    refine ⟨68554716936528570598483697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45703144624352380398989131 68554716936528570598483697)
    ·
      refine ⟨51416037702396427948862773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68554716936528570598483697 51416037702396427948862773)
      ·
        refine ⟨4820253534599665120205885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51416037702396427948862773 4820253534599665120205885)
        ·
          refine ⟨1807595075474874420077207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4820253534599665120205885 1807595075474874420077207)
          ·
            refine ⟨2711392613212311630115811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807595075474874420077207 2711392613212311630115811)
            ·
              refine ⟨4067088919818467445173717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711392613212311630115811 4067088919818467445173717)
              ·
                refine ⟨95322396558245330746259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4067088919818467445173717 95322396558245330746259)
                ·
                  rfl

theorem cell22_2506136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_2506136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506136 prefixEnd_2506136 := by exact prefixLift 2506136
  have htrace : WordTrace (prefixWord ++ tailWord_2506136) baseStart_2506136 baseEnd_2506136 := by
    simpa [prefixWord, tailWord_2506136, baseEnd_2506136] using wordTrace_append hprefix tailTrace_2506136
  have hstable : (prefixWord ++ tailWord_2506136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506136).length < 2 ^ (prefixWord ++ tailWord_2506136).sum := by decide
  have hdescent : baseEnd_2506136 < baseStart_2506136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506147 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 5]
def baseStart_2506147 : Nat := 118140960795 + 2506147 * 2 ^ 59
def prefixEnd_2506147 : Nat := 4983230072969 + 3 ^ 40 * 2506147 * 2
def baseEnd_2506147 : Nat := 285968444849669204897099

theorem tailTrace_2506147 : CollatzResearch.WordTrace tailWord_2506147 prefixEnd_2506147 285968444849669204897099 := by
  unfold tailWord_2506147
  simp only [CollatzResearch.WordTrace]
  refine ⟨91406690451664909676628695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60937793634443273117752463 91406690451664909676628695)
  ·
    refine ⟨137110035677497364514943043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91406690451664909676628695 137110035677497364514943043)
    ·
      refine ⟨205665053516246046772414565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137110035677497364514943043 205665053516246046772414565)
      ·
        refine ⟨38562197534296133769827731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205665053516246046772414565 38562197534296133769827731)
        ·
          refine ⟨57843296301444200654741597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38562197534296133769827731 57843296301444200654741597)
          ·
            refine ⟨21691236113041575245528099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57843296301444200654741597 21691236113041575245528099)
            ·
              refine ⟨32536854169562362868292149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21691236113041575245528099 32536854169562362868292149)
              ·
                refine ⟨3050330078396471518902389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32536854169562362868292149 3050330078396471518902389)
                ·
                  refine ⟨285968444849669204897099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050330078396471518902389 285968444849669204897099)
                  ·
                    rfl

theorem cell22_2506147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 5].length) (baseStart_2506147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506147 prefixEnd_2506147 := by exact prefixLift 2506147
  have htrace : WordTrace (prefixWord ++ tailWord_2506147) baseStart_2506147 baseEnd_2506147 := by
    simpa [prefixWord, tailWord_2506147, baseEnd_2506147] using wordTrace_append hprefix tailTrace_2506147
  have hstable : (prefixWord ++ tailWord_2506147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506147).length < 2 ^ (prefixWord ++ tailWord_2506147).sum := by decide
  have hdescent : baseEnd_2506147 < baseStart_2506147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506198 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2506198 : Nat := 118140960795 + 2506198 * 2 ^ 59
def prefixEnd_2506198 : Nat := 4983230072969 + 3 ^ 40 * 2506198 * 2
def baseEnd_2506198 : Nat := 285974264297086827222047

theorem tailTrace_2506198 : CollatzResearch.WordTrace tailWord_2506198 prefixEnd_2506198 285974264297086827222047 := by
  unfold tailWord_2506198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5713034410905009086670953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60939033716320096924490165 5713034410905009086670953)
  ·
    refine ⟨4284775808178756815003215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5713034410905009086670953 4284775808178756815003215)
    ·
      refine ⟨6427163712268135222504823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284775808178756815003215 6427163712268135222504823)
      ·
        refine ⟨9640745568402202833757235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6427163712268135222504823 9640745568402202833757235)
        ·
          refine ⟨14461118352603304250635853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640745568402202833757235 14461118352603304250635853)
          ·
            refine ⟨5422919382226239093988445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14461118352603304250635853 5422919382226239093988445)
            ·
              refine ⟨2033594768334839660245667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5422919382226239093988445 2033594768334839660245667)
              ·
                refine ⟨3050392152502259490368501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033594768334839660245667 3050392152502259490368501)
                ·
                  refine ⟨285974264297086827222047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050392152502259490368501 285974264297086827222047)
                  ·
                    rfl

theorem cell22_2506198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2506198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506198 prefixEnd_2506198 := by exact prefixLift 2506198
  have htrace : WordTrace (prefixWord ++ tailWord_2506198) baseStart_2506198 baseEnd_2506198 := by
    simpa [prefixWord, tailWord_2506198, baseEnd_2506198] using wordTrace_append hprefix tailTrace_2506198
  have hstable : (prefixWord ++ tailWord_2506198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506198).length < 2 ^ (prefixWord ++ tailWord_2506198).sum := by decide
  have hdescent : baseEnd_2506198 < baseStart_2506198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506211 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 1, 4]
def baseStart_2506211 : Nat := 118140960795 + 2506211 * 2 ^ 59
def prefixEnd_2506211 : Nat := 4983230072969 + 3 ^ 40 * 2506211 * 2
def baseEnd_2506211 : Nat := 857927243056932781091101

theorem tailTrace_2506211 : CollatzResearch.WordTrace tailWord_2506211 prefixEnd_2506211 857927243056932781091101 := by
  unfold tailWord_2506211
  simp only [CollatzResearch.WordTrace]
  refine ⟨91409024723433048606958487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60939349815622032404638991 91409024723433048606958487)
  ·
    refine ⟨137113537085149572910437731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91409024723433048606958487 137113537085149572910437731)
    ·
      refine ⟨205670305627724359365656597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137113537085149572910437731 205670305627724359365656597)
      ·
        refine ⟨9640795576299579345265153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 205670305627724359365656597 9640795576299579345265153)
        ·
          refine ⟨7230596682224684508948865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9640795576299579345265153 7230596682224684508948865)
          ·
            refine ⟨5422947511668513381711649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230596682224684508948865 5422947511668513381711649)
            ·
              refine ⟨4067210633751385036283737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5422947511668513381711649 4067210633751385036283737)
              ·
                refine ⟨3050407975313538777212803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067210633751385036283737 3050407975313538777212803)
                ·
                  refine ⟨4575611962970308165819205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050407975313538777212803 4575611962970308165819205)
                  ·
                    refine ⟨857927243056932781091101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575611962970308165819205 857927243056932781091101)
                    ·
                      rfl

theorem cell22_2506211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 4].length) (baseStart_2506211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506211 prefixEnd_2506211 := by exact prefixLift 2506211
  have htrace : WordTrace (prefixWord ++ tailWord_2506211) baseStart_2506211 baseEnd_2506211 := by
    simpa [prefixWord, tailWord_2506211, baseEnd_2506211] using wordTrace_append hprefix tailTrace_2506211
  have hstable : (prefixWord ++ tailWord_2506211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506211).length < 2 ^ (prefixWord ++ tailWord_2506211).sum := by decide
  have hdescent : baseEnd_2506211 < baseStart_2506211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506224 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_2506224 : Nat := 118140960795 + 2506224 * 2 ^ 59
def prefixEnd_2506224 : Nat := 4983230072969 + 3 ^ 40 * 2506224 * 2
def baseEnd_2506224 : Nat := 857931693222605080516061

theorem tailTrace_2506224 : CollatzResearch.WordTrace tailWord_2506224 prefixEnd_2506224 857931693222605080516061 := by
  unfold tailWord_2506224
  simp only [CollatzResearch.WordTrace]
  refine ⟨45704749436192975913590863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60939665914923967884787817 45704749436192975913590863)
  ·
    refine ⟨68557124154289463870386295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45704749436192975913590863 68557124154289463870386295)
    ·
      refine ⟨102835686231434195805579443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68557124154289463870386295 102835686231434195805579443)
      ·
        refine ⟨154253529347151293708369165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102835686231434195805579443 154253529347151293708369165)
        ·
          refine ⟨57845073505181735140638437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154253529347151293708369165 57845073505181735140638437)
          ·
            refine ⟨10845951282221575338869707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57845073505181735140638437 10845951282221575338869707)
            ·
              refine ⟨16268926923332363008304561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10845951282221575338869707 16268926923332363008304561)
              ·
                refine ⟨12201695192499272256228421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16268926923332363008304561 12201695192499272256228421)
                ·
                  refine ⟨2287817848593613548042829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12201695192499272256228421 2287817848593613548042829)
                  ·
                    refine ⟨857931693222605080516061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287817848593613548042829 857931693222605080516061)
                    ·
                      rfl

theorem cell22_2506224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_2506224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506224 prefixEnd_2506224 := by exact prefixLift 2506224
  have htrace : WordTrace (prefixWord ++ tailWord_2506224) baseStart_2506224 baseEnd_2506224 := by
    simpa [prefixWord, tailWord_2506224, baseEnd_2506224] using wordTrace_append hprefix tailTrace_2506224
  have hstable : (prefixWord ++ tailWord_2506224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506224).length < 2 ^ (prefixWord ++ tailWord_2506224).sum := by decide
  have hdescent : baseEnd_2506224 < baseStart_2506224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506237 : List Nat := [1, 4, 1, 1, 1, 4, 10]
def baseStart_2506237 : Nat := 118140960795 + 2506237 * 2 ^ 59
def prefixEnd_2506237 : Nat := 4983230072969 + 3 ^ 40 * 2506237 * 2
def baseEnd_2506237 : Nat := 31775412718084347405223

theorem tailTrace_2506237 : CollatzResearch.WordTrace tailWord_2506237 prefixEnd_2506237 31775412718084347405223 := by
  unfold tailWord_2506237
  simp only [CollatzResearch.WordTrace]
  refine ⟨91409973021338855047404965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60939982014225903364936643 91409973021338855047404965)
  ·
    refine ⟨17139369941501035321388431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91409973021338855047404965 17139369941501035321388431)
    ·
      refine ⟨25709054912251552982082647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17139369941501035321388431 25709054912251552982082647)
      ·
        refine ⟨38563582368377329473123971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25709054912251552982082647 38563582368377329473123971)
        ·
          refine ⟨57845373552565994209685957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38563582368377329473123971 57845373552565994209685957)
          ·
            refine ⟨10846007541106123914316117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57845373552565994209685957 10846007541106123914316117)
            ·
              refine ⟨31775412718084347405223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10846007541106123914316117 31775412718084347405223)
              ·
                rfl

theorem cell22_2506237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 10].length) (baseStart_2506237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506237 prefixEnd_2506237 := by exact prefixLift 2506237
  have htrace : WordTrace (prefixWord ++ tailWord_2506237) baseStart_2506237 baseEnd_2506237 := by
    simpa [prefixWord, tailWord_2506237, baseEnd_2506237] using wordTrace_append hprefix tailTrace_2506237
  have hstable : (prefixWord ++ tailWord_2506237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506237).length < 2 ^ (prefixWord ++ tailWord_2506237).sum := by decide
  have hdescent : baseEnd_2506237 < baseStart_2506237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506303 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 1, 3]
def baseStart_2506303 : Nat := 118140960795 + 2506303 * 2 ^ 59
def prefixEnd_2506303 : Nat := 4983230072969 + 3 ^ 40 * 2506303 * 2
def baseEnd_2506303 : Nat := 857958736537075207790819

theorem tailTrace_2506303 : CollatzResearch.WordTrace tailWord_2506303 prefixEnd_2506303 857958736537075207790819 := by
  unfold tailWord_2506303
  simp only [CollatzResearch.WordTrace]
  refine ⟨91412380239099748319307563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60941586826066498879538375 91412380239099748319307563)
  ·
    refine ⟨137118570358649622478961345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91412380239099748319307563 137118570358649622478961345)
    ·
      refine ⟨102838927768987216859221009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137118570358649622478961345 102838927768987216859221009)
      ·
        refine ⟨77129195826740412644415757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102838927768987216859221009 77129195826740412644415757)
        ·
          refine ⟨28923448435027654741655909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77129195826740412644415757 28923448435027654741655909)
          ·
            refine ⟨5423146581567685264060483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28923448435027654741655909 5423146581567685264060483)
            ·
              refine ⟨8134719872351527896090725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423146581567685264060483 8134719872351527896090725)
              ·
                refine ⟨1525259976065911480517011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8134719872351527896090725 1525259976065911480517011)
                ·
                  refine ⟨2287889964098867220775517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525259976065911480517011 2287889964098867220775517)
                  ·
                    refine ⟨857958736537075207790819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287889964098867220775517 857958736537075207790819)
                    ·
                      rfl

theorem cell22_2506303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_2506303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506303 prefixEnd_2506303 := by exact prefixLift 2506303
  have htrace : WordTrace (prefixWord ++ tailWord_2506303) baseStart_2506303 baseEnd_2506303 := by
    simpa [prefixWord, tailWord_2506303, baseEnd_2506303] using wordTrace_append hprefix tailTrace_2506303
  have hstable : (prefixWord ++ tailWord_2506303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506303).length < 2 ^ (prefixWord ++ tailWord_2506303).sum := by decide
  have hdescent : baseEnd_2506303 < baseStart_2506303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506314 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_2506314 : Nat := 118140960795 + 2506314 * 2 ^ 59
def prefixEnd_2506314 : Nat := 4983230072969 + 3 ^ 40 * 2506314 * 2
def baseEnd_2506314 : Nat := 857962502061874845765785

theorem tailTrace_2506314 : CollatzResearch.WordTrace tailWord_2506314 prefixEnd_2506314 857962502061874845765785 := by
  unfold tailWord_2506314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22853195360514974299489499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60941854294706598131971997 22853195360514974299489499)
  ·
    refine ⟨34279793040772461449234249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22853195360514974299489499 34279793040772461449234249)
    ·
      refine ⟨25709844780579346086925687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34279793040772461449234249 25709844780579346086925687)
      ·
        refine ⟨38564767170869019130388531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25709844780579346086925687 38564767170869019130388531)
        ·
          refine ⟨57847150756303528695582797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38564767170869019130388531 57847150756303528695582797)
          ·
            refine ⟨21692681533613823260843549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57847150756303528695582797 21692681533613823260843549)
            ·
              refine ⟨8134755575105183722816331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21692681533613823260843549 8134755575105183722816331)
              ·
                refine ⟨12202133362657775584224497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8134755575105183722816331 12202133362657775584224497)
                ·
                  refine ⟨9151600021993331688168373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12202133362657775584224497 9151600021993331688168373)
                  ·
                    refine ⟨857962502061874845765785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9151600021993331688168373 857962502061874845765785)
                    ·
                      rfl

theorem cell22_2506314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_2506314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506314 prefixEnd_2506314 := by exact prefixLift 2506314
  have htrace : WordTrace (prefixWord ++ tailWord_2506314) baseStart_2506314 baseEnd_2506314 := by
    simpa [prefixWord, tailWord_2506314, baseEnd_2506314] using wordTrace_append hprefix tailTrace_2506314
  have hstable : (prefixWord ++ tailWord_2506314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506314).length < 2 ^ (prefixWord ++ tailWord_2506314).sum := by decide
  have hdescent : baseEnd_2506314 < baseStart_2506314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506350 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_2506350 : Nat := 118140960795 + 2506350 * 2 ^ 59
def prefixEnd_2506350 : Nat := 4983230072969 + 3 ^ 40 * 2506350 * 2
def baseEnd_2506350 : Nat := 285991608532527583955225

theorem tailTrace_2506350 : CollatzResearch.WordTrace tailWord_2506350 prefixEnd_2506350 285991608532527583955225 := by
  unfold tailWord_2506350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11426761808741184418283563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60942729646619650230845669 11426761808741184418283563)
  ·
    refine ⟨17140142713111776627425345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11426761808741184418283563 17140142713111776627425345)
    ·
      refine ⟨12855107034833832470569009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17140142713111776627425345 12855107034833832470569009)
      ·
        refine ⟨9641330276125374352926757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12855107034833832470569009 9641330276125374352926757)
        ·
          refine ⟨1807749426773507691173767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9641330276125374352926757 1807749426773507691173767)
          ·
            refine ⟨2711624140160261536760651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807749426773507691173767 2711624140160261536760651)
            ·
              refine ⟨4067436210240392305140977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711624140160261536760651 4067436210240392305140977)
              ·
                refine ⟨3050577157680294228855733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067436210240392305140977 3050577157680294228855733)
                ·
                  refine ⟨285991608532527583955225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050577157680294228855733 285991608532527583955225)
                  ·
                    rfl

theorem cell22_2506350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_2506350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506350 prefixEnd_2506350 := by exact prefixLift 2506350
  have htrace : WordTrace (prefixWord ++ tailWord_2506350) baseStart_2506350 baseEnd_2506350 := by
    simpa [prefixWord, tailWord_2506350, baseEnd_2506350] using wordTrace_append hprefix tailTrace_2506350
  have hstable : (prefixWord ++ tailWord_2506350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506350).length < 2 ^ (prefixWord ++ tailWord_2506350).sum := by decide
  have hdescent : baseEnd_2506350 < baseStart_2506350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506361 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 4]
def baseStart_2506361 : Nat := 118140960795 + 2506361 * 2 ^ 59
def prefixEnd_2506361 : Nat := 4983230072969 + 3 ^ 40 * 2506361 * 2
def baseEnd_2506361 : Nat := 285992863707460796613547

theorem tailTrace_2506361 : CollatzResearch.WordTrace tailWord_2506361 prefixEnd_2506361 285992863707460796613547 := by
  unfold tailWord_2506361
  simp only [CollatzResearch.WordTrace]
  refine ⟨91414495672889624224918937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60942997115259749483279291 91414495672889624224918937)
  ·
    refine ⟨68560871754667218168689203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91414495672889624224918937 68560871754667218168689203)
    ·
      refine ⟨102841307632000827253033805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68560871754667218168689203 102841307632000827253033805)
      ·
        refine ⟨38565490362000310219887677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102841307632000827253033805 38565490362000310219887677)
        ·
          refine ⟨14462058885750116332457879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38565490362000310219887677 14462058885750116332457879)
          ·
            refine ⟨21693088328625174498686819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14462058885750116332457879 21693088328625174498686819)
            ·
              refine ⟨32539632492937761748030229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21693088328625174498686819 32539632492937761748030229)
              ·
                refine ⟨1525295273106457581938917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32539632492937761748030229 1525295273106457581938917)
                ·
                  refine ⟨285992863707460796613547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1525295273106457581938917 285992863707460796613547)
                  ·
                    rfl

theorem cell22_2506361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_2506361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506361 prefixEnd_2506361 := by exact prefixLift 2506361
  have htrace : WordTrace (prefixWord ++ tailWord_2506361) baseStart_2506361 baseEnd_2506361 := by
    simpa [prefixWord, tailWord_2506361, baseEnd_2506361] using wordTrace_append hprefix tailTrace_2506361
  have hstable : (prefixWord ++ tailWord_2506361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506361).length < 2 ^ (prefixWord ++ tailWord_2506361).sum := by decide
  have hdescent : baseEnd_2506361 < baseStart_2506361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506419 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_2506419 : Nat := 118140960795 + 2506419 * 2 ^ 59
def prefixEnd_2506419 : Nat := 4983230072969 + 3 ^ 40 * 2506419 * 2
def baseEnd_2506419 : Nat := 857998445707689571890463

theorem tailTrace_2506419 : CollatzResearch.WordTrace tailWord_2506419 prefixEnd_2506419 857998445707689571890463 := by
  unfold tailWord_2506419
  simp only [CollatzResearch.WordTrace]
  refine ⟨91416611106679500130530311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60944407404453000087020207 91416611106679500130530311)
  ·
    refine ⟨137124916660019250195795467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91416611106679500130530311 137124916660019250195795467)
    ·
      refine ⟨205687374990028875293693201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137124916660019250195795467 205687374990028875293693201)
      ·
        refine ⟨154265531242521656470269901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205687374990028875293693201 154265531242521656470269901)
        ·
          refine ⟨57849574215945621176351213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154265531242521656470269901 57849574215945621176351213)
          ·
            refine ⟨21693590330979607941131705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57849574215945621176351213 21693590330979607941131705)
            ·
              refine ⟨16270192748234705955848779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21693590330979607941131705 16270192748234705955848779)
              ·
                refine ⟨24405289122352058933773169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16270192748234705955848779 24405289122352058933773169)
                ·
                  refine ⟨18303966841764044200329877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24405289122352058933773169 18303966841764044200329877)
                  ·
                    refine ⟨857998445707689571890463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18303966841764044200329877 857998445707689571890463)
                    ·
                      rfl

theorem cell22_2506419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_2506419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506419 prefixEnd_2506419 := by exact prefixLift 2506419
  have htrace : WordTrace (prefixWord ++ tailWord_2506419) baseStart_2506419 baseEnd_2506419 := by
    simpa [prefixWord, tailWord_2506419, baseEnd_2506419] using wordTrace_append hprefix tailTrace_2506419
  have hstable : (prefixWord ++ tailWord_2506419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506419).length < 2 ^ (prefixWord ++ tailWord_2506419).sum := by decide
  have hdescent : baseEnd_2506419 < baseStart_2506419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506472 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 1, 3]
def baseStart_2506472 : Nat := 118140960795 + 2506472 * 2 ^ 59
def prefixEnd_2506472 : Nat := 4983230072969 + 3 ^ 40 * 2506472 * 2
def baseEnd_2506472 : Nat := 858016588690815100315301

theorem tailTrace_2506472 : CollatzResearch.WordTrace tailWord_2506472 prefixEnd_2506472 858016588690815100315301 := by
  unfold tailWord_2506472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45709272087743745091104835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60945696116991660121473113 45709272087743745091104835)
  ·
    refine ⟨68563908131615617636657253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45709272087743745091104835 68563908131615617636657253)
    ·
      refine ⟨12855732774677928306873235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68563908131615617636657253 12855732774677928306873235)
      ·
        refine ⟨19283599162016892460309853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12855732774677928306873235 19283599162016892460309853)
        ·
          refine ⟨7231349685756334672616195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19283599162016892460309853 7231349685756334672616195)
          ·
            refine ⟨10847024528634502008924293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231349685756334672616195 10847024528634502008924293)
            ·
              refine ⟨2033817099118969126673305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10847024528634502008924293 2033817099118969126673305)
              ·
                refine ⟨1525362824339226845004979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033817099118969126673305 1525362824339226845004979)
                ·
                  refine ⟨2288044236508840267507469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525362824339226845004979 2288044236508840267507469)
                  ·
                    refine ⟨858016588690815100315301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288044236508840267507469 858016588690815100315301)
                    ·
                      rfl

theorem cell22_2506472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_2506472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506472 prefixEnd_2506472 := by exact prefixLift 2506472
  have htrace : WordTrace (prefixWord ++ tailWord_2506472) baseStart_2506472 baseEnd_2506472 := by
    simpa [prefixWord, tailWord_2506472, baseEnd_2506472] using wordTrace_append hprefix tailTrace_2506472
  have hstable : (prefixWord ++ tailWord_2506472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506472).length < 2 ^ (prefixWord ++ tailWord_2506472).sum := by decide
  have hdescent : baseEnd_2506472 < baseStart_2506472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506481 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_2506481 : Nat := 118140960795 + 2506481 * 2 ^ 59
def prefixEnd_2506481 : Nat := 4983230072969 + 3 ^ 40 * 2506481 * 2
def baseEnd_2506481 : Nat := 858019669574742076840273

theorem tailTrace_2506481 : CollatzResearch.WordTrace tailWord_2506481 prefixEnd_2506481 858019669574742076840273 := by
  unfold tailWord_2506481
  simp only [CollatzResearch.WordTrace]
  refine ⟨91418872432454884719287297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60945914954969923146191531 91418872432454884719287297)
  ·
    refine ⟨68564154324341163539465473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91418872432454884719287297 68564154324341163539465473)
    ·
      refine ⟨51423115743255872654599105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68564154324341163539465473 51423115743255872654599105)
      ·
        refine ⟨38567336807441904490949329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51423115743255872654599105 38567336807441904490949329)
        ·
          refine ⟨28925502605581428368211997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38567336807441904490949329 28925502605581428368211997)
          ·
            refine ⟨10847063477093035638079499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28925502605581428368211997 10847063477093035638079499)
            ·
              refine ⟨16270595215639553457119249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10847063477093035638079499 16270595215639553457119249)
              ·
                refine ⟨12202946411729665092839437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16270595215639553457119249 12202946411729665092839437)
                ·
                  refine ⟨4576104904398624409814789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12202946411729665092839437 4576104904398624409814789)
                  ·
                    refine ⟨858019669574742076840273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576104904398624409814789 858019669574742076840273)
                    ·
                      rfl

theorem cell22_2506481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_2506481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506481 prefixEnd_2506481 := by exact prefixLift 2506481
  have htrace : WordTrace (prefixWord ++ tailWord_2506481) baseStart_2506481 baseEnd_2506481 := by
    simpa [prefixWord, tailWord_2506481, baseEnd_2506481] using wordTrace_append hprefix tailTrace_2506481
  have hstable : (prefixWord ++ tailWord_2506481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506481).length < 2 ^ (prefixWord ++ tailWord_2506481).sum := by decide
  have hdescent : baseEnd_2506481 < baseStart_2506481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506498 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2506498 : Nat := 118140960795 + 2506498 * 2 ^ 59
def prefixEnd_2506498 : Nat := 4983230072969 + 3 ^ 40 * 2506498 * 2
def baseEnd_2506498 : Nat := 858025489022159699165221

theorem tailTrace_2506498 : CollatzResearch.WordTrace tailWord_2506498 prefixEnd_2506498 858025489022159699165221 := by
  unfold tailWord_2506498
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854873118348324155664037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60946328315595531081770765 22854873118348324155664037)
  ·
    refine ⟨4285288709690310779187007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22854873118348324155664037 4285288709690310779187007)
    ·
      refine ⟨6427933064535466168780511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4285288709690310779187007 6427933064535466168780511)
      ·
        refine ⟨9641899596803199253170767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6427933064535466168780511 9641899596803199253170767)
        ·
          refine ⟨14462849395204798879756151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9641899596803199253170767 14462849395204798879756151)
          ·
            refine ⟨21694274092807198319634227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14462849395204798879756151 21694274092807198319634227)
            ·
              refine ⟨32541411139210797479451341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21694274092807198319634227 32541411139210797479451341)
              ·
                refine ⟨12203029177204049054794253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32541411139210797479451341 12203029177204049054794253)
                ·
                  refine ⟨4576135941451518395547845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12203029177204049054794253 4576135941451518395547845)
                  ·
                    refine ⟨858025489022159699165221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576135941451518395547845 858025489022159699165221)
                    ·
                      rfl

theorem cell22_2506498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2506498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506498 prefixEnd_2506498 := by exact prefixLift 2506498
  have htrace : WordTrace (prefixWord ++ tailWord_2506498) baseStart_2506498 baseEnd_2506498 := by
    simpa [prefixWord, tailWord_2506498, baseEnd_2506498] using wordTrace_append hprefix tailTrace_2506498
  have hstable : (prefixWord ++ tailWord_2506498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506498).length < 2 ^ (prefixWord ++ tailWord_2506498).sum := by decide
  have hdescent : baseEnd_2506498 < baseStart_2506498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506528 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_2506528 : Nat := 118140960795 + 2506528 * 2 ^ 59
def prefixEnd_2506528 : Nat := 4983230072969 + 3 ^ 40 * 2506528 * 2
def baseEnd_2506528 : Nat := 858035758635249620915129

theorem tailTrace_2506528 : CollatzResearch.WordTrace tailWord_2506528 prefixEnd_2506528 858035758635249620915129 := by
  unfold tailWord_2506528
  simp only [CollatzResearch.WordTrace]
  refine ⟨45710293331642305873124119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60947057775523074497498825 45710293331642305873124119)
  ·
    refine ⟨68565439997463458809686179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45710293331642305873124119 68565439997463458809686179)
    ·
      refine ⟨102848159996195188214529269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68565439997463458809686179 102848159996195188214529269)
      ·
        refine ⟨9642014999643298895112119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102848159996195188214529269 9642014999643298895112119)
        ·
          refine ⟨14463022499464948342668179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9642014999643298895112119 14463022499464948342668179)
          ·
            refine ⟨21694533749197422514002269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14463022499464948342668179 21694533749197422514002269)
            ·
              refine ⟨8135450155949033442750851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21694533749197422514002269 8135450155949033442750851)
              ·
                refine ⟨12203175233923550164126277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8135450155949033442750851 12203175233923550164126277)
                ·
                  refine ⟨2288095356360665655773677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12203175233923550164126277 2288095356360665655773677)
                  ·
                    refine ⟨858035758635249620915129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288095356360665655773677 858035758635249620915129)
                    ·
                      rfl

theorem cell22_2506528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_2506528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506528 prefixEnd_2506528 := by exact prefixLift 2506528
  have htrace : WordTrace (prefixWord ++ tailWord_2506528) baseStart_2506528 baseEnd_2506528 := by
    simpa [prefixWord, tailWord_2506528, baseEnd_2506528] using wordTrace_append hprefix tailTrace_2506528
  have hstable : (prefixWord ++ tailWord_2506528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506528).length < 2 ^ (prefixWord ++ tailWord_2506528).sum := by decide
  have hdescent : baseEnd_2506528 < baseStart_2506528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506558 : List Nat := [4, 2, 1, 2, 2, 2, 1, 8]
def baseStart_2506558 : Nat := 118140960795 + 2506558 * 2 ^ 59
def prefixEnd_2506558 : Nat := 4983230072969 + 3 ^ 40 * 2506558 * 2
def baseEnd_2506558 : Nat := 95338447583148838073893

theorem tailTrace_2506558 : CollatzResearch.WordTrace tailWord_2506558 prefixEnd_2506558 95338447583148838073893 := by
  unfold tailWord_2506558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427710106646990858730041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60947787235450617913226885 11427710106646990858730041)
  ·
    refine ⟨8570782579985243144047531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11427710106646990858730041 8570782579985243144047531)
    ·
      refine ⟨12856173869977864716071297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8570782579985243144047531 12856173869977864716071297)
      ·
        refine ⟨9642130402483398537053473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12856173869977864716071297 9642130402483398537053473)
        ·
          refine ⟨7231597801862548902790105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9642130402483398537053473 7231597801862548902790105)
          ·
            refine ⟨5423698351396911677092579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7231597801862548902790105 5423698351396911677092579)
            ·
              refine ⟨8135547527095367515638869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423698351396911677092579 8135547527095367515638869)
              ·
                refine ⟨95338447583148838073893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8135547527095367515638869 95338447583148838073893)
                ·
                  rfl

theorem cell22_2506558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_2506558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506558 prefixEnd_2506558 := by exact prefixLift 2506558
  have htrace : WordTrace (prefixWord ++ tailWord_2506558) baseStart_2506558 baseEnd_2506558 := by
    simpa [prefixWord, tailWord_2506558, baseEnd_2506558] using wordTrace_append hprefix tailTrace_2506558
  have hstable : (prefixWord ++ tailWord_2506558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506558).length < 2 ^ (prefixWord ++ tailWord_2506558).sum := by decide
  have hdescent : baseEnd_2506558 < baseStart_2506558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506586 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_2506586 : Nat := 118140960795 + 2506586 * 2 ^ 59
def prefixEnd_2506586 : Nat := 4983230072969 + 3 ^ 40 * 2506586 * 2
def baseEnd_2506586 : Nat := 286018537740185600988317

theorem tailTrace_2506586 : CollatzResearch.WordTrace tailWord_2506586 prefixEnd_2506586 286018537740185600988317 := by
  unfold tailWord_2506586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22855675524268621912964903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60948468064716325101239741 22855675524268621912964903)
  ·
    refine ⟨34283513286402932869447355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22855675524268621912964903 34283513286402932869447355)
    ·
      refine ⟨51425269929604399304171033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34283513286402932869447355 51425269929604399304171033)
      ·
        refine ⟨38568952447203299478128275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51425269929604399304171033 38568952447203299478128275)
        ·
          refine ⟨57853428670804949217192413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38568952447203299478128275 57853428670804949217192413)
          ·
            refine ⟨21695035751551855956447155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57853428670804949217192413 21695035751551855956447155)
            ·
              refine ⟨32542553627327783934670733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21695035751551855956447155 32542553627327783934670733)
              ·
                refine ⟨12203457610247918975501525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32542553627327783934670733 12203457610247918975501525)
                ·
                  refine ⟨286018537740185600988317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12203457610247918975501525 286018537740185600988317)
                  ·
                    rfl

theorem cell22_2506586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_2506586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506586 prefixEnd_2506586 := by exact prefixLift 2506586
  have htrace : WordTrace (prefixWord ++ tailWord_2506586) baseStart_2506586 baseEnd_2506586 := by
    simpa [prefixWord, tailWord_2506586, baseEnd_2506586] using wordTrace_append hprefix tailTrace_2506586
  have hstable : (prefixWord ++ tailWord_2506586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506586).length < 2 ^ (prefixWord ++ tailWord_2506586).sum := by decide
  have hdescent : baseEnd_2506586 < baseStart_2506586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_2506601 : Nat := 118140960795 + 2506601 * 2 ^ 59
def prefixEnd_2506601 : Nat := 4983230072969 + 3 ^ 40 * 2506601 * 2
def baseEnd_2506601 : Nat := 858060748027101763839905

theorem tailTrace_2506601 : CollatzResearch.WordTrace tailWord_2506601 prefixEnd_2506601 858060748027101763839905 := by
  unfold tailWord_2506601
  simp only [CollatzResearch.WordTrace]
  refine ⟨91423249192020145213655657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60948832794680096809103771 91423249192020145213655657)
  ·
    refine ⟨68567436894015108910241743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91423249192020145213655657 68567436894015108910241743)
    ·
      refine ⟨102851155341022663365362615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68567436894015108910241743 102851155341022663365362615)
      ·
        refine ⟨154276733011533995048043923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102851155341022663365362615 154276733011533995048043923)
        ·
          refine ⟨231415099517300992572065885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154276733011533995048043923 231415099517300992572065885)
          ·
            refine ⟨86780662318987872214524707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231415099517300992572065885 86780662318987872214524707)
            ·
              refine ⟨130170993478481808321787061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86780662318987872214524707 130170993478481808321787061)
              ·
                refine ⟨12203530638607669530167537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130170993478481808321787061 12203530638607669530167537)
                ·
                  refine ⟨9152647978955752147625653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12203530638607669530167537 9152647978955752147625653)
                  ·
                    refine ⟨858060748027101763839905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9152647978955752147625653 858060748027101763839905)
                    ·
                      rfl

theorem cell22_2506601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_2506601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506601 prefixEnd_2506601 := by exact prefixLift 2506601
  have htrace : WordTrace (prefixWord ++ tailWord_2506601) baseStart_2506601 baseEnd_2506601 := by
    simpa [prefixWord, tailWord_2506601, baseEnd_2506601] using wordTrace_append hprefix tailTrace_2506601
  have hstable : (prefixWord ++ tailWord_2506601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506601).length < 2 ^ (prefixWord ++ tailWord_2506601).sum := by decide
  have hdescent : baseEnd_2506601 < baseStart_2506601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506714 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_2506714 : Nat := 118140960795 + 2506714 * 2 ^ 59
def prefixEnd_2506714 : Nat := 4983230072969 + 3 ^ 40 * 2506714 * 2
def baseEnd_2506714 : Nat := 858099430236407135764559

theorem tailTrace_2506714 : CollatzResearch.WordTrace tailWord_2506714 prefixEnd_2506714 858099430236407135764559 := by
  unfold tailWord_2506714
  simp only [CollatzResearch.WordTrace]
  refine ⟨22856842660152691378129799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60951580427073843675012797 22856842660152691378129799)
  ·
    refine ⟨34285263990229037067194699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22856842660152691378129799 34285263990229037067194699)
    ·
      refine ⟨51427895985343555600792049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34285263990229037067194699 51427895985343555600792049)
      ·
        refine ⟨38570921989007666700594037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51427895985343555600792049 38570921989007666700594037)
        ·
          refine ⟨3616023936469468753180691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38570921989007666700594037 3616023936469468753180691)
          ·
            refine ⟨5424035904704203129771037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616023936469468753180691 5424035904704203129771037)
            ·
              refine ⟨2034013464264076173664139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5424035904704203129771037 2034013464264076173664139)
              ·
                refine ⟨3051020196396114260496209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034013464264076173664139 3051020196396114260496209)
                ·
                  refine ⟨2288265147297085695372157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051020196396114260496209 2288265147297085695372157)
                  ·
                    refine ⟨858099430236407135764559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288265147297085695372157 858099430236407135764559)
                    ·
                      rfl

theorem cell22_2506714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_2506714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506714 prefixEnd_2506714 := by exact prefixLift 2506714
  have htrace : WordTrace (prefixWord ++ tailWord_2506714) baseStart_2506714 baseEnd_2506714 := by
    simpa [prefixWord, tailWord_2506714, baseEnd_2506714] using wordTrace_append hprefix tailTrace_2506714
  have hstable : (prefixWord ++ tailWord_2506714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506714).length < 2 ^ (prefixWord ++ tailWord_2506714).sum := by decide
  have hdescent : baseEnd_2506714 < baseStart_2506714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506727 : List Nat := [1, 1, 5, 2, 3, 2, 2, 6]
def baseStart_2506727 : Nat := 118140960795 + 2506727 * 2 ^ 59
def prefixEnd_2506727 : Nat := 4983230072969 + 3 ^ 40 * 2506727 * 2
def baseEnd_2506727 : Nat := 95344875600231048354391

theorem tailTrace_2506727 : CollatzResearch.WordTrace tailWord_2506727 prefixEnd_2506727 95344875600231048354391 := by
  unfold tailWord_2506727
  simp only [CollatzResearch.WordTrace]
  refine ⟨91427844789563668732742435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60951896526375779155161623 91427844789563668732742435)
  ·
    refine ⟨137141767184345503099113653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91427844789563668732742435 137141767184345503099113653)
    ·
      refine ⟨12857040673532390915541905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137141767184345503099113653 12857040673532390915541905)
      ·
        refine ⟨9642780505149293186656429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12857040673532390915541905 9642780505149293186656429)
        ·
          refine ⟨3616042689430984944996161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9642780505149293186656429 3616042689430984944996161)
          ·
            refine ⟨2712032017073238708747121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3616042689430984944996161 2712032017073238708747121)
            ·
              refine ⟨2034024012804929031560341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712032017073238708747121 2034024012804929031560341)
              ·
                refine ⟨95344875600231048354391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2034024012804929031560341 95344875600231048354391)
                ·
                  rfl

theorem cell22_2506727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 6].length) (baseStart_2506727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506727 prefixEnd_2506727 := by exact prefixLift 2506727
  have htrace : WordTrace (prefixWord ++ tailWord_2506727) baseStart_2506727 baseEnd_2506727 := by
    simpa [prefixWord, tailWord_2506727, baseEnd_2506727] using wordTrace_append hprefix tailTrace_2506727
  have hstable : (prefixWord ++ tailWord_2506727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506727).length < 2 ^ (prefixWord ++ tailWord_2506727).sum := by decide
  have hdescent : baseEnd_2506727 < baseStart_2506727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506765 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2506765 : Nat := 118140960795 + 2506765 * 2 ^ 59
def prefixEnd_2506765 : Nat := 4983230072969 + 3 ^ 40 * 2506765 * 2
def baseEnd_2506765 : Nat := 858116888578660002739403

theorem tailTrace_2506765 : CollatzResearch.WordTrace tailWord_2506765 prefixEnd_2506765 858116888578660002739403 := by
  unfold tailWord_2506765
  simp only [CollatzResearch.WordTrace]
  refine ⟨91429230763426001222625749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60952820508950667481750499 91429230763426001222625749)
  ·
    refine ⟨2142872596017796903655291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 91429230763426001222625749 2142872596017796903655291)
    ·
      refine ⟨3214308894026695355482937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142872596017796903655291 3214308894026695355482937)
      ·
        refine ⟨2410731670520021516612203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3214308894026695355482937 2410731670520021516612203)
        ·
          refine ⟨3616097505780032274918305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410731670520021516612203 3616097505780032274918305)
          ·
            refine ⟨2712073129335024206188729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3616097505780032274918305 2712073129335024206188729)
            ·
              refine ⟨2034054847001268154641547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712073129335024206188729 2034054847001268154641547)
              ·
                refine ⟨3051082270501902231962321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034054847001268154641547 3051082270501902231962321)
                ·
                  refine ⟨2288311702876426673971741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051082270501902231962321 2288311702876426673971741)
                  ·
                    refine ⟨858116888578660002739403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288311702876426673971741 858116888578660002739403)
                    ·
                      rfl

theorem cell22_2506765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2506765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506765 prefixEnd_2506765 := by exact prefixLift 2506765
  have htrace : WordTrace (prefixWord ++ tailWord_2506765) baseStart_2506765 baseEnd_2506765 := by
    simpa [prefixWord, tailWord_2506765, baseEnd_2506765] using wordTrace_append hprefix tailTrace_2506765
  have hstable : (prefixWord ++ tailWord_2506765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506765).length < 2 ^ (prefixWord ++ tailWord_2506765).sum := by decide
  have hdescent : baseEnd_2506765 < baseStart_2506765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506768 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_2506768 : Nat := 118140960795 + 2506768 * 2 ^ 59
def prefixEnd_2506768 : Nat := 4983230072969 + 3 ^ 40 * 2506768 * 2
def baseEnd_2506768 : Nat := 858117915539968994914393

theorem tailTrace_2506768 : CollatzResearch.WordTrace tailWord_2506768 prefixEnd_2506768 858117915539968994914393 := by
  unfold tailWord_2506768
  simp only [CollatzResearch.WordTrace]
  refine ⟨45714670091207566367492479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60952893454943421823323305 45714670091207566367492479)
  ·
    refine ⟨68572005136811349551238719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45714670091207566367492479 68572005136811349551238719)
    ·
      refine ⟨102858007705217024326858079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68572005136811349551238719 102858007705217024326858079)
      ·
        refine ⟨154287011557825536490287119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102858007705217024326858079 154287011557825536490287119)
        ·
          refine ⟨231430517336738304735430679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154287011557825536490287119 231430517336738304735430679)
          ·
            refine ⟨347145776005107457103146019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231430517336738304735430679 347145776005107457103146019)
            ·
              refine ⟨520718664007661185654719029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347145776005107457103146019 520718664007661185654719029)
              ·
                refine ⟨48817374750718236155129909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 520718664007661185654719029 48817374750718236155129909)
                ·
                  refine ⟨4576628882879834639543429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48817374750718236155129909 4576628882879834639543429)
                  ·
                    refine ⟨858117915539968994914393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576628882879834639543429 858117915539968994914393)
                    ·
                      rfl

theorem cell22_2506768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_2506768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506768 prefixEnd_2506768 := by exact prefixLift 2506768
  have htrace : WordTrace (prefixWord ++ tailWord_2506768) baseStart_2506768 baseEnd_2506768 := by
    simpa [prefixWord, tailWord_2506768, baseEnd_2506768] using wordTrace_append hprefix tailTrace_2506768
  have hstable : (prefixWord ++ tailWord_2506768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506768).length < 2 ^ (prefixWord ++ tailWord_2506768).sum := by decide
  have hdescent : baseEnd_2506768 < baseStart_2506768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506783 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 8]
def baseStart_2506783 : Nat := 118140960795 + 2506783 * 2 ^ 59
def prefixEnd_2506783 : Nat := 4983230072969 + 3 ^ 40 * 2506783 * 2
def baseEnd_2506783 : Nat := 286041016782171318596449

theorem tailTrace_2506783 : CollatzResearch.WordTrace tailWord_2506783 prefixEnd_2506783 286041016782171318596449 := by
  unfold tailWord_2506783
  simp only [CollatzResearch.WordTrace]
  refine ⟨91429887277360790296781003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60953258184907193531187335 91429887277360790296781003)
  ·
    refine ⟨137144830916041185445171505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91429887277360790296781003 137144830916041185445171505)
    ·
      refine ⟨102858623187030889083878629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137144830916041185445171505 102858623187030889083878629)
      ·
        refine ⟨19285991847568291703227243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102858623187030889083878629 19285991847568291703227243)
        ·
          refine ⟨28928987771352437554840865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19285991847568291703227243 28928987771352437554840865)
          ·
            refine ⟨21696740828514328166130649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28928987771352437554840865 21696740828514328166130649)
            ·
              refine ⟨16272555621385746124597987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21696740828514328166130649 16272555621385746124597987)
              ·
                refine ⟨24408833432078619186896981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16272555621385746124597987 24408833432078619186896981)
                ·
                  refine ⟨286041016782171318596449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24408833432078619186896981 286041016782171318596449)
                  ·
                    rfl

theorem cell22_2506783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_2506783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506783 prefixEnd_2506783 := by exact prefixLift 2506783
  have htrace : WordTrace (prefixWord ++ tailWord_2506783) baseStart_2506783 baseEnd_2506783 := by
    simpa [prefixWord, tailWord_2506783, baseEnd_2506783] using wordTrace_append hprefix tailTrace_2506783
  have hstable : (prefixWord ++ tailWord_2506783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506783).length < 2 ^ (prefixWord ++ tailWord_2506783).sum := by decide
  have hdescent : baseEnd_2506783 < baseStart_2506783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506815 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 4, 3]
def baseStart_2506815 : Nat := 118140960795 + 2506815 * 2 ^ 59
def prefixEnd_2506815 : Nat := 4983230072969 + 3 ^ 40 * 2506815 * 2
def baseEnd_2506815 : Nat := 858134004600476538989249

theorem tailTrace_2506815 : CollatzResearch.WordTrace tailWord_2506815 prefixEnd_2506815 858134004600476538989249 := by
  unfold tailWord_2506815
  simp only [CollatzResearch.WordTrace]
  refine ⟨91431054413244859761945899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60954036275496573174630599 91431054413244859761945899)
  ·
    refine ⟨137146581619867289642918849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91431054413244859761945899 137146581619867289642918849)
    ·
      refine ⟨102859936214900467232189137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137146581619867289642918849 102859936214900467232189137)
      ·
        refine ⟨77144952161175350424141853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102859936214900467232189137 77144952161175350424141853)
        ·
          refine ⟨28929357060440756409053195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77144952161175350424141853 28929357060440756409053195)
          ·
            refine ⟨43394035590661134613579793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28929357060440756409053195 43394035590661134613579793)
            ·
              refine ⟨32545526692995850960184845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43394035590661134613579793 32545526692995850960184845)
              ·
                refine ⟨12204572509873444110069317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32545526692995850960184845 12204572509873444110069317)
                ·
                  refine ⟨2288357345601270770637997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12204572509873444110069317 2288357345601270770637997)
                  ·
                    refine ⟨858134004600476538989249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288357345601270770637997 858134004600476538989249)
                    ·
                      rfl

theorem cell22_2506815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_2506815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506815 prefixEnd_2506815 := by exact prefixLift 2506815
  have htrace : WordTrace (prefixWord ++ tailWord_2506815) baseStart_2506815 baseEnd_2506815 := by
    simpa [prefixWord, tailWord_2506815, baseEnd_2506815] using wordTrace_append hprefix tailTrace_2506815
  have hstable : (prefixWord ++ tailWord_2506815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506815).length < 2 ^ (prefixWord ++ tailWord_2506815).sum := by decide
  have hdescent : baseEnd_2506815 < baseStart_2506815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506877 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_2506877 : Nat := 118140960795 + 2506877 * 2 ^ 59
def prefixEnd_2506877 : Nat := 4983230072969 + 3 ^ 40 * 2506877 * 2
def baseEnd_2506877 : Nat := 858155228467529043939059

theorem tailTrace_2506877 : CollatzResearch.WordTrace tailWord_2506877 prefixEnd_2506877 858155228467529043939059 := by
  unfold tailWord_2506877
  simp only [CollatzResearch.WordTrace]
  refine ⟨91433315739020244350702885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60955543826013496233801923 91433315739020244350702885)
  ·
    refine ⟨17143746701066295815756791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91433315739020244350702885 17143746701066295815756791)
    ·
      refine ⟨25715620051599443723635187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17143746701066295815756791 25715620051599443723635187)
      ·
        refine ⟨38573430077399165585452781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25715620051599443723635187 38573430077399165585452781)
        ·
          refine ⟨14465036279024687094544793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38573430077399165585452781 14465036279024687094544793)
          ·
            refine ⟨10848777209268515320908595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14465036279024687094544793 10848777209268515320908595)
            ·
              refine ⟨16273165813902772981362893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10848777209268515320908595 16273165813902772981362893)
              ·
                refine ⟨6102437180213539868011085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16273165813902772981362893 6102437180213539868011085)
                ·
                  refine ⟨2288413942580077450504157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6102437180213539868011085 2288413942580077450504157)
                  ·
                    refine ⟨858155228467529043939059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288413942580077450504157 858155228467529043939059)
                    ·
                      rfl

theorem cell22_2506877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_2506877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506877 prefixEnd_2506877 := by exact prefixLift 2506877
  have htrace : WordTrace (prefixWord ++ tailWord_2506877) baseStart_2506877 baseEnd_2506877 := by
    simpa [prefixWord, tailWord_2506877, baseEnd_2506877] using wordTrace_append hprefix tailTrace_2506877
  have hstable : (prefixWord ++ tailWord_2506877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506877).length < 2 ^ (prefixWord ++ tailWord_2506877).sum := by decide
  have hdescent : baseEnd_2506877 < baseStart_2506877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506902 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2506902 : Nat := 118140960795 + 2506902 * 2 ^ 59
def prefixEnd_2506902 : Nat := 4983230072969 + 3 ^ 40 * 2506902 * 2
def baseEnd_2506902 : Nat := 286054595492812437354661

theorem tailTrace_2506902 : CollatzResearch.WordTrace tailWord_2506902 prefixEnd_2506902 286054595492812437354661 := by
  unfold tailWord_2506902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5714639222745604601272685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60956151709286449080241973 5714639222745604601272685)
  ·
    refine ⟨2142989708529601725477257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5714639222745604601272685 2142989708529601725477257)
    ·
      refine ⟨1607242281397201294107943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2142989708529601725477257 1607242281397201294107943)
      ·
        refine ⟨2410863422095801941161915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607242281397201294107943 2410863422095801941161915)
        ·
          refine ⟨3616295133143702911742873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410863422095801941161915 3616295133143702911742873)
          ·
            refine ⟨2712221349857777183807155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3616295133143702911742873 2712221349857777183807155)
            ·
              refine ⟨4068332024786665775710733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712221349857777183807155 4068332024786665775710733)
              ·
                refine ⟨1525624509294999665891525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4068332024786665775710733 1525624509294999665891525)
                ·
                  refine ⟨286054595492812437354661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1525624509294999665891525 286054595492812437354661)
                  ·
                    rfl

theorem cell22_2506902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2506902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506902 prefixEnd_2506902 := by exact prefixLift 2506902
  have htrace : WordTrace (prefixWord ++ tailWord_2506902) baseStart_2506902 baseEnd_2506902 := by
    simpa [prefixWord, tailWord_2506902, baseEnd_2506902] using wordTrace_append hprefix tailTrace_2506902
  have hstable : (prefixWord ++ tailWord_2506902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506902).length < 2 ^ (prefixWord ++ tailWord_2506902).sum := by decide
  have hdescent : baseEnd_2506902 < baseStart_2506902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506911 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 1, 3]
def baseStart_2506911 : Nat := 118140960795 + 2506911 * 2 ^ 59
def prefixEnd_2506911 : Nat := 4983230072969 + 3 ^ 40 * 2506911 * 2
def baseEnd_2506911 : Nat := 858166867362364288588955

theorem tailTrace_2506911 : CollatzResearch.WordTrace tailWord_2506911 prefixEnd_2506911 858166867362364288588955 := by
  unfold tailWord_2506911
  simp only [CollatzResearch.WordTrace]
  refine ⟨91434555820897068157440587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60956370547264712104960391 91434555820897068157440587)
  ·
    refine ⟨137151833731345602236160881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91434555820897068157440587 137151833731345602236160881)
    ·
      refine ⟨102863875298509201677120661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137151833731345602236160881 102863875298509201677120661)
      ·
        refine ⟨4821744154617618828615031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102863875298509201677120661 4821744154617618828615031)
        ·
          refine ⟨7232616231926428242922547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821744154617618828615031 7232616231926428242922547)
          ·
            refine ⟨10848924347889642364383821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232616231926428242922547 10848924347889642364383821)
            ·
              refine ⟨4068346630458615886643933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10848924347889642364383821 4068346630458615886643933)
              ·
                refine ⟨1525629986421980957491475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4068346630458615886643933 1525629986421980957491475)
                ·
                  refine ⟨2288444979632971436237213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525629986421980957491475 2288444979632971436237213)
                  ·
                    refine ⟨858166867362364288588955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288444979632971436237213 858166867362364288588955)
                    ·
                      rfl

theorem cell22_2506911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_2506911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506911 prefixEnd_2506911 := by exact prefixLift 2506911
  have htrace : WordTrace (prefixWord ++ tailWord_2506911) baseStart_2506911 baseEnd_2506911 := by
    simpa [prefixWord, tailWord_2506911, baseEnd_2506911] using wordTrace_append hprefix tailTrace_2506911
  have hstable : (prefixWord ++ tailWord_2506911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506911).length < 2 ^ (prefixWord ++ tailWord_2506911).sum := by decide
  have hdescent : baseEnd_2506911 < baseStart_2506911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506984 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_2506984 : Nat := 118140960795 + 2506984 * 2 ^ 59
def prefixEnd_2506984 : Nat := 4983230072969 + 3 ^ 40 * 2506984 * 2
def baseEnd_2506984 : Nat := 858191856754216431513731

theorem tailTrace_2506984 : CollatzResearch.WordTrace tailWord_2506984 prefixEnd_2506984 858191856754216431513731 := by
  unfold tailWord_2506984
  simp only [CollatzResearch.WordTrace]
  refine ⟨45718609174816300812424003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60958145566421734416565337 45718609174816300812424003)
  ·
    refine ⟨68577913762224451218636005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45718609174816300812424003 68577913762224451218636005)
    ·
      refine ⟨12858358830417084603494251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68577913762224451218636005 12858358830417084603494251)
      ·
        refine ⟨19287538245625626905241377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12858358830417084603494251 19287538245625626905241377)
        ·
          refine ⟨14465653684219220178931033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19287538245625626905241377 14465653684219220178931033)
          ·
            refine ⟨10849240263164415134198275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14465653684219220178931033 10849240263164415134198275)
            ·
              refine ⟨16273860394746622701297413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10849240263164415134198275 16273860394746622701297413)
              ·
                refine ⟨3051348824014991756493265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16273860394746622701297413 3051348824014991756493265)
                ·
                  refine ⟨2288511618011243817369949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051348824014991756493265 2288511618011243817369949)
                  ·
                    refine ⟨858191856754216431513731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288511618011243817369949 858191856754216431513731)
                    ·
                      rfl

theorem cell22_2506984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_2506984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2506984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2506984 prefixEnd_2506984 := by exact prefixLift 2506984
  have htrace : WordTrace (prefixWord ++ tailWord_2506984) baseStart_2506984 baseEnd_2506984 := by
    simpa [prefixWord, tailWord_2506984, baseEnd_2506984] using wordTrace_append hprefix tailTrace_2506984
  have hstable : (prefixWord ++ tailWord_2506984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506984).length < 2 ^ (prefixWord ++ tailWord_2506984).sum := by decide
  have hdescent : baseEnd_2506984 < baseStart_2506984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507059 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 5]
def baseStart_2507059 : Nat := 118140960795 + 2507059 * 2 ^ 59
def prefixEnd_2507059 : Nat := 4983230072969 + 3 ^ 40 * 2507059 * 2
def baseEnd_2507059 : Nat := 286072510262313745296167

theorem tailTrace_2507059 : CollatzResearch.WordTrace tailWord_2507059 prefixEnd_2507059 286072510262313745296167 := by
  unfold tailWord_2507059
  simp only [CollatzResearch.WordTrace]
  refine ⟨91439953824360889433828231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60959969216240592955885487 91439953824360889433828231)
  ·
    refine ⟨137159930736541334150742347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91439953824360889433828231 137159930736541334150742347)
    ·
      refine ⟨205739896104812001226113521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137159930736541334150742347 205739896104812001226113521)
      ·
        refine ⟨154304922078609000919585141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205739896104812001226113521 154304922078609000919585141)
        ·
          refine ⟨14466086444869593836211107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154304922078609000919585141 14466086444869593836211107)
          ·
            refine ⟨21699129667304390754316661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14466086444869593836211107 21699129667304390754316661)
            ·
              refine ⟨2034293406309786633217187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21699129667304390754316661 2034293406309786633217187)
              ·
                refine ⟨3051440109464679949825781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034293406309786633217187 3051440109464679949825781)
                ·
                  refine ⟨286072510262313745296167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3051440109464679949825781 286072510262313745296167)
                  ·
                    rfl

theorem cell22_2507059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 5].length) (baseStart_2507059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507059 prefixEnd_2507059 := by exact prefixLift 2507059
  have htrace : WordTrace (prefixWord ++ tailWord_2507059) baseStart_2507059 baseEnd_2507059 := by
    simpa [prefixWord, tailWord_2507059, baseEnd_2507059] using wordTrace_append hprefix tailTrace_2507059
  have hstable : (prefixWord ++ tailWord_2507059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507059).length < 2 ^ (prefixWord ++ tailWord_2507059).sum := by decide
  have hdescent : baseEnd_2507059 < baseStart_2507059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507089 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_2507089 : Nat := 118140960795 + 2507089 * 2 ^ 59
def prefixEnd_2507089 : Nat := 4983230072969 + 3 ^ 40 * 2507089 * 2
def baseEnd_2507089 : Nat := 858227800400031157638409

theorem tailTrace_2507089 : CollatzResearch.WordTrace tailWord_2507089 prefixEnd_2507089 858227800400031157638409 := by
  unfold tailWord_2507089
  simp only [CollatzResearch.WordTrace]
  refine ⟨91441048014252204557420321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60960698676168136371613547 91441048014252204557420321)
  ·
    refine ⟨68580786010689153418065241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91441048014252204557420321 68580786010689153418065241)
    ·
      refine ⟨51435589508016865063548931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68580786010689153418065241 51435589508016865063548931)
      ·
        refine ⟨77153384262025297595323397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51435589508016865063548931 77153384262025297595323397)
        ·
          refine ⟨14466259549129743299123137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77153384262025297595323397 14466259549129743299123137)
          ·
            refine ⟨10849694661847307474342353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14466259549129743299123137 10849694661847307474342353)
            ·
              refine ⟨8137270996385480605756765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10849694661847307474342353 8137270996385480605756765)
              ·
                refine ⟨3051476623644555227158787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8137270996385480605756765 3051476623644555227158787)
                ·
                  refine ⟨4577214935466832840738181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051476623644555227158787 4577214935466832840738181)
                  ·
                    refine ⟨858227800400031157638409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4577214935466832840738181 858227800400031157638409)
                    ·
                      rfl

theorem cell22_2507089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_2507089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507089 prefixEnd_2507089 := by exact prefixLift 2507089
  have htrace : WordTrace (prefixWord ++ tailWord_2507089) baseStart_2507089 baseEnd_2507089 := by
    simpa [prefixWord, tailWord_2507089, baseEnd_2507089] using wordTrace_append hprefix tailTrace_2507089
  have hstable : (prefixWord ++ tailWord_2507089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507089).length < 2 ^ (prefixWord ++ tailWord_2507089).sum := by decide
  have hdescent : baseEnd_2507089 < baseStart_2507089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507166 : List Nat := [4, 3, 1, 2, 1, 1, 3, 7]
def baseStart_2507166 : Nat := 118140960795 + 2507166 * 2 ^ 59
def prefixEnd_2507166 : Nat := 4983230072969 + 3 ^ 40 * 2507166 * 2
def baseEnd_2507166 : Nat := 95361573230403180384797

theorem tailTrace_2507166 : CollatzResearch.WordTrace tailWord_2507166 prefixEnd_2507166 95361573230403180384797 := by
  unfold tailWord_2507166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11430482054371655838496669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60962570956648831138648901 11430482054371655838496669)
  ·
    refine ⟨4286430770389370939436251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11430482054371655838496669 4286430770389370939436251)
    ·
      refine ⟨6429646155584056409154377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286430770389370939436251 6429646155584056409154377)
      ·
        refine ⟨4822234616688042306865783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6429646155584056409154377 4822234616688042306865783)
        ·
          refine ⟨7233351925032063460298675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4822234616688042306865783 7233351925032063460298675)
          ·
            refine ⟨10850027887548095190448013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7233351925032063460298675 10850027887548095190448013)
            ·
              refine ⟨4068760457830535696418005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10850027887548095190448013 4068760457830535696418005)
              ·
                refine ⟨95361573230403180384797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4068760457830535696418005 95361573230403180384797)
                ·
                  rfl

theorem cell22_2507166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_2507166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507166 prefixEnd_2507166 := by exact prefixLift 2507166
  have htrace : WordTrace (prefixWord ++ tailWord_2507166) baseStart_2507166 baseEnd_2507166 := by
    simpa [prefixWord, tailWord_2507166, baseEnd_2507166] using wordTrace_append hprefix tailTrace_2507166
  have hstable : (prefixWord ++ tailWord_2507166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507166).length < 2 ^ (prefixWord ++ tailWord_2507166).sum := by decide
  have hdescent : baseEnd_2507166 < baseStart_2507166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507192 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2507192 : Nat := 118140960795 + 2507192 * 2 ^ 59
def prefixEnd_2507192 : Nat := 4983230072969 + 3 ^ 40 * 2507192 * 2
def baseEnd_2507192 : Nat := 858263059404973222313093

theorem tailTrace_2507192 : CollatzResearch.WordTrace tailWord_2507192 prefixEnd_2507192 858263059404973222313093 := by
  unfold tailWord_2507192
  simp only [CollatzResearch.WordTrace]
  refine ⟨45722402366439526574209915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60963203155252702098946553 45722402366439526574209915)
  ·
    refine ⟨68583603549659289861314873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45722402366439526574209915 68583603549659289861314873)
    ·
      refine ⟨51437702662244467395986155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68583603549659289861314873 51437702662244467395986155)
      ·
        refine ⟨77156553993366701093979233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51437702662244467395986155 77156553993366701093979233)
        ·
          refine ⟨57867415495025025820484425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77156553993366701093979233 57867415495025025820484425)
          ·
            refine ⟨43400561621268769365363319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57867415495025025820484425 43400561621268769365363319)
            ·
              refine ⟨65100842431903154048044979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43400561621268769365363319 65100842431903154048044979)
              ·
                refine ⟨97651263647854731072067469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65100842431903154048044979 97651263647854731072067469)
                ·
                  refine ⟨36619223867945524152025301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97651263647854731072067469 36619223867945524152025301)
                  ·
                    refine ⟨858263059404973222313093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36619223867945524152025301 858263059404973222313093)
                    ·
                      rfl

theorem cell22_2507192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2507192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507192 prefixEnd_2507192 := by exact prefixLift 2507192
  have htrace : WordTrace (prefixWord ++ tailWord_2507192) baseStart_2507192 baseEnd_2507192 := by
    simpa [prefixWord, tailWord_2507192, baseEnd_2507192] using wordTrace_append hprefix tailTrace_2507192
  have hstable : (prefixWord ++ tailWord_2507192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507192).length < 2 ^ (prefixWord ++ tailWord_2507192).sum := by decide
  have hdescent : baseEnd_2507192 < baseStart_2507192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507198 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2507198 : Nat := 118140960795 + 2507198 * 2 ^ 59
def prefixEnd_2507198 : Nat := 4983230072969 + 3 ^ 40 * 2507198 * 2
def baseEnd_2507198 : Nat := 858265113327591206663075

theorem tailTrace_2507198 : CollatzResearch.WordTrace tailWord_2507198 prefixEnd_2507198 858265113327591206663075 := by
  unfold tailWord_2507198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11430627946357164521642281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60963349047238210782092165 11430627946357164521642281)
  ·
    refine ⟨8572970959767873391231711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11430627946357164521642281 8572970959767873391231711)
    ·
      refine ⟨12859456439651810086847567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8572970959767873391231711 12859456439651810086847567)
      ·
        refine ⟨19289184659477715130271351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12859456439651810086847567 19289184659477715130271351)
        ·
          refine ⟨28933776989216572695407027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19289184659477715130271351 28933776989216572695407027)
          ·
            refine ⟨43400665483824859043110541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28933776989216572695407027 43400665483824859043110541)
            ·
              refine ⟨16275249556434322141166453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43400665483824859043110541 16275249556434322141166453)
              ·
                refine ⟨1525804645915717700734355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16275249556434322141166453 1525804645915717700734355)
                ·
                  refine ⟨2288706968873576551101533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525804645915717700734355 2288706968873576551101533)
                  ·
                    refine ⟨858265113327591206663075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288706968873576551101533 858265113327591206663075)
                    ·
                      rfl

theorem cell22_2507198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2507198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507198 prefixEnd_2507198 := by exact prefixLift 2507198
  have htrace : WordTrace (prefixWord ++ tailWord_2507198) baseStart_2507198 baseEnd_2507198 := by
    simpa [prefixWord, tailWord_2507198, baseEnd_2507198] using wordTrace_append hprefix tailTrace_2507198
  have hstable : (prefixWord ++ tailWord_2507198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507198).length < 2 ^ (prefixWord ++ tailWord_2507198).sum := by decide
  have hdescent : baseEnd_2507198 < baseStart_2507198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507239 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 6]
def baseStart_2507239 : Nat := 118140960795 + 2507239 * 2 ^ 59
def prefixEnd_2507239 : Nat := 4983230072969 + 3 ^ 40 * 2507239 * 2
def baseEnd_2507239 : Nat := 286093049488493588795983

theorem tailTrace_2507239 : CollatzResearch.WordTrace tailWord_2507239 prefixEnd_2507239 286093049488493588795983 := by
  unfold tailWord_2507239
  simp only [CollatzResearch.WordTrace]
  refine ⟨91446518963708780175380771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60964345975805853450253847 91446518963708780175380771)
  ·
    refine ⟨137169778445563170263071157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91446518963708780175380771 137169778445563170263071157)
    ·
      refine ⟨12859666729271547212162921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137169778445563170263071157 12859666729271547212162921)
      ·
        refine ⟨9644750046953660409122191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12859666729271547212162921 9644750046953660409122191)
        ·
          refine ⟨14467125070430490613683287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644750046953660409122191 14467125070430490613683287)
          ·
            refine ⟨21700687605645735920524931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14467125070430490613683287 21700687605645735920524931)
            ·
              refine ⟨32551031408468603880787397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21700687605645735920524931 32551031408468603880787397)
              ·
                refine ⟨6103318389087863227647637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32551031408468603880787397 6103318389087863227647637)
                ·
                  refine ⟨286093049488493588795983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6103318389087863227647637 286093049488493588795983)
                  ·
                    rfl

theorem cell22_2507239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 6].length) (baseStart_2507239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507239 prefixEnd_2507239 := by exact prefixLift 2507239
  have htrace : WordTrace (prefixWord ++ tailWord_2507239) baseStart_2507239 baseEnd_2507239 := by
    simpa [prefixWord, tailWord_2507239, baseEnd_2507239] using wordTrace_append hprefix tailTrace_2507239
  have hstable : (prefixWord ++ tailWord_2507239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507239).length < 2 ^ (prefixWord ++ tailWord_2507239).sum := by decide
  have hdescent : baseEnd_2507239 < baseStart_2507239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507269 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_2507269 : Nat := 118140960795 + 2507269 * 2 ^ 59
def prefixEnd_2507269 : Nat := 4983230072969 + 3 ^ 40 * 2507269 * 2
def baseEnd_2507269 : Nat := 858289418078570688137857

theorem tailTrace_2507269 : CollatzResearch.WordTrace tailWord_2507269 prefixEnd_2507269 858289418078570688137857 := by
  unfold tailWord_2507269
  simp only [CollatzResearch.WordTrace]
  refine ⟨91447613153600095298972861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60965075435733396865981907 91447613153600095298972861)
  ·
    refine ⟨34292854932600035737114823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91447613153600095298972861 34292854932600035737114823)
    ·
      refine ⟨51439282398900053605672235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34292854932600035737114823 51439282398900053605672235)
      ·
        refine ⟨77158923598350080408508353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51439282398900053605672235 77158923598350080408508353)
        ·
          refine ⟨57869192698762560306381265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77158923598350080408508353 57869192698762560306381265)
          ·
            refine ⟨43401894524071920229785949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57869192698762560306381265 43401894524071920229785949)
            ·
              refine ⟨16275710446526970086169731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43401894524071920229785949 16275710446526970086169731)
              ·
                refine ⟨24413565669790455129254597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16275710446526970086169731 24413565669790455129254597)
                ·
                  refine ⟨4577543563085710336735237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24413565669790455129254597 4577543563085710336735237)
                  ·
                    refine ⟨858289418078570688137857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4577543563085710336735237 858289418078570688137857)
                    ·
                      rfl

theorem cell22_2507269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_2507269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507269 prefixEnd_2507269 := by exact prefixLift 2507269
  have htrace : WordTrace (prefixWord ++ tailWord_2507269) baseStart_2507269 baseEnd_2507269 := by
    simpa [prefixWord, tailWord_2507269, baseEnd_2507269] using wordTrace_append hprefix tailTrace_2507269
  have hstable : (prefixWord ++ tailWord_2507269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507269).length < 2 ^ (prefixWord ++ tailWord_2507269).sum := by decide
  have hdescent : baseEnd_2507269 < baseStart_2507269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507288 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_2507288 : Nat := 118140960795 + 2507288 * 2 ^ 59
def prefixEnd_2507288 : Nat := 4983230072969 + 3 ^ 40 * 2507288 * 2
def baseEnd_2507288 : Nat := 858295922166860971912799

theorem tailTrace_2507288 : CollatzResearch.WordTrace tailWord_2507288 prefixEnd_2507288 858295922166860971912799 := by
  unfold tailWord_2507288
  simp only [CollatzResearch.WordTrace]
  refine ⟨45724153070265630771957259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60965537427020841029276345 45724153070265630771957259)
  ·
    refine ⟨68586229605398446157935889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45724153070265630771957259 68586229605398446157935889)
    ·
      refine ⟨51439672204048834618451917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68586229605398446157935889 51439672204048834618451917)
      ·
        refine ⟨19289877076518312981919469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51439672204048834618451917 19289877076518312981919469)
        ·
          refine ⟨7233703903694367368219801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19289877076518312981919469 7233703903694367368219801)
          ·
            refine ⟨5425277927770775526164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7233703903694367368219801 5425277927770775526164851)
            ·
              refine ⟨8137916891656163289247277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425277927770775526164851 8137916891656163289247277)
              ·
                refine ⟨3051718834371061233467729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8137916891656163289247277 3051718834371061233467729)
                ·
                  refine ⟨2288789125778295925100797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051718834371061233467729 2288789125778295925100797)
                  ·
                    refine ⟨858295922166860971912799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288789125778295925100797 858295922166860971912799)
                    ·
                      rfl

theorem cell22_2507288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_2507288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507288 prefixEnd_2507288 := by exact prefixLift 2507288
  have htrace : WordTrace (prefixWord ++ tailWord_2507288) baseStart_2507288 baseEnd_2507288 := by
    simpa [prefixWord, tailWord_2507288, baseEnd_2507288] using wordTrace_append hprefix tailTrace_2507288
  have hstable : (prefixWord ++ tailWord_2507288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507288).length < 2 ^ (prefixWord ++ tailWord_2507288).sum := by decide
  have hdescent : baseEnd_2507288 < baseStart_2507288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507309 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2507309 : Nat := 118140960795 + 2507309 * 2 ^ 59
def prefixEnd_2507309 : Nat := 4983230072969 + 3 ^ 40 * 2507309 * 2
def baseEnd_2507309 : Nat := 858303110896023917137735

theorem tailTrace_2507309 : CollatzResearch.WordTrace tailWord_2507309 prefixEnd_2507309 858303110896023917137735 := by
  unfold tailWord_2507309
  simp only [CollatzResearch.WordTrace]
  refine ⟨91449072073455182130428981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60966048048970121420285987 91449072073455182130428981)
  ·
    refine ⟨8573350506886423324727717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91449072073455182130428981 8573350506886423324727717)
    ·
      refine ⟨1607503220041204373386447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8573350506886423324727717 1607503220041204373386447)
      ·
        refine ⟨2411254830061806560079671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607503220041204373386447 2411254830061806560079671)
        ·
          refine ⟨3616882245092709840119507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411254830061806560079671 3616882245092709840119507)
          ·
            refine ⟨5425323367639064760179261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616882245092709840119507 5425323367639064760179261)
            ·
              refine ⟨2034496262864649285067223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5425323367639064760179261 2034496262864649285067223)
              ·
                refine ⟨3051744394296973927600835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034496262864649285067223 3051744394296973927600835)
                ·
                  refine ⟨4577616591445460891401253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051744394296973927600835 4577616591445460891401253)
                  ·
                    refine ⟨858303110896023917137735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4577616591445460891401253 858303110896023917137735)
                    ·
                      rfl

theorem cell22_2507309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2507309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507309 prefixEnd_2507309 := by exact prefixLift 2507309
  have htrace : WordTrace (prefixWord ++ tailWord_2507309) baseStart_2507309 baseEnd_2507309 := by
    simpa [prefixWord, tailWord_2507309, baseEnd_2507309] using wordTrace_append hprefix tailTrace_2507309
  have hstable : (prefixWord ++ tailWord_2507309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507309).length < 2 ^ (prefixWord ++ tailWord_2507309).sum := by decide
  have hdescent : baseEnd_2507309 < baseStart_2507309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507346 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_2507346 : Nat := 118140960795 + 2507346 * 2 ^ 59
def prefixEnd_2507346 : Nat := 4983230072969 + 3 ^ 40 * 2507346 * 2
def baseEnd_2507346 : Nat := 286105258917389384654207

theorem tailTrace_2507346 : CollatzResearch.WordTrace tailWord_2507346 prefixEnd_2507346 286105258917389384654207 := by
  unfold tailWord_2507346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22862605393580284362381473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60966947716214091633017261 22862605393580284362381473)
  ·
    refine ⟨17146954045185213271786105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22862605393580284362381473 17146954045185213271786105)
    ·
      refine ⟨12860215533888909953839579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17146954045185213271786105 12860215533888909953839579)
      ·
        refine ⟨19290323300833364930759369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12860215533888909953839579 19290323300833364930759369)
        ·
          refine ⟨14467742475625023698069527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19290323300833364930759369 14467742475625023698069527)
          ·
            refine ⟨21701613713437535547104291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14467742475625023698069527 21701613713437535547104291)
            ·
              refine ⟨32552420570156303320656437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21701613713437535547104291 32552420570156303320656437)
              ·
                refine ⟨3051789428452153436311541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32552420570156303320656437 3051789428452153436311541)
                ·
                  refine ⟨286105258917389384654207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3051789428452153436311541 286105258917389384654207)
                  ·
                    rfl

theorem cell22_2507346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_2507346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507346 prefixEnd_2507346 := by exact prefixLift 2507346
  have htrace : WordTrace (prefixWord ++ tailWord_2507346) baseStart_2507346 baseEnd_2507346 := by
    simpa [prefixWord, tailWord_2507346, baseEnd_2507346] using wordTrace_append hprefix tailTrace_2507346
  have hstable : (prefixWord ++ tailWord_2507346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507346).length < 2 ^ (prefixWord ++ tailWord_2507346).sum := by decide
  have hdescent : baseEnd_2507346 < baseStart_2507346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507410 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2507410 : Nat := 118140960795 + 2507410 * 2 ^ 59
def prefixEnd_2507410 : Nat := 4983230072969 + 3 ^ 40 * 2507410 * 2
def baseEnd_2507410 : Nat := 858337685260093320362425

theorem tailTrace_2507410 : CollatzResearch.WordTrace tailWord_2507410 prefixEnd_2507410 858337685260093320362425 := by
  unfold tailWord_2507410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22863188961522319094963921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60968503897392850919903789 22863188961522319094963921)
  ·
    refine ⟨17147391721141739321222941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22863188961522319094963921 17147391721141739321222941)
    ·
      refine ⟨6430271895428152245458603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17147391721141739321222941 6430271895428152245458603)
      ·
        refine ⟨9645407843142228368187905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6430271895428152245458603 9645407843142228368187905)
        ·
          refine ⟨7234055882356671276140929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9645407843142228368187905 7234055882356671276140929)
          ·
            refine ⟨5425541911767503457105697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7234055882356671276140929 5425541911767503457105697)
            ·
              refine ⟨4069156433825627592829273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5425541911767503457105697 4069156433825627592829273)
              ·
                refine ⟨3051867325369220694621955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069156433825627592829273 3051867325369220694621955)
                ·
                  refine ⟨4577800988053831041932933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051867325369220694621955 4577800988053831041932933)
                  ·
                    refine ⟨858337685260093320362425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4577800988053831041932933 858337685260093320362425)
                    ·
                      rfl

theorem cell22_2507410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2507410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507410 prefixEnd_2507410 := by exact prefixLift 2507410
  have htrace : WordTrace (prefixWord ++ tailWord_2507410) baseStart_2507410 baseEnd_2507410 := by
    simpa [prefixWord, tailWord_2507410, baseEnd_2507410] using wordTrace_append hprefix tailTrace_2507410
  have hstable : (prefixWord ++ tailWord_2507410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507410).length < 2 ^ (prefixWord ++ tailWord_2507410).sum := by decide
  have hdescent : baseEnd_2507410 < baseStart_2507410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507421 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2507421 : Nat := 118140960795 + 2507421 * 2 ^ 59
def prefixEnd_2507421 : Nat := 4983230072969 + 3 ^ 40 * 2507421 * 2
def baseEnd_2507421 : Nat := 858341450784892958337391

theorem tailTrace_2507421 : CollatzResearch.WordTrace tailWord_2507421 prefixEnd_2507421 858341450784892958337391 := by
  unfold tailWord_2507421
  simp only [CollatzResearch.WordTrace]
  refine ⟨91453157049049425258506117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60968771366032950172337411 91453157049049425258506117)
  ·
    refine ⟨17147466946696767235969897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91453157049049425258506117 17147466946696767235969897)
    ·
      refine ⟨12860600210022575426977423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17147466946696767235969897 12860600210022575426977423)
      ·
        refine ⟨19290900315033863140466135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12860600210022575426977423 19290900315033863140466135)
        ·
          refine ⟨28936350472550794710699203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19290900315033863140466135 28936350472550794710699203)
          ·
            refine ⟨43404525708826192066048805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28936350472550794710699203 43404525708826192066048805)
            ·
              refine ⟨8138348570404911012384151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43404525708826192066048805 8138348570404911012384151)
              ·
                refine ⟨12207522855607366518576227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8138348570404911012384151 12207522855607366518576227)
                ·
                  refine ⟨18311284283411049777864341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12207522855607366518576227 18311284283411049777864341)
                  ·
                    refine ⟨858341450784892958337391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18311284283411049777864341 858341450784892958337391)
                    ·
                      rfl

theorem cell22_2507421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2507421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507421 prefixEnd_2507421 := by exact prefixLift 2507421
  have htrace : WordTrace (prefixWord ++ tailWord_2507421) baseStart_2507421 baseEnd_2507421 := by
    simpa [prefixWord, tailWord_2507421, baseEnd_2507421] using wordTrace_append hprefix tailTrace_2507421
  have hstable : (prefixWord ++ tailWord_2507421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507421).length < 2 ^ (prefixWord ++ tailWord_2507421).sum := by decide
  have hdescent : baseEnd_2507421 < baseStart_2507421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507502 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_2507502 : Nat := 118140960795 + 2507502 * 2 ^ 59
def prefixEnd_2507502 : Nat := 4983230072969 + 3 ^ 40 * 2507502 * 2
def baseEnd_2507502 : Nat := 858369178740235747062143

theorem tailTrace_2507502 : CollatzResearch.WordTrace tailWord_2507502 prefixEnd_2507502 858369178740235747062143 := by
  unfold tailWord_2507502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11432013920219497011525595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60970740907837317394803173 11432013920219497011525595)
  ·
    refine ⟨17148020880329245517288393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11432013920219497011525595 17148020880329245517288393)
    ·
      refine ⟨12861015660246934137966295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17148020880329245517288393 12861015660246934137966295)
      ·
        refine ⟨19291523490370401206949443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12861015660246934137966295 19291523490370401206949443)
        ·
          refine ⟨28937285235555601810424165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19291523490370401206949443 28937285235555601810424165)
          ·
            refine ⟨5425740981666675339454531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28937285235555601810424165 5425740981666675339454531)
            ·
              refine ⟨8138611472500013009181797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425740981666675339454531 8138611472500013009181797)
              ·
                refine ⟨1525989651093752439221587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8138611472500013009181797 1525989651093752439221587)
                ·
                  refine ⟨2288984476640628658832381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525989651093752439221587 2288984476640628658832381)
                  ·
                    refine ⟨858369178740235747062143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288984476640628658832381 858369178740235747062143)
                    ·
                      rfl

theorem cell22_2507502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_2507502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507502 prefixEnd_2507502 := by exact prefixLift 2507502
  have htrace : WordTrace (prefixWord ++ tailWord_2507502) baseStart_2507502 baseEnd_2507502 := by
    simpa [prefixWord, tailWord_2507502, baseEnd_2507502] using wordTrace_append hprefix tailTrace_2507502
  have hstable : (prefixWord ++ tailWord_2507502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507502).length < 2 ^ (prefixWord ++ tailWord_2507502).sum := by decide
  have hdescent : baseEnd_2507502 < baseStart_2507502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507528 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_2507528 : Nat := 118140960795 + 2507528 * 2 ^ 59
def prefixEnd_2507528 : Nat := 4983230072969 + 3 ^ 40 * 2507528 * 2
def baseEnd_2507528 : Nat := 858378079071580345912063

theorem tailTrace_2507528 : CollatzResearch.WordTrace tailWord_2507528 prefixEnd_2507528 858378079071580345912063 := by
  unfold tailWord_2507528
  simp only [CollatzResearch.WordTrace]
  refine ⟨45728529829830891266325619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60971373106441188355100825 45728529829830891266325619)
  ·
    refine ⟨68592794744746336899488429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45728529829830891266325619 68592794744746336899488429)
    ·
      refine ⟨25722298029279876337308161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68592794744746336899488429 25722298029279876337308161)
      ·
        refine ⟨19291723521959907252981121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25722298029279876337308161 19291723521959907252981121)
        ·
          refine ⟨14468792641469930439735841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19291723521959907252981121 14468792641469930439735841)
          ·
            refine ⟨10851594481102447829801881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14468792641469930439735841 10851594481102447829801881)
            ·
              refine ⟨8138695860826835872351411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10851594481102447829801881 8138695860826835872351411)
              ·
                refine ⟨12208043791240253808527117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8138695860826835872351411 12208043791240253808527117)
                ·
                  refine ⟨4578016421715095178197669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12208043791240253808527117 4578016421715095178197669)
                  ·
                    refine ⟨858378079071580345912063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4578016421715095178197669 858378079071580345912063)
                    ·
                      rfl

theorem cell22_2507528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_2507528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507528 prefixEnd_2507528 := by exact prefixLift 2507528
  have htrace : WordTrace (prefixWord ++ tailWord_2507528) baseStart_2507528 baseEnd_2507528 := by
    simpa [prefixWord, tailWord_2507528, baseEnd_2507528] using wordTrace_append hprefix tailTrace_2507528
  have hstable : (prefixWord ++ tailWord_2507528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507528).length < 2 ^ (prefixWord ++ tailWord_2507528).sum := by decide
  have hdescent : baseEnd_2507528 < baseStart_2507528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507549 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 5]
def baseStart_2507549 : Nat := 118140960795 + 2507549 * 2 ^ 59
def prefixEnd_2507549 : Nat := 4983230072969 + 3 ^ 40 * 2507549 * 2
def baseEnd_2507549 : Nat := 286128422600247763712333

theorem tailTrace_2507549 : CollatzResearch.WordTrace tailWord_2507549 prefixEnd_2507549 286128422600247763712333 := by
  unfold tailWord_2507549
  simp only [CollatzResearch.WordTrace]
  refine ⟨91457825592585703119165701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60971883728390468746110467 91457825592585703119165701)
  ·
    refine ⟨17148342298609819334843569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91457825592585703119165701 17148342298609819334843569)
    ·
      refine ⟨12861256723957364501132677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17148342298609819334843569 12861256723957364501132677)
      ·
        refine ⟨2411485635742005843962377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12861256723957364501132677 2411485635742005843962377)
        ·
          refine ⟨1808614226806504382971783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2411485635742005843962377 1808614226806504382971783)
          ·
            refine ⟨2712921340209756574457675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808614226806504382971783 2712921340209756574457675)
            ·
              refine ⟨4069382010314634861686513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712921340209756574457675 4069382010314634861686513)
              ·
                refine ⟨3052036507735976146264885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069382010314634861686513 3052036507735976146264885)
                ·
                  refine ⟨286128422600247763712333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3052036507735976146264885 286128422600247763712333)
                  ·
                    rfl

theorem cell22_2507549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_2507549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507549 prefixEnd_2507549 := by exact prefixLift 2507549
  have htrace : WordTrace (prefixWord ++ tailWord_2507549) baseStart_2507549 baseEnd_2507549 := by
    simpa [prefixWord, tailWord_2507549, baseEnd_2507549] using wordTrace_append hprefix tailTrace_2507549
  have hstable : (prefixWord ++ tailWord_2507549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507549).length < 2 ^ (prefixWord ++ tailWord_2507549).sum := by decide
  have hdescent : baseEnd_2507549 < baseStart_2507549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507560 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 4]
def baseStart_2507560 : Nat := 118140960795 + 2507560 * 2 ^ 59
def prefixEnd_2507560 : Nat := 4983230072969 + 3 ^ 40 * 2507560 * 2
def baseEnd_2507560 : Nat := 286129677775180976370655

theorem tailTrace_2507560 : CollatzResearch.WordTrace tailWord_2507560 prefixEnd_2507560 286129677775180976370655 := by
  unfold tailWord_2507560
  simp only [CollatzResearch.WordTrace]
  refine ⟨45729113397772925998908067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60972151197030567998544089 45729113397772925998908067)
  ·
    refine ⟨68593670096659388998362101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45729113397772925998908067 68593670096659388998362101)
    ·
      refine ⟨6430656571561817718596447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68593670096659388998362101 6430656571561817718596447)
      ·
        refine ⟨9645984857342726577894671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6430656571561817718596447 9645984857342726577894671)
        ·
          refine ⟨14468977286014089866842007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9645984857342726577894671 14468977286014089866842007)
          ·
            refine ⟨21703465929021134800263011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14468977286014089866842007 21703465929021134800263011)
            ·
              refine ⟨32555198893531702200394517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21703465929021134800263011 32555198893531702200394517)
              ·
                refine ⟨1526024948134298540643493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32555198893531702200394517 1526024948134298540643493)
                ·
                  refine ⟨286129677775180976370655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526024948134298540643493 286129677775180976370655)
                  ·
                    rfl

theorem cell22_2507560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_2507560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507560 prefixEnd_2507560 := by exact prefixLift 2507560
  have htrace : WordTrace (prefixWord ++ tailWord_2507560) baseStart_2507560 baseEnd_2507560 := by
    simpa [prefixWord, tailWord_2507560, baseEnd_2507560] using wordTrace_append hprefix tailTrace_2507560
  have hstable : (prefixWord ++ tailWord_2507560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507560).length < 2 ^ (prefixWord ++ tailWord_2507560).sum := by decide
  have hdescent : baseEnd_2507560 < baseStart_2507560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507573 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2507573 : Nat := 118140960795 + 2507573 * 2 ^ 59
def prefixEnd_2507573 : Nat := 4983230072969 + 3 ^ 40 * 2507573 * 2
def baseEnd_2507573 : Nat := 858393483491215228536925

theorem tailTrace_2507573 : CollatzResearch.WordTrace tailWord_2507573 prefixEnd_2507573 858393483491215228536925 := by
  unfold tailWord_2507573
  simp only [CollatzResearch.WordTrace]
  refine ⟨91458700944498755218039373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60972467296332503478692915 91458700944498755218039373)
  ·
    refine ⟨34297012854187033206764765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91458700944498755218039373 34297012854187033206764765)
    ·
      refine ⟨12861379820320137452536787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34297012854187033206764765 12861379820320137452536787)
      ·
        refine ⟨19292069730480206178805181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12861379820320137452536787 19292069730480206178805181)
        ·
          refine ⟨7234526148930077317051943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19292069730480206178805181 7234526148930077317051943)
          ·
            refine ⟨10851789223395115975577915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7234526148930077317051943 10851789223395115975577915)
            ·
              refine ⟨16277683835092673963366873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10851789223395115975577915 16277683835092673963366873)
              ·
                refine ⟨12208262876319505472525155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16277683835092673963366873 12208262876319505472525155)
                ·
                  refine ⟨18312394314479258208787733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12208262876319505472525155 18312394314479258208787733)
                  ·
                    refine ⟨858393483491215228536925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18312394314479258208787733 858393483491215228536925)
                    ·
                      rfl

theorem cell22_2507573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2507573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507573 prefixEnd_2507573 := by exact prefixLift 2507573
  have htrace : WordTrace (prefixWord ++ tailWord_2507573) baseStart_2507573 baseEnd_2507573 := by
    simpa [prefixWord, tailWord_2507573, baseEnd_2507573] using wordTrace_append hprefix tailTrace_2507573
  have hstable : (prefixWord ++ tailWord_2507573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507573).length < 2 ^ (prefixWord ++ tailWord_2507573).sum := by decide
  have hdescent : baseEnd_2507573 < baseStart_2507573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507603 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 5, 3]
def baseStart_2507603 : Nat := 118140960795 + 2507603 * 2 ^ 59
def prefixEnd_2507603 : Nat := 4983230072969 + 3 ^ 40 * 2507603 * 2
def baseEnd_2507603 : Nat := 858403753104305150286833

theorem tailTrace_2507603 : CollatzResearch.WordTrace tailWord_2507603 prefixEnd_2507603 858403753104305150286833 := by
  unfold tailWord_2507603
  simp only [CollatzResearch.WordTrace]
  refine ⟨91459795134390070341631463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60973196756260046894420975 91459795134390070341631463)
  ·
    refine ⟨137189692701585105512447195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91459795134390070341631463 137189692701585105512447195)
    ·
      refine ⟨205784539052377658268670793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137189692701585105512447195 205784539052377658268670793)
      ·
        refine ⟨154338404289283243701503095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205784539052377658268670793 154338404289283243701503095)
        ·
          refine ⟨231507606433924865552254643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154338404289283243701503095 231507606433924865552254643)
          ·
            refine ⟨347261409650887298328381965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231507606433924865552254643 347261409650887298328381965)
            ·
              refine ⟨130223028619082736873143237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347261409650887298328381965 130223028619082736873143237)
              ·
                refine ⟨24416817866078013163714357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130223028619082736873143237 24416817866078013163714357)
                ·
                  refine ⟨2289076674944813734098221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24416817866078013163714357 2289076674944813734098221)
                  ·
                    refine ⟨858403753104305150286833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289076674944813734098221 858403753104305150286833)
                    ·
                      rfl

theorem cell22_2507603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 3].length) (baseStart_2507603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507603 prefixEnd_2507603 := by exact prefixLift 2507603
  have htrace : WordTrace (prefixWord ++ tailWord_2507603) baseStart_2507603 baseEnd_2507603 := by
    simpa [prefixWord, tailWord_2507603, baseEnd_2507603] using wordTrace_append hprefix tailTrace_2507603
  have hstable : (prefixWord ++ tailWord_2507603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507603).length < 2 ^ (prefixWord ++ tailWord_2507603).sum := by decide
  have hdescent : baseEnd_2507603 < baseStart_2507603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507710 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2507710 : Nat := 118140960795 + 2507710 * 2 ^ 59
def prefixEnd_2507710 : Nat := 4983230072969 + 3 ^ 40 * 2507710 * 2
def baseEnd_2507710 : Nat := 858440381390992537861505

theorem tailTrace_2507710 : CollatzResearch.WordTrace tailWord_2507710 prefixEnd_2507710 858440381390992537861505 := by
  unfold tailWord_2507710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11432962218125303451972073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60975798496668285077184389 11432962218125303451972073)
  ·
    refine ⟨8574721663593977588979055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11432962218125303451972073 8574721663593977588979055)
    ·
      refine ⟨12862082495390966383468583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8574721663593977588979055 12862082495390966383468583)
      ·
        refine ⟨19293123743086449575202875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12862082495390966383468583 19293123743086449575202875)
        ·
          refine ⟨28939685614629674362804313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19293123743086449575202875 28939685614629674362804313)
          ·
            refine ⟨21704764210972255772103235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28939685614629674362804313 21704764210972255772103235)
            ·
              refine ⟨32557146316458383658154853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21704764210972255772103235 32557146316458383658154853)
              ·
                refine ⟨6104464934335946935904035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32557146316458383658154853 6104464934335946935904035)
                ·
                  refine ⟨9156697401503920403856053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6104464934335946935904035 9156697401503920403856053)
                  ·
                    refine ⟨858440381390992537861505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9156697401503920403856053 858440381390992537861505)
                    ·
                      rfl

theorem cell22_2507710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2507710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507710 prefixEnd_2507710 := by exact prefixLift 2507710
  have htrace : WordTrace (prefixWord ++ tailWord_2507710) baseStart_2507710 baseEnd_2507710 := by
    simpa [prefixWord, tailWord_2507710, baseEnd_2507710] using wordTrace_append hprefix tailTrace_2507710
  have hstable : (prefixWord ++ tailWord_2507710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507710).length < 2 ^ (prefixWord ++ tailWord_2507710).sum := by decide
  have hdescent : baseEnd_2507710 < baseStart_2507710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507712 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 4]
def baseStart_2507712 : Nat := 118140960795 + 2507712 * 2 ^ 59
def prefixEnd_2507712 : Nat := 4983230072969 + 3 ^ 40 * 2507712 * 2
def baseEnd_2507712 : Nat := 286147022010621733103833

theorem tailTrace_2507712 : CollatzResearch.WordTrace tailWord_2507712 prefixEnd_2507712 286147022010621733103833 := by
  unfold tailWord_2507712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45731885345497590978674695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60975847127330121304899593 45731885345497590978674695)
  ·
    refine ⟨68597828018246386468012043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45731885345497590978674695 68597828018246386468012043)
    ·
      refine ⟨102896742027369579702018065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68597828018246386468012043 102896742027369579702018065)
      ·
        refine ⟨77172556520527184776513549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102896742027369579702018065 77172556520527184776513549)
        ·
          refine ⟨28939708695197694291192581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77172556520527184776513549 28939708695197694291192581)
          ·
            refine ⟨5426195380349567679598609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28939708695197694291192581 5426195380349567679598609)
            ·
              refine ⟨4069646535262175759698957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426195380349567679598609 4069646535262175759698957)
              ·
                refine ⟨1526117450723315909887109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4069646535262175759698957 1526117450723315909887109)
                ·
                  refine ⟨286147022010621733103833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526117450723315909887109 286147022010621733103833)
                  ·
                    rfl

theorem cell22_2507712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_2507712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507712 prefixEnd_2507712 := by exact prefixLift 2507712
  have htrace : WordTrace (prefixWord ++ tailWord_2507712) baseStart_2507712 baseEnd_2507712 := by
    simpa [prefixWord, tailWord_2507712, baseEnd_2507712] using wordTrace_append hprefix tailTrace_2507712
  have hstable : (prefixWord ++ tailWord_2507712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507712).length < 2 ^ (prefixWord ++ tailWord_2507712).sum := by decide
  have hdescent : baseEnd_2507712 < baseStart_2507712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507723 : List Nat := [1, 1, 1, 1, 3, 6, 9]
def baseStart_2507723 : Nat := 118140960795 + 2507723 * 2 ^ 59
def prefixEnd_2507723 : Nat := 4983230072969 + 3 ^ 40 * 2507723 * 2
def baseEnd_2507723 : Nat := 31794253020617216195795

theorem tailTrace_2507723 : CollatzResearch.WordTrace tailWord_2507723 prefixEnd_2507723 31794253020617216195795 := by
  unfold tailWord_2507723
  simp only [CollatzResearch.WordTrace]
  refine ⟨91464171893955330835999823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60976114595970220557333215 91464171893955330835999823)
  ·
    refine ⟨137196257840932996253999735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91464171893955330835999823 137196257840932996253999735)
    ·
      refine ⟨205794386761399494380999603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137196257840932996253999735 205794386761399494380999603)
      ·
        refine ⟨308691580142099241571499405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205794386761399494380999603 308691580142099241571499405)
        ·
          refine ⟨115759342553287215589312277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308691580142099241571499405 115759342553287215589312277)
          ·
            refine ⟨5426219182185338230749013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115759342553287215589312277 5426219182185338230749013)
            ·
              refine ⟨31794253020617216195795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5426219182185338230749013 31794253020617216195795)
              ·
                rfl

theorem cell22_2507723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 9].length) (baseStart_2507723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507723 prefixEnd_2507723 := by exact prefixLift 2507723
  have htrace : WordTrace (prefixWord ++ tailWord_2507723) baseStart_2507723 baseEnd_2507723 := by
    simpa [prefixWord, tailWord_2507723, baseEnd_2507723] using wordTrace_append hprefix tailTrace_2507723
  have hstable : (prefixWord ++ tailWord_2507723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507723).length < 2 ^ (prefixWord ++ tailWord_2507723).sum := by decide
  have hdescent : baseEnd_2507723 < baseStart_2507723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507727 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 2, 3]
def baseStart_2507727 : Nat := 118140960795 + 2507727 * 2 ^ 59
def prefixEnd_2507727 : Nat := 4983230072969 + 3 ^ 40 * 2507727 * 2
def baseEnd_2507727 : Nat := 858446200838410160186453

theorem tailTrace_2507727 : CollatzResearch.WordTrace tailWord_2507727 prefixEnd_2507727 858446200838410160186453 := by
  unfold tailWord_2507727
  simp only [CollatzResearch.WordTrace]
  refine ⟨91464317785940839519145435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60976211857293893012763623 91464317785940839519145435)
  ·
    refine ⟨137196476678911259278718153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91464317785940839519145435 137196476678911259278718153)
    ·
      refine ⟨102897357509183444459038615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137196476678911259278718153 102897357509183444459038615)
      ·
        refine ⟨154346036263775166688557923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102897357509183444459038615 154346036263775166688557923)
        ·
          refine ⟨231519054395662750032836885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154346036263775166688557923 231519054395662750032836885)
          ·
            refine ⟨10852455674796691407789229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 231519054395662750032836885 10852455674796691407789229)
            ·
              refine ⟨4069670878048759277920961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10852455674796691407789229 4069670878048759277920961)
              ·
                refine ⟨3052253158536569458440721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069670878048759277920961 3052253158536569458440721)
                ·
                  refine ⟨2289189868902427093830541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052253158536569458440721 2289189868902427093830541)
                  ·
                    refine ⟨858446200838410160186453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289189868902427093830541 858446200838410160186453)
                    ·
                      rfl

theorem cell22_2507727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_2507727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507727 prefixEnd_2507727 := by exact prefixLift 2507727
  have htrace : WordTrace (prefixWord ++ tailWord_2507727) baseStart_2507727 baseEnd_2507727 := by
    simpa [prefixWord, tailWord_2507727, baseEnd_2507727] using wordTrace_append hprefix tailTrace_2507727
  have hstable : (prefixWord ++ tailWord_2507727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507727).length < 2 ^ (prefixWord ++ tailWord_2507727).sum := by decide
  have hdescent : baseEnd_2507727 < baseStart_2507727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507774 : List Nat := [4, 2, 2, 2, 3, 1, 8]
def baseStart_2507774 : Nat := 118140960795 + 2507774 * 2 ^ 59
def prefixEnd_2507774 : Nat := 4983230072969 + 3 ^ 40 * 2507774 * 2
def baseEnd_2507774 : Nat := 31794899625885840898567

theorem tailTrace_2507774 : CollatzResearch.WordTrace tailWord_2507774 prefixEnd_2507774 31794899625885840898567 := by
  unfold tailWord_2507774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11433254002096320818263297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60977354677847044364070917 11433254002096320818263297)
  ·
    refine ⟨8574940501572240613697473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11433254002096320818263297 8574940501572240613697473)
    ·
      refine ⟨6431205376179180460273105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8574940501572240613697473 6431205376179180460273105)
      ·
        refine ⟨4823404032134385345204829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6431205376179180460273105 4823404032134385345204829)
        ·
          refine ⟨1808776512050394504451811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4823404032134385345204829 1808776512050394504451811)
          ·
            refine ⟨2713164768075591756677717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808776512050394504451811 2713164768075591756677717)
            ·
              refine ⟨31794899625885840898567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2713164768075591756677717 31794899625885840898567)
              ·
                rfl

theorem cell22_2507774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 8].length) (baseStart_2507774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507774 prefixEnd_2507774 := by exact prefixLift 2507774
  have htrace : WordTrace (prefixWord ++ tailWord_2507774) baseStart_2507774 baseEnd_2507774 := by
    simpa [prefixWord, tailWord_2507774, baseEnd_2507774] using wordTrace_append hprefix tailTrace_2507774
  have hstable : (prefixWord ++ tailWord_2507774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507774).length < 2 ^ (prefixWord ++ tailWord_2507774).sum := by decide
  have hdescent : baseEnd_2507774 < baseStart_2507774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507941 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_2507941 : Nat := 118140960795 + 2507941 * 2 ^ 59
def prefixEnd_2507941 : Nat := 4983230072969 + 3 ^ 40 * 2507941 * 2
def baseEnd_2507941 : Nat := 858519457411784935335797

theorem tailTrace_2507941 : CollatzResearch.WordTrace tailWord_2507941 prefixEnd_2507941 858519457411784935335797 := by
  unfold tailWord_2507941
  simp only [CollatzResearch.WordTrace]
  refine ⟨91472123007165554067435677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60981415338110369378290451 91472123007165554067435677)
  ·
    refine ⟨34302046127687082775288379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91472123007165554067435677 34302046127687082775288379)
    ·
      refine ⟨51453069191530624162932569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34302046127687082775288379 51453069191530624162932569)
      ·
        refine ⟨38589801893647968122199427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51453069191530624162932569 38589801893647968122199427)
        ·
          refine ⟨57884702840471952183299141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38589801893647968122199427 57884702840471952183299141)
          ·
            refine ⟨10853381782588491034368589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57884702840471952183299141 10853381782588491034368589)
            ·
              refine ⟨4070018168470684137888221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10853381782588491034368589 4070018168470684137888221)
              ·
                refine ⟨1526256813176506551708083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4070018168470684137888221 1526256813176506551708083)
                ·
                  refine ⟨2289385219764759827562125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526256813176506551708083 2289385219764759827562125)
                  ·
                    refine ⟨858519457411784935335797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289385219764759827562125 858519457411784935335797)
                    ·
                      rfl

theorem cell22_2507941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_2507941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2507941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2507941 prefixEnd_2507941 := by exact prefixLift 2507941
  have htrace : WordTrace (prefixWord ++ tailWord_2507941) baseStart_2507941 baseEnd_2507941 := by
    simpa [prefixWord, tailWord_2507941, baseEnd_2507941] using wordTrace_append hprefix tailTrace_2507941
  have hstable : (prefixWord ++ tailWord_2507941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507941).length < 2 ^ (prefixWord ++ tailWord_2507941).sum := by decide
  have hdescent : baseEnd_2507941 < baseStart_2507941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508001 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 1, 4]
def baseStart_2508001 : Nat := 118140960795 + 2508001 * 2 ^ 59
def prefixEnd_2508001 : Nat := 4983230072969 + 3 ^ 40 * 2508001 * 2
def baseEnd_2508001 : Nat := 858539996637964778835613

theorem tailTrace_2508001 : CollatzResearch.WordTrace tailWord_2508001 prefixEnd_2508001 858539996637964778835613 := by
  unfold tailWord_2508001
  simp only [CollatzResearch.WordTrace]
  refine ⟨91474311386948184314619857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60982874257965456209746571 91474311386948184314619857)
  ·
    refine ⟨68605733540211138235964893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91474311386948184314619857 68605733540211138235964893)
    ·
      refine ⟨25727150077579176838486835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68605733540211138235964893 25727150077579176838486835)
      ·
        refine ⟨38590725116368765257730253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25727150077579176838486835 38590725116368765257730253)
        ·
          refine ⟨14471521918638286971648845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38590725116368765257730253 14471521918638286971648845)
          ·
            refine ⟨5426820719489357614368317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14471521918638286971648845 5426820719489357614368317)
            ·
              refine ⟨2035057769808509105388119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5426820719489357614368317 2035057769808509105388119)
              ·
                refine ⟨3052586654712763658082179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035057769808509105388119 3052586654712763658082179)
                ·
                  refine ⟨4578879982069145487123269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052586654712763658082179 4578879982069145487123269)
                  ·
                    refine ⟨858539996637964778835613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4578879982069145487123269 858539996637964778835613)
                    ·
                      rfl

theorem cell22_2508001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_2508001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508001 prefixEnd_2508001 := by exact prefixLift 2508001
  have htrace : WordTrace (prefixWord ++ tailWord_2508001) baseStart_2508001 baseEnd_2508001 := by
    simpa [prefixWord, tailWord_2508001, baseEnd_2508001] using wordTrace_append hprefix tailTrace_2508001
  have hstable : (prefixWord ++ tailWord_2508001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508001).length < 2 ^ (prefixWord ++ tailWord_2508001).sum := by decide
  have hdescent : baseEnd_2508001 < baseStart_2508001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508014 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2508014 : Nat := 118140960795 + 2508014 * 2 ^ 59
def prefixEnd_2508014 : Nat := 4983230072969 + 3 ^ 40 * 2508014 * 2
def baseEnd_2508014 : Nat := 858544446803637078260573

theorem tailTrace_2508014 : CollatzResearch.WordTrace tailWord_2508014 prefixEnd_2508014 858544446803637078260573 := by
  unfold tailWord_2508014
  simp only [CollatzResearch.WordTrace]
  refine ⟨11434348191987635941855387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60983190357267391689895397 11434348191987635941855387)
  ·
    refine ⟨17151522287981453912783081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11434348191987635941855387 17151522287981453912783081)
    ·
      refine ⟨12863641715986090434587311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17151522287981453912783081 12863641715986090434587311)
      ·
        refine ⟨19295462573979135651880967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12863641715986090434587311 19295462573979135651880967)
        ·
          refine ⟨28943193860968703477821451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19295462573979135651880967 28943193860968703477821451)
          ·
            refine ⟨43414790791453055216732177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28943193860968703477821451 43414790791453055216732177)
            ·
              refine ⟨32561093093589791412549133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43414790791453055216732177 32561093093589791412549133)
              ·
                refine ⟨12210409910096171779705925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32561093093589791412549133 12210409910096171779705925)
                ·
                  refine ⟨2289451858143032208694861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12210409910096171779705925 2289451858143032208694861)
                  ·
                    refine ⟨858544446803637078260573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289451858143032208694861 858544446803637078260573)
                    ·
                      rfl

theorem cell22_2508014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2508014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508014 prefixEnd_2508014 := by exact prefixLift 2508014
  have htrace : WordTrace (prefixWord ++ tailWord_2508014) baseStart_2508014 baseEnd_2508014 := by
    simpa [prefixWord, tailWord_2508014, baseEnd_2508014] using wordTrace_append hprefix tailTrace_2508014
  have hstable : (prefixWord ++ tailWord_2508014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508014).length < 2 ^ (prefixWord ++ tailWord_2508014).sum := by decide
  have hdescent : baseEnd_2508014 < baseStart_2508014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508044 : List Nat := [2, 2, 1, 2, 2, 4, 3, 6]
def baseStart_2508044 : Nat := 118140960795 + 2508044 * 2 ^ 59
def prefixEnd_2508044 : Nat := 4983230072969 + 3 ^ 40 * 2508044 * 2
def baseEnd_2508044 : Nat := 95394968490747444445609

theorem tailTrace_2508044 : CollatzResearch.WordTrace tailWord_2508044 prefixEnd_2508044 95394968490747444445609 := by
  unfold tailWord_2508044
  simp only [CollatzResearch.WordTrace]
  refine ⟨45737939862896201329217593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60983919817194935105623457 45737939862896201329217593)
  ·
    refine ⟨34303454897172150996913195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45737939862896201329217593 34303454897172150996913195)
    ·
      refine ⟨51455182345758226495369793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34303454897172150996913195 51455182345758226495369793)
      ·
        refine ⟨38591386759318669871527345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51455182345758226495369793 38591386759318669871527345)
        ·
          refine ⟨28943540069489002403645509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38591386759318669871527345 28943540069489002403645509)
          ·
            refine ⟨5426913763029187950683533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28943540069489002403645509 5426913763029187950683533)
            ·
              refine ⟨2035092661135945481506325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5426913763029187950683533 2035092661135945481506325)
              ·
                refine ⟨95394968490747444445609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2035092661135945481506325 95394968490747444445609)
                ·
                  rfl

theorem cell22_2508044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 6].length) (baseStart_2508044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508044 prefixEnd_2508044 := by exact prefixLift 2508044
  have htrace : WordTrace (prefixWord ++ tailWord_2508044) baseStart_2508044 baseEnd_2508044 := by
    simpa [prefixWord, tailWord_2508044, baseEnd_2508044] using wordTrace_append hprefix tailTrace_2508044
  have hstable : (prefixWord ++ tailWord_2508044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508044).length < 2 ^ (prefixWord ++ tailWord_2508044).sum := by decide
  have hdescent : baseEnd_2508044 < baseStart_2508044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508046 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2508046 : Nat := 118140960795 + 2508046 * 2 ^ 59
def prefixEnd_2508046 : Nat := 4983230072969 + 3 ^ 40 * 2508046 * 2
def baseEnd_2508046 : Nat := 858555401057599661460475

theorem tailTrace_2508046 : CollatzResearch.WordTrace tailWord_2508046 prefixEnd_2508046 858555401057599661460475 := by
  unfold tailWord_2508046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11434494083973144625000999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60983968447856771333338661 11434494083973144625000999)
  ·
    refine ⟨17151741125959716937501499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11434494083973144625000999 17151741125959716937501499)
    ·
      refine ⟨25727611688939575406252249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17151741125959716937501499 25727611688939575406252249)
      ·
        refine ⟨19295708766704681554689187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25727611688939575406252249 19295708766704681554689187)
        ·
          refine ⟨28943563150057022332033781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19295708766704681554689187 28943563150057022332033781)
          ·
            refine ⟨2713459045317845843628167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28943563150057022332033781 2713459045317845843628167)
            ·
              refine ⟨4070188567976768765442251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713459045317845843628167 4070188567976768765442251)
              ·
                refine ⟨6105282851965153148163377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070188567976768765442251 6105282851965153148163377)
                ·
                  refine ⟨4578962138973864861122533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6105282851965153148163377 4578962138973864861122533)
                  ·
                    refine ⟨858555401057599661460475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4578962138973864861122533 858555401057599661460475)
                    ·
                      rfl

theorem cell22_2508046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2508046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508046 prefixEnd_2508046 := by exact prefixLift 2508046
  have htrace : WordTrace (prefixWord ++ tailWord_2508046) baseStart_2508046 baseEnd_2508046 := by
    simpa [prefixWord, tailWord_2508046, baseEnd_2508046] using wordTrace_append hprefix tailTrace_2508046
  have hstable : (prefixWord ++ tailWord_2508046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508046).length < 2 ^ (prefixWord ++ tailWord_2508046).sum := by decide
  have hdescent : baseEnd_2508046 < baseStart_2508046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508050 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_2508050 : Nat := 118140960795 + 2508050 * 2 ^ 59
def prefixEnd_2508050 : Nat := 4983230072969 + 3 ^ 40 * 2508050 * 2
def baseEnd_2508050 : Nat := 286185590113114994786821

theorem tailTrace_2508050 : CollatzResearch.WordTrace tailWord_2508050 prefixEnd_2508050 286185590113114994786821 := by
  unfold tailWord_2508050
  simp only [CollatzResearch.WordTrace]
  refine ⟨22869024640942666420788401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60984065709180443788769069 22869024640942666420788401)
  ·
    refine ⟨17151768480706999815591301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22869024640942666420788401 17151768480706999815591301)
    ·
      refine ⟨3215956590132562465423369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17151768480706999815591301 3215956590132562465423369)
      ·
        refine ⟨2411967442599421849067527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3215956590132562465423369 2411967442599421849067527)
        ·
          refine ⟨3617951163899132773601291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411967442599421849067527 3617951163899132773601291)
          ·
            refine ⟨5426926745848699160401937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617951163899132773601291 5426926745848699160401937)
            ·
              refine ⟨4070195059386524370301453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426926745848699160401937 4070195059386524370301453)
              ·
                refine ⟨1526323147269946638863045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4070195059386524370301453 1526323147269946638863045)
                ·
                  refine ⟨286185590113114994786821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1526323147269946638863045 286185590113114994786821)
                  ·
                    rfl

theorem cell22_2508050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_2508050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508050 prefixEnd_2508050 := by exact prefixLift 2508050
  have htrace : WordTrace (prefixWord ++ tailWord_2508050) baseStart_2508050 baseEnd_2508050 := by
    simpa [prefixWord, tailWord_2508050, baseEnd_2508050] using wordTrace_append hprefix tailTrace_2508050
  have hstable : (prefixWord ++ tailWord_2508050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508050).length < 2 ^ (prefixWord ++ tailWord_2508050).sum := by decide
  have hdescent : baseEnd_2508050 < baseStart_2508050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508209 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2508209 : Nat := 118140960795 + 2508209 * 2 ^ 59
def prefixEnd_2508209 : Nat := 4983230072969 + 3 ^ 40 * 2508209 * 2
def baseEnd_2508209 : Nat := 858611199288721569634975

theorem tailTrace_2508209 : CollatzResearch.WordTrace tailWord_2508209 prefixEnd_2508209 858611199288721569634975 := by
  unfold tailWord_2508209
  simp only [CollatzResearch.WordTrace]
  refine ⟨91481897770194635838191681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60987931846796423892127787 91481897770194635838191681)
  ·
    refine ⟨68611423327645976878643761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91481897770194635838191681 68611423327645976878643761)
    ·
      refine ⟨51458567495734482658982821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68611423327645976878643761 51458567495734482658982821)
      ·
        refine ⟨9648481405450215498559279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51458567495734482658982821 9648481405450215498559279)
        ·
          refine ⟨14472722108175323247838919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9648481405450215498559279 14472722108175323247838919)
          ·
            refine ⟨21709083162262984871758379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14472722108175323247838919 21709083162262984871758379)
            ·
              refine ⟨32563624743394477307637569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21709083162262984871758379 32563624743394477307637569)
              ·
                refine ⟨24422718557545857980728177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32563624743394477307637569 24422718557545857980728177)
                ·
                  refine ⟨18317038918159393485546133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24422718557545857980728177 18317038918159393485546133)
                  ·
                    refine ⟨858611199288721569634975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18317038918159393485546133 858611199288721569634975)
                    ·
                      rfl

theorem cell22_2508209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2508209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508209 prefixEnd_2508209 := by exact prefixLift 2508209
  have htrace : WordTrace (prefixWord ++ tailWord_2508209) baseStart_2508209 baseEnd_2508209 := by
    simpa [prefixWord, tailWord_2508209, baseEnd_2508209] using wordTrace_append hprefix tailTrace_2508209
  have hstable : (prefixWord ++ tailWord_2508209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508209).length < 2 ^ (prefixWord ++ tailWord_2508209).sum := by decide
  have hdescent : baseEnd_2508209 < baseStart_2508209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508239 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_2508239 : Nat := 118140960795 + 2508239 * 2 ^ 59
def prefixEnd_2508239 : Nat := 4983230072969 + 3 ^ 40 * 2508239 * 2
def baseEnd_2508239 : Nat := 858621468901811491384883

theorem tailTrace_2508239 : CollatzResearch.WordTrace tailWord_2508239 prefixEnd_2508239 858621468901811491384883 := by
  unfold tailWord_2508239
  simp only [CollatzResearch.WordTrace]
  refine ⟨91482991960085950961783771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60988661306723967307855847 91482991960085950961783771)
  ·
    refine ⟨137224487940128926442675657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91482991960085950961783771 137224487940128926442675657)
    ·
      refine ⟨102918365955096694832006743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137224487940128926442675657 102918365955096694832006743)
      ·
        refine ⟨154377548932645042248010115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102918365955096694832006743 154377548932645042248010115)
        ·
          refine ⟨231566323398967563372015173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154377548932645042248010115 231566323398967563372015173)
          ·
            refine ⟨43418685637306418132252845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231566323398967563372015173 43418685637306418132252845)
            ·
              refine ⟨16282007113989906799594817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43418685637306418132252845 16282007113989906799594817)
              ·
                refine ⟨12211505335492430099696113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16282007113989906799594817 12211505335492430099696113)
                ·
                  refine ⟨9158629001619322574772085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12211505335492430099696113 9158629001619322574772085)
                  ·
                    refine ⟨858621468901811491384883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9158629001619322574772085 858621468901811491384883)
                    ·
                      rfl

theorem cell22_2508239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_2508239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508239 prefixEnd_2508239 := by exact prefixLift 2508239
  have htrace : WordTrace (prefixWord ++ tailWord_2508239) baseStart_2508239 baseEnd_2508239 := by
    simpa [prefixWord, tailWord_2508239, baseEnd_2508239] using wordTrace_append hprefix tailTrace_2508239
  have hstable : (prefixWord ++ tailWord_2508239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508239).length < 2 ^ (prefixWord ++ tailWord_2508239).sum := by decide
  have hdescent : baseEnd_2508239 < baseStart_2508239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508271 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 1, 4]
def baseStart_2508271 : Nat := 118140960795 + 2508271 * 2 ^ 59
def prefixEnd_2508271 : Nat := 4983230072969 + 3 ^ 40 * 2508271 * 2
def baseEnd_2508271 : Nat := 858632423155774074584785

theorem tailTrace_2508271 : CollatzResearch.WordTrace tailWord_2508271 prefixEnd_2508271 858632423155774074584785 := by
  unfold tailWord_2508271
  simp only [CollatzResearch.WordTrace]
  refine ⟨91484159095970020426948667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60989439397313346951299111 91484159095970020426948667)
  ·
    refine ⟨137226238643955030640423001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91484159095970020426948667 137226238643955030640423001)
    ·
      refine ⟨102919678982966272980317251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137226238643955030640423001 102919678982966272980317251)
      ·
        refine ⟨154379518474449409470475877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102919678982966272980317251 154379518474449409470475877)
        ·
          refine ⟨28946159713959264275714227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154379518474449409470475877 28946159713959264275714227)
          ·
            refine ⟨43419239570938896413571341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28946159713959264275714227 43419239570938896413571341)
            ·
              refine ⟨16282214839102086155089253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43419239570938896413571341 16282214839102086155089253)
              ·
                refine ⟨3052915282331641154079235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16282214839102086155089253 3052915282331641154079235)
                ·
                  refine ⟨4579372923497461731118853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052915282331641154079235 4579372923497461731118853)
                  ·
                    refine ⟨858632423155774074584785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579372923497461731118853 858632423155774074584785)
                    ·
                      rfl

theorem cell22_2508271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_2508271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508271 prefixEnd_2508271 := by exact prefixLift 2508271
  have htrace : WordTrace (prefixWord ++ tailWord_2508271) baseStart_2508271 baseEnd_2508271 := by
    simpa [prefixWord, tailWord_2508271, baseEnd_2508271] using wordTrace_append hprefix tailTrace_2508271
  have hstable : (prefixWord ++ tailWord_2508271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508271).length < 2 ^ (prefixWord ++ tailWord_2508271).sum := by decide
  have hdescent : baseEnd_2508271 < baseStart_2508271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508316 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2508316 : Nat := 118140960795 + 2508316 * 2 ^ 59
def prefixEnd_2508316 : Nat := 4983230072969 + 3 ^ 40 * 2508316 * 2
def baseEnd_2508316 : Nat := 858647827575408957209647

theorem tailTrace_2508316 : CollatzResearch.WordTrace tailWord_2508316 prefixEnd_2508316 858647827575408957209647 := by
  unfold tailWord_2508316
  simp only [CollatzResearch.WordTrace]
  refine ⟨45742900190403496556168401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60990533587204662074891201 45742900190403496556168401)
  ·
    refine ⟨34307175142802622417126301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45742900190403496556168401 34307175142802622417126301)
    ·
      refine ⟨12865190678550983406422363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34307175142802622417126301 12865190678550983406422363)
      ·
        refine ⟨19297786017826475109633545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12865190678550983406422363 19297786017826475109633545)
        ·
          refine ⟨14473339513369856332225159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19297786017826475109633545 14473339513369856332225159)
          ·
            refine ⟨21710009270054784498337739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14473339513369856332225159 21710009270054784498337739)
            ·
              refine ⟨32565013905082176747506609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21710009270054784498337739 32565013905082176747506609)
              ·
                refine ⟨24423760428811632560629957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32565013905082176747506609 24423760428811632560629957)
                ·
                  refine ⟨4579455080402181105118117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24423760428811632560629957 4579455080402181105118117)
                  ·
                    refine ⟨858647827575408957209647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579455080402181105118117 858647827575408957209647)
                    ·
                      rfl

theorem cell22_2508316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2508316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508316 prefixEnd_2508316 := by exact prefixLift 2508316
  have htrace : WordTrace (prefixWord ++ tailWord_2508316) baseStart_2508316 baseEnd_2508316 := by
    simpa [prefixWord, tailWord_2508316, baseEnd_2508316] using wordTrace_append hprefix tailTrace_2508316
  have hstable : (prefixWord ++ tailWord_2508316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508316).length < 2 ^ (prefixWord ++ tailWord_2508316).sum := by decide
  have hdescent : baseEnd_2508316 < baseStart_2508316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508365 : List Nat := [1, 6, 1, 1, 3, 2, 1, 7]
def baseStart_2508365 : Nat := 118140960795 + 2508365 * 2 ^ 59
def prefixEnd_2508365 : Nat := 4983230072969 + 3 ^ 40 * 2508365 * 2
def baseEnd_2508365 : Nat := 95407177919643240303833

theorem tailTrace_2508365 : CollatzResearch.WordTrace tailWord_2508365 prefixEnd_2508365 95407177919643240303833 := by
  unfold tailWord_2508365
  simp only [CollatzResearch.WordTrace]
  refine ⟨91487587557629474480870549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60991725038419649653913699 91487587557629474480870549)
  ·
    refine ⟨4288480666763881616290807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91487587557629474480870549 4288480666763881616290807)
    ·
      refine ⟨6432721000145822424436211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4288480666763881616290807 6432721000145822424436211)
      ·
        refine ⟨9649081500218733636654317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6432721000145822424436211 9649081500218733636654317)
        ·
          refine ⟨3618405562582025113745369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9649081500218733636654317 3618405562582025113745369)
          ·
            refine ⟨2713804171936518835309027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3618405562582025113745369 2713804171936518835309027)
            ·
              refine ⟨4070706257904778252963541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713804171936518835309027 4070706257904778252963541)
              ·
                refine ⟨95407177919643240303833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4070706257904778252963541 95407177919643240303833)
                ·
                  rfl

theorem cell22_2508365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 7].length) (baseStart_2508365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508365 prefixEnd_2508365 := by exact prefixLift 2508365
  have htrace : WordTrace (prefixWord ++ tailWord_2508365) baseStart_2508365 baseEnd_2508365 := by
    simpa [prefixWord, tailWord_2508365, baseEnd_2508365] using wordTrace_append hprefix tailTrace_2508365
  have hstable : (prefixWord ++ tailWord_2508365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508365).length < 2 ^ (prefixWord ++ tailWord_2508365).sum := by decide
  have hdescent : baseEnd_2508365 < baseStart_2508365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508380 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2508380 : Nat := 118140960795 + 2508380 * 2 ^ 59
def prefixEnd_2508380 : Nat := 4983230072969 + 3 ^ 40 * 2508380 * 2
def baseEnd_2508380 : Nat := 858669736083334123609451

theorem tailTrace_2508380 : CollatzResearch.WordTrace tailWord_2508380 prefixEnd_2508380 858669736083334123609451 := by
  unfold tailWord_2508380
  simp only [CollatzResearch.WordTrace]
  refine ⟨45744067326287566021333297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60992089768383421361777729 45744067326287566021333297)
  ·
    refine ⟨34308050494715674515999973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45744067326287566021333297 34308050494715674515999973)
    ·
      refine ⟨6432759467759188971749995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34308050494715674515999973 6432759467759188971749995)
      ·
        refine ⟨9649139201638783457624993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6432759467759188971749995 9649139201638783457624993)
        ·
          refine ⟨7236854401229087593218745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9649139201638783457624993 7236854401229087593218745)
          ·
            refine ⟨5427640800921815694914059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7236854401229087593218745 5427640800921815694914059)
            ·
              refine ⟨8141461201382723542371089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427640800921815694914059 8141461201382723542371089)
              ·
                refine ⟨6106095901037042656778317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8141461201382723542371089 6106095901037042656778317)
                ·
                  refine ⟨2289785962888890996291869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6106095901037042656778317 2289785962888890996291869)
                  ·
                    refine ⟨858669736083334123609451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289785962888890996291869 858669736083334123609451)
                    ·
                      rfl

theorem cell22_2508380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2508380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508380 prefixEnd_2508380 := by exact prefixLift 2508380
  have htrace : WordTrace (prefixWord ++ tailWord_2508380) baseStart_2508380 baseEnd_2508380 := by
    simpa [prefixWord, tailWord_2508380, baseEnd_2508380] using wordTrace_append hprefix tailTrace_2508380
  have hstable : (prefixWord ++ tailWord_2508380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508380).length < 2 ^ (prefixWord ++ tailWord_2508380).sum := by decide
  have hdescent : baseEnd_2508380 < baseStart_2508380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508440 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_2508440 : Nat := 118140960795 + 2508440 * 2 ^ 59
def prefixEnd_2508440 : Nat := 4983230072969 + 3 ^ 40 * 2508440 * 2
def baseEnd_2508440 : Nat := 858690275309513967109267

theorem tailTrace_2508440 : CollatzResearch.WordTrace tailWord_2508440 prefixEnd_2508440 858690275309513967109267 := by
  unfold tailWord_2508440
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745161516178881144925387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60993548688238508193233849 45745161516178881144925387)
  ·
    refine ⟨68617742274268321717388081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45745161516178881144925387 68617742274268321717388081)
    ·
      refine ⟨51463306705701241288041061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68617742274268321717388081 51463306705701241288041061)
      ·
        refine ⟨9649370007318982741507699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51463306705701241288041061 9649370007318982741507699)
        ·
          refine ⟨14474055010978474112261549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9649370007318982741507699 14474055010978474112261549)
          ·
            refine ⟨5427770629116927792098081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14474055010978474112261549 5427770629116927792098081)
            ·
              refine ⟨4070827971837695844073561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5427770629116927792098081 4070827971837695844073561)
              ·
                refine ⟨3053120978878271883055171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4070827971837695844073561 3053120978878271883055171)
                ·
                  refine ⟨4579681468317407824582757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053120978878271883055171 4579681468317407824582757)
                  ·
                    refine ⟨858690275309513967109267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579681468317407824582757 858690275309513967109267)
                    ·
                      rfl

theorem cell22_2508440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_2508440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508440 prefixEnd_2508440 := by exact prefixLift 2508440
  have htrace : WordTrace (prefixWord ++ tailWord_2508440) baseStart_2508440 baseEnd_2508440 := by
    simpa [prefixWord, tailWord_2508440, baseEnd_2508440] using wordTrace_append hprefix tailTrace_2508440
  have hstable : (prefixWord ++ tailWord_2508440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508440).length < 2 ^ (prefixWord ++ tailWord_2508440).sum := by decide
  have hdescent : baseEnd_2508440 < baseStart_2508440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508451 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_2508451 : Nat := 118140960795 + 2508451 * 2 ^ 59
def prefixEnd_2508451 : Nat := 4983230072969 + 3 ^ 40 * 2508451 * 2
def baseEnd_2508451 : Nat := 858694040834313605084233

theorem tailTrace_2508451 : CollatzResearch.WordTrace tailWord_2508451 prefixEnd_2508451 858694040834313605084233 := by
  unfold tailWord_2508451
  simp only [CollatzResearch.WordTrace]
  refine ⟨91490724235317911168501207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60993816156878607445667471 91490724235317911168501207)
  ·
    refine ⟨137236086352976866752751811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91490724235317911168501207 137236086352976866752751811)
    ·
      refine ⟨205854129529465300129127717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137236086352976866752751811 205854129529465300129127717)
      ·
        refine ⟨38597649286774743774211447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205854129529465300129127717 38597649286774743774211447)
        ·
          refine ⟨57896473930162115661317171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38597649286774743774211447 57896473930162115661317171)
          ·
            refine ⟨86844710895243173491975757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57896473930162115661317171 86844710895243173491975757)
            ·
              refine ⟨32566766585716190059490909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86844710895243173491975757 32566766585716190059490909)
              ·
                refine ⟨12212537469643571272309091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32566766585716190059490909 12212537469643571272309091)
                ·
                  refine ⟨18318806204465356908463637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12212537469643571272309091 18318806204465356908463637)
                  ·
                    refine ⟨858694040834313605084233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18318806204465356908463637 858694040834313605084233)
                    ·
                      rfl

theorem cell22_2508451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_2508451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508451 prefixEnd_2508451 := by exact prefixLift 2508451
  have htrace : WordTrace (prefixWord ++ tailWord_2508451) baseStart_2508451 baseEnd_2508451 := by
    simpa [prefixWord, tailWord_2508451, baseEnd_2508451] using wordTrace_append hprefix tailTrace_2508451
  have hstable : (prefixWord ++ tailWord_2508451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508451).length < 2 ^ (prefixWord ++ tailWord_2508451).sum := by decide
  have hdescent : baseEnd_2508451 < baseStart_2508451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508453 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_2508453 : Nat := 118140960795 + 2508453 * 2 ^ 59
def prefixEnd_2508453 : Nat := 4983230072969 + 3 ^ 40 * 2508453 * 2
def baseEnd_2508453 : Nat := 858694725475186266534227

theorem tailTrace_2508453 : CollatzResearch.WordTrace tailWord_2508453 prefixEnd_2508453 858694725475186266534227 := by
  unfold tailWord_2508453
  simp only [CollatzResearch.WordTrace]
  refine ⟨91490797181310665510074013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60993864787540443673382675 91490797181310665510074013)
  ·
    refine ⟨34309048942991499566277755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91490797181310665510074013 34309048942991499566277755)
    ·
      refine ⟨51463573414487249349416633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34309048942991499566277755 51463573414487249349416633)
      ·
        refine ⟨38597680060865437012062475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51463573414487249349416633 38597680060865437012062475)
        ·
          refine ⟨57896520091298155518093713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38597680060865437012062475 57896520091298155518093713)
          ·
            refine ⟨43422390068473616638570285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57896520091298155518093713 43422390068473616638570285)
            ·
              refine ⟨16283396275677606239463857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43422390068473616638570285 16283396275677606239463857)
              ·
                refine ⟨12212547206758204679597893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16283396275677606239463857 12212547206758204679597893)
                ·
                  refine ⟨2289852601267163377424605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12212547206758204679597893 2289852601267163377424605)
                  ·
                    refine ⟨858694725475186266534227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289852601267163377424605 858694725475186266534227)
                    ·
                      rfl

theorem cell22_2508453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_2508453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508453 prefixEnd_2508453 := by exact prefixLift 2508453
  have htrace : WordTrace (prefixWord ++ tailWord_2508453) baseStart_2508453 baseEnd_2508453 := by
    simpa [prefixWord, tailWord_2508453, baseEnd_2508453] using wordTrace_append hprefix tailTrace_2508453
  have hstable : (prefixWord ++ tailWord_2508453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508453).length < 2 ^ (prefixWord ++ tailWord_2508453).sum := by decide
  have hdescent : baseEnd_2508453 < baseStart_2508453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508466 : List Nat := [3, 2, 1, 1, 1, 2, 12]
def baseStart_2508466 : Nat := 118140960795 + 2508466 * 2 ^ 59
def prefixEnd_2508466 : Nat := 4983230072969 + 3 ^ 40 * 2508466 * 2
def baseEnd_2508466 : Nat := 31803673171883650591081

theorem tailTrace_2508466 : CollatzResearch.WordTrace tailWord_2508466 prefixEnd_2508466 31803673171883650591081 := by
  unfold tailWord_2508466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22872817832565892182574313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60994180886842379153531501 22872817832565892182574313)
  ·
    refine ⟨17154613374424419136930735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22872817832565892182574313 17154613374424419136930735)
    ·
      refine ⟨25731920061636628705396103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17154613374424419136930735 25731920061636628705396103)
      ·
        refine ⟨38597880092454943058094155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25731920061636628705396103 38597880092454943058094155)
        ·
          refine ⟨57896820138682414587141233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38597880092454943058094155 57896820138682414587141233)
          ·
            refine ⟨43422615104011810940355925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57896820138682414587141233 43422615104011810940355925)
            ·
              refine ⟨31803673171883650591081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 43422615104011810940355925 31803673171883650591081)
              ·
                rfl

theorem cell22_2508466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 12].length) (baseStart_2508466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508466 prefixEnd_2508466 := by exact prefixLift 2508466
  have htrace : WordTrace (prefixWord ++ tailWord_2508466) baseStart_2508466 baseEnd_2508466 := by
    simpa [prefixWord, tailWord_2508466, baseEnd_2508466] using wordTrace_append hprefix tailTrace_2508466
  have hstable : (prefixWord ++ tailWord_2508466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508466).length < 2 ^ (prefixWord ++ tailWord_2508466).sum := by decide
  have hdescent : baseEnd_2508466 < baseStart_2508466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508496 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_2508496 : Nat := 118140960795 + 2508496 * 2 ^ 59
def prefixEnd_2508496 : Nat := 4983230072969 + 3 ^ 40 * 2508496 * 2
def baseEnd_2508496 : Nat := 858709445253948487709095

theorem tailTrace_2508496 : CollatzResearch.WordTrace tailWord_2508496 prefixEnd_2508496 858709445253948487709095 := by
  unfold tailWord_2508496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45746182760077441926944671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60994910346769922569259561 45746182760077441926944671)
  ·
    refine ⟨68619274140116162890417007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45746182760077441926944671 68619274140116162890417007)
    ·
      refine ⟨102928911210174244335625511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68619274140116162890417007 102928911210174244335625511)
      ·
        refine ⟨154393366815261366503438267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102928911210174244335625511 154393366815261366503438267)
        ·
          refine ⟨231590050222892049755157401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154393366815261366503438267 231590050222892049755157401)
          ·
            refine ⟨173692537667169037316368051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231590050222892049755157401 173692537667169037316368051)
            ·
              refine ⟨260538806500753555974552077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173692537667169037316368051 260538806500753555974552077)
              ·
                refine ⟨97702052437782583490457029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260538806500753555974552077 97702052437782583490457029)
                ·
                  refine ⟨18319134832084234404460693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97702052437782583490457029 18319134832084234404460693)
                  ·
                    refine ⟨858709445253948487709095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18319134832084234404460693 858709445253948487709095)
                    ·
                      rfl

theorem cell22_2508496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_2508496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508496 prefixEnd_2508496 := by exact prefixLift 2508496
  have htrace : WordTrace (prefixWord ++ tailWord_2508496) baseStart_2508496 baseEnd_2508496 := by
    simpa [prefixWord, tailWord_2508496, baseEnd_2508496] using wordTrace_append hprefix tailTrace_2508496
  have hstable : (prefixWord ++ tailWord_2508496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508496).length < 2 ^ (prefixWord ++ tailWord_2508496).sum := by decide
  have hdescent : baseEnd_2508496 < baseStart_2508496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508575 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 1, 4]
def baseStart_2508575 : Nat := 118140960795 + 2508575 * 2 ^ 59
def prefixEnd_2508575 : Nat := 4983230072969 + 3 ^ 40 * 2508575 * 2
def baseEnd_2508575 : Nat := 858736488568418614983853

theorem tailTrace_2508575 : CollatzResearch.WordTrace tailWord_2508575 prefixEnd_2508575 858736488568418614983853 := by
  unfold tailWord_2508575
  simp only [CollatzResearch.WordTrace]
  refine ⟨91495246886868680346015179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60996831257912453564010119 91495246886868680346015179)
  ·
    refine ⟨137242870330303020519022769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91495246886868680346015179 137242870330303020519022769)
    ·
      refine ⟨102932152747727265389267077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137242870330303020519022769 102932152747727265389267077)
      ·
        refine ⟨19299778640198862260487577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102932152747727265389267077 19299778640198862260487577)
        ·
          refine ⟨14474833980149146695365683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19299778640198862260487577 14474833980149146695365683)
          ·
            refine ⟨21712250970223720043048525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14474833980149146695365683 21712250970223720043048525)
            ·
              refine ⟨8142094113833895016143197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21712250970223720043048525 8142094113833895016143197)
              ·
                refine ⟨3053285292687710631053699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8142094113833895016143197 3053285292687710631053699)
                ·
                  refine ⟨4579927939031565946580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053285292687710631053699 4579927939031565946580549)
                  ·
                    refine ⟨858736488568418614983853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4579927939031565946580549 858736488568418614983853)
                    ·
                      rfl

theorem cell22_2508575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_2508575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508575 prefixEnd_2508575 := by exact prefixLift 2508575
  have htrace : WordTrace (prefixWord ++ tailWord_2508575) baseStart_2508575 baseEnd_2508575 := by
    simpa [prefixWord, tailWord_2508575, baseEnd_2508575] using wordTrace_append hprefix tailTrace_2508575
  have hstable : (prefixWord ++ tailWord_2508575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508575).length < 2 ^ (prefixWord ++ tailWord_2508575).sum := by decide
  have hdescent : baseEnd_2508575 < baseStart_2508575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508618 : List Nat := [3, 1, 2, 1, 1, 1, 5, 8]
def baseStart_2508618 : Nat := 118140960795 + 2508618 * 2 ^ 59
def prefixEnd_2508618 : Nat := 4983230072969 + 3 ^ 40 * 2508618 * 2
def baseEnd_2508618 : Nat := 95416800927464537350969

theorem tailTrace_2508618 : CollatzResearch.WordTrace tailWord_2508618 prefixEnd_2508618 95416800927464537350969 := by
  unfold tailWord_2508618
  simp only [CollatzResearch.WordTrace]
  refine ⟨22874203806428224672457627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60997876817141932459887005 22874203806428224672457627)
  ·
    refine ⟨34311305709642337008686441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22874203806428224672457627 34311305709642337008686441)
    ·
      refine ⟨25733479282231752756514831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34311305709642337008686441 25733479282231752756514831)
      ·
        refine ⟨38600218923347629134772247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25733479282231752756514831 38600218923347629134772247)
        ·
          refine ⟨57900328385021443702158371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38600218923347629134772247 57900328385021443702158371)
          ·
            refine ⟨86850492577532165553237557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57900328385021443702158371 86850492577532165553237557)
            ·
              refine ⟨8142233679143640520616021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86850492577532165553237557 8142233679143640520616021)
              ·
                refine ⟨95416800927464537350969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8142233679143640520616021 95416800927464537350969)
                ·
                  rfl

theorem cell22_2508618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_2508618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508618 prefixEnd_2508618 := by exact prefixLift 2508618
  have htrace : WordTrace (prefixWord ++ tailWord_2508618) baseStart_2508618 baseEnd_2508618 := by
    simpa [prefixWord, tailWord_2508618, baseEnd_2508618] using wordTrace_append hprefix tailTrace_2508618
  have hstable : (prefixWord ++ tailWord_2508618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508618).length < 2 ^ (prefixWord ++ tailWord_2508618).sum := by decide
  have hdescent : baseEnd_2508618 < baseStart_2508618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508701 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_2508701 : Nat := 118140960795 + 2508701 * 2 ^ 59
def prefixEnd_2508701 : Nat := 4983230072969 + 3 ^ 40 * 2508701 * 2
def baseEnd_2508701 : Nat := 858779620943396286333467

theorem tailTrace_2508701 : CollatzResearch.WordTrace tailWord_2508701 prefixEnd_2508701 858779620943396286333467 := by
  unfold tailWord_2508701
  simp only [CollatzResearch.WordTrace]
  refine ⟨91499842484412203865101957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60999894989608135910067971 91499842484412203865101957)
  ·
    refine ⟨17156220465827288224706617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91499842484412203865101957 17156220465827288224706617)
    ·
      refine ⟨12867165349370466168529963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17156220465827288224706617 12867165349370466168529963)
      ·
        refine ⟨19300748024055699252794945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12867165349370466168529963 19300748024055699252794945)
        ·
          refine ⟨14475561018041774439596209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19300748024055699252794945 14475561018041774439596209)
          ·
            refine ⟨10856670763531330829697157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14475561018041774439596209 10856670763531330829697157)
            ·
              refine ⟨2035625768162124530568217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10856670763531330829697157 2035625768162124530568217)
              ·
                refine ⟨1526719326121593397926163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035625768162124530568217 1526719326121593397926163)
                ·
                  refine ⟨2290078989182390096889245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526719326121593397926163 2290078989182390096889245)
                  ·
                    refine ⟨858779620943396286333467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290078989182390096889245 858779620943396286333467)
                    ·
                      rfl

theorem cell22_2508701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_2508701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508701 prefixEnd_2508701 := by exact prefixLift 2508701
  have htrace : WordTrace (prefixWord ++ tailWord_2508701) baseStart_2508701 baseEnd_2508701 := by
    simpa [prefixWord, tailWord_2508701, baseEnd_2508701] using wordTrace_append hprefix tailTrace_2508701
  have hstable : (prefixWord ++ tailWord_2508701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508701).length < 2 ^ (prefixWord ++ tailWord_2508701).sum := by decide
  have hdescent : baseEnd_2508701 < baseStart_2508701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508718 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2508718 : Nat := 118140960795 + 2508718 * 2 ^ 59
def prefixEnd_2508718 : Nat := 4983230072969 + 3 ^ 40 * 2508718 * 2
def baseEnd_2508718 : Nat := 858785440390813908658415

theorem tailTrace_2508718 : CollatzResearch.WordTrace tailWord_2508718 prefixEnd_2508718 858785440390813908658415 := by
  unfold tailWord_2508718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11437557815668826971058851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61000308350233743845647205 11437557815668826971058851)
  ·
    refine ⟨17156336723503240456588277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11437557815668826971058851 17156336723503240456588277)
    ·
      refine ⟨1608406567828428792805151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17156336723503240456588277 1608406567828428792805151)
      ·
        refine ⟨2412609851742643189207727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1608406567828428792805151 2412609851742643189207727)
        ·
          refine ⟨3618914777613964783811591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412609851742643189207727 3618914777613964783811591)
          ·
            refine ⟨5428372166420947175717387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618914777613964783811591 5428372166420947175717387)
            ·
              refine ⟨8142558249631420763576081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5428372166420947175717387 8142558249631420763576081)
              ·
                refine ⟨6106918687223565572682061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8142558249631420763576081 6106918687223565572682061)
                ·
                  refine ⟨2290094507708837089755773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6106918687223565572682061 2290094507708837089755773)
                  ·
                    refine ⟨858785440390813908658415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290094507708837089755773 858785440390813908658415)
                    ·
                      rfl

theorem cell22_2508718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2508718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508718 prefixEnd_2508718 := by exact prefixLift 2508718
  have htrace : WordTrace (prefixWord ++ tailWord_2508718) baseStart_2508718 baseEnd_2508718 := by
    simpa [prefixWord, tailWord_2508718, baseEnd_2508718] using wordTrace_append hprefix tailTrace_2508718
  have hstable : (prefixWord ++ tailWord_2508718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508718).length < 2 ^ (prefixWord ++ tailWord_2508718).sum := by decide
  have hdescent : baseEnd_2508718 < baseStart_2508718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508725 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 8]
def baseStart_2508725 : Nat := 118140960795 + 2508725 * 2 ^ 59
def prefixEnd_2508725 : Nat := 4983230072969 + 3 ^ 40 * 2508725 * 2
def baseEnd_2508725 : Nat := 286262612211289407911131

theorem tailTrace_2508725 : CollatzResearch.WordTrace tailWord_2508725 prefixEnd_2508725 286262612211289407911131 := by
  unfold tailWord_2508725
  simp only [CollatzResearch.WordTrace]
  refine ⟨91500717836325255963975629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61000478557550170642650419 91500717836325255963975629)
  ·
    refine ⟨34312769188621970986490861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91500717836325255963975629 34312769188621970986490861)
    ·
      refine ⟨12867288445733239119934073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34312769188621970986490861 12867288445733239119934073)
      ·
        refine ⟨9650466334299929339950555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12867288445733239119934073 9650466334299929339950555)
        ·
          refine ⟨14475699501449894009925833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9650466334299929339950555 14475699501449894009925833)
          ·
            refine ⟨10856774626087420507444375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14475699501449894009925833 10856774626087420507444375)
            ·
              refine ⟨16285161939131130761166563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10856774626087420507444375 16285161939131130761166563)
              ·
                refine ⟨24427742908696696141749845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16285161939131130761166563 24427742908696696141749845)
                ·
                  refine ⟨286262612211289407911131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24427742908696696141749845 286262612211289407911131)
                  ·
                    rfl

theorem cell22_2508725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_2508725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508725 prefixEnd_2508725 := by exact prefixLift 2508725
  have htrace : WordTrace (prefixWord ++ tailWord_2508725) baseStart_2508725 baseEnd_2508725 := by
    simpa [prefixWord, tailWord_2508725, baseEnd_2508725] using wordTrace_append hprefix tailTrace_2508725
  have hstable : (prefixWord ++ tailWord_2508725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508725).length < 2 ^ (prefixWord ++ tailWord_2508725).sum := by decide
  have hdescent : baseEnd_2508725 < baseStart_2508725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508744 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 1, 4]
def baseStart_2508744 : Nat := 118140960795 + 2508744 * 2 ^ 59
def prefixEnd_2508744 : Nat := 4983230072969 + 3 ^ 40 * 2508744 * 2
def baseEnd_2508744 : Nat := 858794340722158507508335

theorem tailTrace_2508744 : CollatzResearch.WordTrace tailWord_2508744 prefixEnd_2508744 858794340722158507508335 := by
  unfold tailWord_2508744
  simp only [CollatzResearch.WordTrace]
  refine ⟨45750705411628211104458643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61000940548837614805944857 45750705411628211104458643)
  ·
    refine ⟨68626058117442316656687965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45750705411628211104458643 68626058117442316656687965)
    ·
      refine ⟨25734771794040868746257987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68626058117442316656687965 25734771794040868746257987)
      ·
        refine ⟨38602157691061303119386981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25734771794040868746257987 38602157691061303119386981)
        ·
          refine ⟨7237904567073994334885059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38602157691061303119386981 7237904567073994334885059)
          ·
            refine ⟨10856856850610991502327589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237904567073994334885059 10856856850610991502327589)
            ·
              refine ⟨2035660659489560906686423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10856856850610991502327589 2035660659489560906686423)
              ·
                refine ⟨3053490989234341360029635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035660659489560906686423 3053490989234341360029635)
                ·
                  refine ⟨4580236483851512040044453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053490989234341360029635 4580236483851512040044453)
                  ·
                    refine ⟨858794340722158507508335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4580236483851512040044453 858794340722158507508335)
                    ·
                      rfl

theorem cell22_2508744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_2508744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508744 prefixEnd_2508744 := by exact prefixLift 2508744
  have htrace : WordTrace (prefixWord ++ tailWord_2508744) baseStart_2508744 baseEnd_2508744 := by
    simpa [prefixWord, tailWord_2508744, baseEnd_2508744] using wordTrace_append hprefix tailTrace_2508744
  have hstable : (prefixWord ++ tailWord_2508744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508744).length < 2 ^ (prefixWord ++ tailWord_2508744).sum := by decide
  have hdescent : baseEnd_2508744 < baseStart_2508744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508804 : List Nat := [2, 3, 2, 4, 1, 2, 8]
def baseStart_2508804 : Nat := 118140960795 + 2508804 * 2 ^ 59
def prefixEnd_2508804 : Nat := 4983230072969 + 3 ^ 40 * 2508804 * 2
def baseEnd_2508804 : Nat := 31807958516605124111413

theorem tailTrace_2508804 : CollatzResearch.WordTrace tailWord_2508804 prefixEnd_2508804 31807958516605124111413 := by
  unfold tailWord_2508804
  simp only [CollatzResearch.WordTrace]
  refine ⟨45751799601519526228050733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61002399468692701637400977 45751799601519526228050733)
  ·
    refine ⟨17156924850569822335519025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45751799601519526228050733 17156924850569822335519025)
    ·
      refine ⟨12867693637927366751639269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17156924850569822335519025 12867693637927366751639269)
      ·
        refine ⟨2412692557111381265932363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12867693637927366751639269 2412692557111381265932363)
        ·
          refine ⟨3619038835667071898898545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412692557111381265932363 3619038835667071898898545)
          ·
            refine ⟨2714279126750303924173909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619038835667071898898545 2714279126750303924173909)
            ·
              refine ⟨31807958516605124111413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2714279126750303924173909 31807958516605124111413)
              ·
                rfl

theorem cell22_2508804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 8].length) (baseStart_2508804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508804 prefixEnd_2508804 := by exact prefixLift 2508804
  have htrace : WordTrace (prefixWord ++ tailWord_2508804) baseStart_2508804 baseEnd_2508804 := by
    simpa [prefixWord, tailWord_2508804, baseEnd_2508804] using wordTrace_append hprefix tailTrace_2508804
  have hstable : (prefixWord ++ tailWord_2508804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508804).length < 2 ^ (prefixWord ++ tailWord_2508804).sum := by decide
  have hdescent : baseEnd_2508804 < baseStart_2508804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508819 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 1, 3]
def baseStart_2508819 : Nat := 118140960795 + 2508819 * 2 ^ 59
def prefixEnd_2508819 : Nat := 4983230072969 + 3 ^ 40 * 2508819 * 2
def baseEnd_2508819 : Nat := 858820014754883311883105

theorem tailTrace_2508819 : CollatzResearch.WordTrace tailWord_2508819 prefixEnd_2508819 858820014754883311883105 := by
  unfold tailWord_2508819
  simp only [CollatzResearch.WordTrace]
  refine ⟨91504146297984710017897511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61002764198656473345265007 91504146297984710017897511)
  ·
    refine ⟨137256219446977065026846267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91504146297984710017897511 137256219446977065026846267)
    ·
      refine ⟨205884329170465597540269401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137256219446977065026846267 205884329170465597540269401)
      ·
        refine ⟨154413246877849198155202051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205884329170465597540269401 154413246877849198155202051)
        ·
          refine ⟨231619870316773797232803077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154413246877849198155202051 231619870316773797232803077)
          ·
            refine ⟨43428725684395086981150577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231619870316773797232803077 43428725684395086981150577)
            ·
              refine ⟨32571544263296315235862933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43428725684395086981150577 32571544263296315235862933)
              ·
                refine ⟨1526791137342014776681075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32571544263296315235862933 1526791137342014776681075)
                ·
                  refine ⟨2290186706013022165021613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526791137342014776681075 2290186706013022165021613)
                  ·
                    refine ⟨858820014754883311883105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290186706013022165021613 858820014754883311883105)
                    ·
                      rfl

theorem cell22_2508819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 3].length) (baseStart_2508819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508819 prefixEnd_2508819 := by exact prefixLift 2508819
  have htrace : WordTrace (prefixWord ++ tailWord_2508819) baseStart_2508819 baseEnd_2508819 := by
    simpa [prefixWord, tailWord_2508819, baseEnd_2508819] using wordTrace_append hprefix tailTrace_2508819
  have hstable : (prefixWord ++ tailWord_2508819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508819).length < 2 ^ (prefixWord ++ tailWord_2508819).sum := by decide
  have hdescent : baseEnd_2508819 < baseStart_2508819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508909 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2508909 : Nat := 118140960795 + 2508909 * 2 ^ 59
def prefixEnd_2508909 : Nat := 4983230072969 + 3 ^ 40 * 2508909 * 2
def baseEnd_2508909 : Nat := 858850823594153077132829

theorem tailTrace_2508909 : CollatzResearch.WordTrace tailWord_2508909 prefixEnd_2508909 858850823594153077132829 := by
  unfold tailWord_2508909
  simp only [CollatzResearch.WordTrace]
  refine ⟨91507428867658655388673781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61004952578439103592449187 91507428867658655388673781)
  ·
    refine ⟨8578821456342998942688167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91507428867658655388673781 8578821456342998942688167)
    ·
      refine ⟨12868232184514498414032251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578821456342998942688167 12868232184514498414032251)
      ·
        refine ⟨19302348276771747621048377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12868232184514498414032251 19302348276771747621048377)
        ·
          refine ⟨14476761207578810715786283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19302348276771747621048377 14476761207578810715786283)
          ·
            refine ⟨21715141811368216073679425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14476761207578810715786283 21715141811368216073679425)
            ·
              refine ⟨16286356358526162055259569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21715141811368216073679425 16286356358526162055259569)
              ·
                refine ⟨12214767268894621541444677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16286356358526162055259569 12214767268894621541444677)
                ·
                  refine ⟨2290268862917741539020877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12214767268894621541444677 2290268862917741539020877)
                  ·
                    refine ⟨858850823594153077132829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290268862917741539020877 858850823594153077132829)
                    ·
                      rfl

theorem cell22_2508909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2508909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508909 prefixEnd_2508909 := by exact prefixLift 2508909
  have htrace : WordTrace (prefixWord ++ tailWord_2508909) baseStart_2508909 baseEnd_2508909 := by
    simpa [prefixWord, tailWord_2508909, baseEnd_2508909] using wordTrace_append hprefix tailTrace_2508909
  have hstable : (prefixWord ++ tailWord_2508909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508909).length < 2 ^ (prefixWord ++ tailWord_2508909).sum := by decide
  have hdescent : baseEnd_2508909 < baseStart_2508909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508988 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_2508988 : Nat := 118140960795 + 2508988 * 2 ^ 59
def prefixEnd_2508988 : Nat := 4983230072969 + 3 ^ 40 * 2508988 * 2
def baseEnd_2508988 : Nat := 858877866908623204407587

theorem tailTrace_2508988 : CollatzResearch.WordTrace tailWord_2508988 prefixEnd_2508988 858877866908623204407587 := by
  unfold tailWord_2508988
  simp only [CollatzResearch.WordTrace]
  refine ⟨45755155117186225940399809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61006873489581634587199745 45755155117186225940399809)
  ·
    refine ⟨34316366337889669455299857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45755155117186225940399809 34316366337889669455299857)
    ·
      refine ⟨25737274753417252091474893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34316366337889669455299857 25737274753417252091474893)
      ·
        refine ⟨9651478032531469534303085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25737274753417252091474893 9651478032531469534303085)
        ·
          refine ⟨3619304262199301075363657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9651478032531469534303085 3619304262199301075363657)
          ·
            refine ⟨2714478196649475806522743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619304262199301075363657 2714478196649475806522743)
            ·
              refine ⟨4071717294974213709784115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714478196649475806522743 4071717294974213709784115)
              ·
                refine ⟨6107575942461320564676173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4071717294974213709784115 6107575942461320564676173)
                ·
                  refine ⟨2290340978422995211753565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6107575942461320564676173 2290340978422995211753565)
                  ·
                    refine ⟨858877866908623204407587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290340978422995211753565 858877866908623204407587)
                    ·
                      rfl

theorem cell22_2508988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_2508988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2508988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2508988 prefixEnd_2508988 := by exact prefixLift 2508988
  have htrace : WordTrace (prefixWord ++ tailWord_2508988) baseStart_2508988 baseEnd_2508988 := by
    simpa [prefixWord, tailWord_2508988, baseEnd_2508988] using wordTrace_append hprefix tailTrace_2508988
  have hstable : (prefixWord ++ tailWord_2508988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508988).length < 2 ^ (prefixWord ++ tailWord_2508988).sum := by decide
  have hdescent : baseEnd_2508988 < baseStart_2508988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509134 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2509134 : Nat := 118140960795 + 2509134 * 2 ^ 59
def prefixEnd_2509134 : Nat := 4983230072969 + 3 ^ 40 * 2509134 * 2
def baseEnd_2509134 : Nat := 858927845692327490257139

theorem tailTrace_2509134 : CollatzResearch.WordTrace tailWord_2509134 prefixEnd_2509134 858927845692327490257139 := by
  unfold tailWord_2509134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439454411480439851951807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61010423527895679210409637 11439454411480439851951807)
  ·
    refine ⟨17159181617220659777927711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11439454411480439851951807 17159181617220659777927711)
    ·
      refine ⟨25738772425830989666891567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17159181617220659777927711 25738772425830989666891567)
      ·
        refine ⟨38608158638746484500337351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25738772425830989666891567 38608158638746484500337351)
        ·
          refine ⟨57912237958119726750506027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38608158638746484500337351 57912237958119726750506027)
          ·
            refine ⟨86868356937179590125759041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57912237958119726750506027 86868356937179590125759041)
            ·
              refine ⟨65151267702884692594319281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86868356937179590125759041 65151267702884692594319281)
              ·
                refine ⟨48863450777163519445739461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65151267702884692594319281 48863450777163519445739461)
                ·
                  refine ⟨9161897020718159896076149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48863450777163519445739461 9161897020718159896076149)
                  ·
                    refine ⟨858927845692327490257139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9161897020718159896076149 858927845692327490257139)
                    ·
                      rfl

theorem cell22_2509134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2509134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509134 prefixEnd_2509134 := by exact prefixLift 2509134
  have htrace : WordTrace (prefixWord ++ tailWord_2509134) baseStart_2509134 baseEnd_2509134 := by
    simpa [prefixWord, tailWord_2509134, baseEnd_2509134] using wordTrace_append hprefix tailTrace_2509134
  have hstable : (prefixWord ++ tailWord_2509134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509134).length < 2 ^ (prefixWord ++ tailWord_2509134).sum := by decide
  have hdescent : baseEnd_2509134 < baseStart_2509134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509140 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2509140 : Nat := 118140960795 + 2509140 * 2 ^ 59
def prefixEnd_2509140 : Nat := 4983230072969 + 3 ^ 40 * 2509140 * 2
def baseEnd_2509140 : Nat := 858929899614945474607121

theorem tailTrace_2509140 : CollatzResearch.WordTrace tailWord_2509140 prefixEnd_2509140 858929899614945474607121 := by
  unfold tailWord_2509140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45757927064910890920166437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61010569419881187893555249 45757927064910890920166437)
  ·
    refine ⟨8579611324670792047531207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45757927064910890920166437 8579611324670792047531207)
    ·
      refine ⟨12869416987006188071296811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8579611324670792047531207 12869416987006188071296811)
      ·
        refine ⟨19304125480509282106945217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12869416987006188071296811 19304125480509282106945217)
        ·
          refine ⟨14478094110381961580208913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19304125480509282106945217 14478094110381961580208913)
          ·
            refine ⟨10858570582786471185156685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14478094110381961580208913 10858570582786471185156685)
            ·
              refine ⟨4071963968544926694433757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10858570582786471185156685 4071963968544926694433757)
              ·
                refine ⟨1526986488204347510412659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4071963968544926694433757 1526986488204347510412659)
                ·
                  refine ⟨2290479732306521265618989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526986488204347510412659 2290479732306521265618989)
                  ·
                    refine ⟨858929899614945474607121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290479732306521265618989 858929899614945474607121)
                    ·
                      rfl

theorem cell22_2509140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2509140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509140 prefixEnd_2509140 := by exact prefixLift 2509140
  have htrace : WordTrace (prefixWord ++ tailWord_2509140) baseStart_2509140 baseEnd_2509140 := by
    simpa [prefixWord, tailWord_2509140, baseEnd_2509140] using wordTrace_append hprefix tailTrace_2509140
  have hstable : (prefixWord ++ tailWord_2509140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509140).length < 2 ^ (prefixWord ++ tailWord_2509140).sum := by decide
  have hdescent : baseEnd_2509140 < baseStart_2509140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509196 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_2509196 : Nat := 118140960795 + 2509196 * 2 ^ 59
def prefixEnd_2509196 : Nat := 4983230072969 + 3 ^ 40 * 2509196 * 2
def baseEnd_2509196 : Nat := 858949069559379995206949

theorem tailTrace_2509196 : CollatzResearch.WordTrace tailWord_2509196 prefixEnd_2509196 858949069559379995206949 := by
  unfold tailWord_2509196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45758948308809451702185721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61011931078412602269580961 45758948308809451702185721)
  ·
    refine ⟨34319211231607088776639291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45758948308809451702185721 34319211231607088776639291)
    ·
      refine ⟨51478816847410633164958937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34319211231607088776639291 51478816847410633164958937)
      ·
        refine ⟨38609112635557974873719203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51478816847410633164958937 38609112635557974873719203)
        ·
          refine ⟨57913668953336962310578805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38609112635557974873719203 57913668953336962310578805)
          ·
            refine ⟨5429406464375340216616763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57913668953336962310578805 5429406464375340216616763)
            ·
              refine ⟨8144109696563010324925145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5429406464375340216616763 8144109696563010324925145)
              ·
                refine ⟨6108082272422257743693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8144109696563010324925145 6108082272422257743693859)
                ·
                  refine ⟨9162123408633386615540789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6108082272422257743693859 9162123408633386615540789)
                  ·
                    refine ⟨858949069559379995206949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9162123408633386615540789 858949069559379995206949)
                    ·
                      rfl

theorem cell22_2509196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_2509196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509196 prefixEnd_2509196 := by exact prefixLift 2509196
  have htrace : WordTrace (prefixWord ++ tailWord_2509196) baseStart_2509196 baseEnd_2509196 := by
    simpa [prefixWord, tailWord_2509196, baseEnd_2509196] using wordTrace_append hprefix tailTrace_2509196
  have hstable : (prefixWord ++ tailWord_2509196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509196).length < 2 ^ (prefixWord ++ tailWord_2509196).sum := by decide
  have hdescent : baseEnd_2509196 < baseStart_2509196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509249 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 4]
def baseStart_2509249 : Nat := 118140960795 + 2509249 * 2 ^ 59
def prefixEnd_2509249 : Nat := 4983230072969 + 3 ^ 40 * 2509249 * 2
def baseEnd_2509249 : Nat := 286322404180835174543929

theorem tailTrace_2509249 : CollatzResearch.WordTrace tailWord_2509249 prefixEnd_2509249 286322404180835174543929 := by
  unfold tailWord_2509249
  simp only [CollatzResearch.WordTrace]
  refine ⟨91519829686426893456050801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61013219790951262304033867 91519829686426893456050801)
  ·
    refine ⟨68639872264820170092038101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91519829686426893456050801 68639872264820170092038101)
    ·
      refine ⟨1608747006206722736532143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 68639872264820170092038101 1608747006206722736532143)
      ·
        refine ⟨2413120509310084104798215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1608747006206722736532143 2413120509310084104798215)
        ·
          refine ⟨3619680763965126157197323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413120509310084104798215 3619680763965126157197323)
          ·
            refine ⟨5429521145947689235795985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619680763965126157197323 5429521145947689235795985)
            ·
              refine ⟨4072140859460766926846989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429521145947689235795985 4072140859460766926846989)
              ·
                refine ⟨1527052822297787597567621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4072140859460766926846989 1527052822297787597567621)
                ·
                  refine ⟨286322404180835174543929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1527052822297787597567621 286322404180835174543929)
                  ·
                    rfl

theorem cell22_2509249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_2509249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509249 prefixEnd_2509249 := by exact prefixLift 2509249
  have htrace : WordTrace (prefixWord ++ tailWord_2509249) baseStart_2509249 baseEnd_2509249 := by
    simpa [prefixWord, tailWord_2509249, baseEnd_2509249] using wordTrace_append hprefix tailTrace_2509249
  have hstable : (prefixWord ++ tailWord_2509249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509249).length < 2 ^ (prefixWord ++ tailWord_2509249).sum := by decide
  have hdescent : baseEnd_2509249 < baseStart_2509249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509352 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2509352 : Nat := 118140960795 + 2509352 * 2 ^ 59
def prefixEnd_2509352 : Nat := 4983230072969 + 3 ^ 40 * 2509352 * 2
def baseEnd_2509352 : Nat := 859002471547447588306471

theorem tailTrace_2509352 : CollatzResearch.WordTrace tailWord_2509352 prefixEnd_2509352 859002471547447588306471 := by
  unfold tailWord_2509352
  simp only [CollatzResearch.WordTrace]
  refine ⟨45761793202526871023525155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61015724270035828031366873 45761793202526871023525155)
  ·
    refine ⟨68642689803790306535287733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45761793202526871023525155 68642689803790306535287733)
    ·
      refine ⟨6435252169105341237683225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68642689803790306535287733 6435252169105341237683225)
      ·
        refine ⟨4826439126829005928262419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6435252169105341237683225 4826439126829005928262419)
        ·
          refine ⟨7239658690243508892393629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826439126829005928262419 7239658690243508892393629)
          ·
            refine ⟨2714872008841315834647611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7239658690243508892393629 2714872008841315834647611)
            ·
              refine ⟨4072308013261973751971417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714872008841315834647611 4072308013261973751971417)
              ·
                refine ⟨3054231009946480313978563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072308013261973751971417 3054231009946480313978563)
                ·
                  refine ⟨4581346514919720470967845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054231009946480313978563 4581346514919720470967845)
                  ·
                    refine ⟨859002471547447588306471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581346514919720470967845 859002471547447588306471)
                    ·
                      rfl

theorem cell22_2509352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2509352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509352 prefixEnd_2509352 := by exact prefixLift 2509352
  have htrace : WordTrace (prefixWord ++ tailWord_2509352) baseStart_2509352 baseEnd_2509352 := by
    simpa [prefixWord, tailWord_2509352, baseEnd_2509352] using wordTrace_append hprefix tailTrace_2509352
  have hstable : (prefixWord ++ tailWord_2509352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509352).length < 2 ^ (prefixWord ++ tailWord_2509352).sum := by decide
  have hdescent : baseEnd_2509352 < baseStart_2509352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509361 : List Nat := [1, 2, 2, 3, 1, 1, 4, 8]
def baseStart_2509361 : Nat := 118140960795 + 2509361 * 2 ^ 59
def prefixEnd_2509361 : Nat := 4983230072969 + 3 ^ 40 * 2509361 * 2
def baseEnd_2509361 : Nat := 95445061381263840536827

theorem tailTrace_2509361 : CollatzResearch.WordTrace tailWord_2509361 prefixEnd_2509361 95445061381263840536827 := by
  unfold tailWord_2509361
  simp only [CollatzResearch.WordTrace]
  refine ⟨91523914662021136584127937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61015943108014091056085291 91523914662021136584127937)
  ·
    refine ⟨68642935996515852438095953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91523914662021136584127937 68642935996515852438095953)
    ·
      refine ⟨51482201997386889328571965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68642935996515852438095953 51482201997386889328571965)
      ·
        refine ⟨19305825749020083498214487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51482201997386889328571965 19305825749020083498214487)
        ·
          refine ⟨28958738623530125247321731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19305825749020083498214487 28958738623530125247321731)
          ·
            refine ⟨43438107935295187870982597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28958738623530125247321731 43438107935295187870982597)
            ·
              refine ⟨8144645237867847725809237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43438107935295187870982597 8144645237867847725809237)
              ·
                refine ⟨95445061381263840536827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8144645237867847725809237 95445061381263840536827)
                ·
                  rfl

theorem cell22_2509361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 8].length) (baseStart_2509361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509361 prefixEnd_2509361 := by exact prefixLift 2509361
  have htrace : WordTrace (prefixWord ++ tailWord_2509361) baseStart_2509361 baseEnd_2509361 := by
    simpa [prefixWord, tailWord_2509361, baseEnd_2509361] using wordTrace_append hprefix tailTrace_2509361
  have hstable : (prefixWord ++ tailWord_2509361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509361).length < 2 ^ (prefixWord ++ tailWord_2509361).sum := by decide
  have hdescent : baseEnd_2509361 < baseStart_2509361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509363 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 2, 4]
def baseStart_2509363 : Nat := 118140960795 + 2509363 * 2 ^ 59
def prefixEnd_2509363 : Nat := 4983230072969 + 3 ^ 40 * 2509363 * 2
def baseEnd_2509363 : Nat := 859006237072247226281437

theorem tailTrace_2509363 : CollatzResearch.WordTrace tailWord_2509363 prefixEnd_2509363 859006237072247226281437 := by
  unfold tailWord_2509363
  simp only [CollatzResearch.WordTrace]
  refine ⟨91523987608013890925700743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61015991738675927283800495 91523987608013890925700743)
  ·
    refine ⟨137285981412020836388551115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91523987608013890925700743 137285981412020836388551115)
    ·
      refine ⟨205928972118031254582826673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137285981412020836388551115 205928972118031254582826673)
      ·
        refine ⟨154446729088523440937120005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205928972118031254582826673 154446729088523440937120005)
        ·
          refine ⟨28958761704098145175710001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154446729088523440937120005 28958761704098145175710001)
          ·
            refine ⟨21719071278073608881782501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28958761704098145175710001 21719071278073608881782501)
            ·
              refine ⟨4072325864638801665334219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21719071278073608881782501 4072325864638801665334219)
              ·
                refine ⟨6108488796958202498001329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072325864638801665334219 6108488796958202498001329)
                ·
                  refine ⟨4581366597718651873500997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108488796958202498001329 4581366597718651873500997)
                  ·
                    refine ⟨859006237072247226281437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581366597718651873500997 859006237072247226281437)
                    ·
                      rfl

theorem cell22_2509363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 4].length) (baseStart_2509363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509363 prefixEnd_2509363 := by exact prefixLift 2509363
  have htrace : WordTrace (prefixWord ++ tailWord_2509363) baseStart_2509363 baseEnd_2509363 := by
    simpa [prefixWord, tailWord_2509363, baseEnd_2509363] using wordTrace_append hprefix tailTrace_2509363
  have hstable : (prefixWord ++ tailWord_2509363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509363).length < 2 ^ (prefixWord ++ tailWord_2509363).sum := by decide
  have hdescent : baseEnd_2509363 < baseStart_2509363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509391 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_2509391 : Nat := 118140960795 + 2509391 * 2 ^ 59
def prefixEnd_2509391 : Nat := 4983230072969 + 3 ^ 40 * 2509391 * 2
def baseEnd_2509391 : Nat := 859015822044464486581351

theorem tailTrace_2509391 : CollatzResearch.WordTrace tailWord_2509391 prefixEnd_2509391 859015822044464486581351 := by
  unfold tailWord_2509391
  simp only [CollatzResearch.WordTrace]
  refine ⟨91525008851912451707720027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61016672567941634471813351 91525008851912451707720027)
  ·
    refine ⟨137287513277868677561580041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91525008851912451707720027 137287513277868677561580041)
    ·
      refine ⟨102965634958401508171185031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137287513277868677561580041 102965634958401508171185031)
      ·
        refine ⟨154448452437602262256777547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102965634958401508171185031 154448452437602262256777547)
        ·
          refine ⟨231672678656403393385166321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154448452437602262256777547 231672678656403393385166321)
          ·
            refine ⟨173754508992302545038874741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231672678656403393385166321 173754508992302545038874741)
            ·
              refine ⟨16289485218028363597394507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173754508992302545038874741 16289485218028363597394507)
              ·
                refine ⟨24434227827042545396091761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16289485218028363597394507 24434227827042545396091761)
                ·
                  refine ⟨18325670870281909047068821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24434227827042545396091761 18325670870281909047068821)
                  ·
                    refine ⟨859015822044464486581351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18325670870281909047068821 859015822044464486581351)
                    ·
                      rfl

theorem cell22_2509391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_2509391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509391 prefixEnd_2509391 := by exact prefixLift 2509391
  have htrace : WordTrace (prefixWord ++ tailWord_2509391) baseStart_2509391 baseEnd_2509391 := by
    simpa [prefixWord, tailWord_2509391, baseEnd_2509391] using wordTrace_append hprefix tailTrace_2509391
  have hstable : (prefixWord ++ tailWord_2509391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509391).length < 2 ^ (prefixWord ++ tailWord_2509391).sum := by decide
  have hdescent : baseEnd_2509391 < baseStart_2509391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509440 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 5]
def baseStart_2509440 : Nat := 118140960795 + 2509440 * 2 ^ 59
def prefixEnd_2509440 : Nat := 4983230072969 + 3 ^ 40 * 2509440 * 2
def baseEnd_2509440 : Nat := 286344198581948230702067

theorem tailTrace_2509440 : CollatzResearch.WordTrace tailWord_2509440 prefixEnd_2509440 286344198581948230702067 := by
  unfold tailWord_2509440
  simp only [CollatzResearch.WordTrace]
  refine ⟨45763398014367466538126887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61017864019156622050835849 45763398014367466538126887)
  ·
    refine ⟨68645097021551199807190331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45763398014367466538126887 68645097021551199807190331)
    ·
      refine ⟨102967645532326799710785497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68645097021551199807190331 102967645532326799710785497)
      ·
        refine ⟨77225734149245099783089123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102967645532326799710785497 77225734149245099783089123)
        ·
          refine ⟨115838601223867649674633685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77225734149245099783089123 115838601223867649674633685)
          ·
            refine ⟨2714967216184398039249227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 115838601223867649674633685 2714967216184398039249227)
            ·
              refine ⟨4072450824276597058873841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714967216184398039249227 4072450824276597058873841)
              ·
                refine ⟨3054338118207447794155381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072450824276597058873841 3054338118207447794155381)
                ·
                  refine ⟨286344198581948230702067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3054338118207447794155381 286344198581948230702067)
                  ·
                    rfl

theorem cell22_2509440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_2509440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509440 prefixEnd_2509440 := by exact prefixLift 2509440
  have htrace : WordTrace (prefixWord ++ tailWord_2509440) baseStart_2509440 baseEnd_2509440 := by
    simpa [prefixWord, tailWord_2509440, baseEnd_2509440] using wordTrace_append hprefix tailTrace_2509440
  have hstable : (prefixWord ++ tailWord_2509440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509440).length < 2 ^ (prefixWord ++ tailWord_2509440).sum := by decide
  have hdescent : baseEnd_2509440 < baseStart_2509440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509500 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_2509500 : Nat := 118140960795 + 2509500 * 2 ^ 59
def prefixEnd_2509500 : Nat := 4983230072969 + 3 ^ 40 * 2509500 * 2
def baseEnd_2509500 : Nat := 859053134972024535606017

theorem tailTrace_2509500 : CollatzResearch.WordTrace tailWord_2509500 prefixEnd_2509500 859053134972024535606017 := by
  unfold tailWord_2509500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45764492204258781661718977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61019322939011708882291969 45764492204258781661718977)
  ·
    refine ⟨34323369153194086246289233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45764492204258781661718977 34323369153194086246289233)
    ·
      refine ⟨25742526864895564684716925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34323369153194086246289233 25742526864895564684716925)
      ·
        refine ⟨9653447574335836756768847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25742526864895564684716925 9653447574335836756768847)
        ·
          refine ⟨14480171361503755135153271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9653447574335836756768847 14480171361503755135153271)
          ·
            refine ⟨21720257042255632702729907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14480171361503755135153271 21720257042255632702729907)
            ·
              refine ⟨32580385563383449054094861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21720257042255632702729907 32580385563383449054094861)
              ·
                refine ⟨12217644586268793395285573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32580385563383449054094861 12217644586268793395285573)
                ·
                  refine ⟨2290808359925398761616045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12217644586268793395285573 2290808359925398761616045)
                  ·
                    refine ⟨859053134972024535606017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290808359925398761616045 859053134972024535606017)
                    ·
                      rfl

theorem cell22_2509500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_2509500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509500 prefixEnd_2509500 := by exact prefixLift 2509500
  have htrace : WordTrace (prefixWord ++ tailWord_2509500) baseStart_2509500 baseEnd_2509500 := by
    simpa [prefixWord, tailWord_2509500, baseEnd_2509500] using wordTrace_append hprefix tailTrace_2509500
  have hstable : (prefixWord ++ tailWord_2509500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509500).length < 2 ^ (prefixWord ++ tailWord_2509500).sum := by decide
  have hdescent : baseEnd_2509500 < baseStart_2509500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509532 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2509532 : Nat := 118140960795 + 2509532 * 2 ^ 59
def prefixEnd_2509532 : Nat := 4983230072969 + 3 ^ 40 * 2509532 * 2
def baseEnd_2509532 : Nat := 859064089225987118805919

theorem tailTrace_2509532 : CollatzResearch.WordTrace tailWord_2509532 prefixEnd_2509532 859064089225987118805919 := by
  unfold tailWord_2509532
  simp only [CollatzResearch.WordTrace]
  refine ⟨45765075772200816394301425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61020101029601088525735233 45765075772200816394301425)
  ·
    refine ⟨34323806829150612295726069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45765075772200816394301425 34323806829150612295726069)
    ·
      refine ⟨3217856890232869902724319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34323806829150612295726069 3217856890232869902724319)
      ·
        refine ⟨4826785335349304854086479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217856890232869902724319 4826785335349304854086479)
        ·
          refine ⟨7240178003023957281129719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826785335349304854086479 7240178003023957281129719)
          ·
            refine ⟨10860267004535935921694579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240178003023957281129719 10860267004535935921694579)
            ·
              refine ⟨16290400506803903882541869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10860267004535935921694579 16290400506803903882541869)
              ·
                refine ⟨6108900190051463955953201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16290400506803903882541869 6108900190051463955953201)
                ·
                  refine ⟨4581675142538597966964901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108900190051463955953201 4581675142538597966964901)
                  ·
                    refine ⟨859064089225987118805919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581675142538597966964901 859064089225987118805919)
                    ·
                      rfl

theorem cell22_2509532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2509532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509532 prefixEnd_2509532 := by exact prefixLift 2509532
  have htrace : WordTrace (prefixWord ++ tailWord_2509532) baseStart_2509532 baseEnd_2509532 := by
    simpa [prefixWord, tailWord_2509532, baseEnd_2509532] using wordTrace_append hprefix tailTrace_2509532
  have hstable : (prefixWord ++ tailWord_2509532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509532).length < 2 ^ (prefixWord ++ tailWord_2509532).sum := by decide
  have hdescent : baseEnd_2509532 < baseStart_2509532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509603 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 10]
def baseStart_2509603 : Nat := 118140960795 + 2509603 * 2 ^ 59
def prefixEnd_2509603 : Nat := 4983230072969 + 3 ^ 40 * 2509603 * 2
def baseEnd_2509603 : Nat := 286362797992322200093567

theorem tailTrace_2509603 : CollatzResearch.WordTrace tailWord_2509603 prefixEnd_2509603 286362797992322200093567 := by
  unfold tailWord_2509603
  simp only [CollatzResearch.WordTrace]
  refine ⟨91532741127144411914437463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61021827418096274609624975 91532741127144411914437463)
  ·
    refine ⟨137299111690716617871656195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91532741127144411914437463 137299111690716617871656195)
    ·
      refine ⟨205948667536074926807484293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137299111690716617871656195 205948667536074926807484293)
      ·
        refine ⟨38615375163014048776403305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205948667536074926807484293 38615375163014048776403305)
        ·
          refine ⟨28961531372260536582302479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38615375163014048776403305 28961531372260536582302479)
          ·
            refine ⟨43442297058390804873453719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28961531372260536582302479 43442297058390804873453719)
            ·
              refine ⟨65163445587586207310180579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43442297058390804873453719 65163445587586207310180579)
              ·
                refine ⟨97745168381379310965270869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65163445587586207310180579 97745168381379310965270869)
                ·
                  refine ⟨286362797992322200093567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97745168381379310965270869 286362797992322200093567)
                  ·
                    rfl

theorem cell22_2509603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_2509603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509603 prefixEnd_2509603 := by exact prefixLift 2509603
  have htrace : WordTrace (prefixWord ++ tailWord_2509603) baseStart_2509603 baseEnd_2509603 := by
    simpa [prefixWord, tailWord_2509603, baseEnd_2509603] using wordTrace_append hprefix tailTrace_2509603
  have hstable : (prefixWord ++ tailWord_2509603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509603).length < 2 ^ (prefixWord ++ tailWord_2509603).sum := by decide
  have hdescent : baseEnd_2509603 < baseStart_2509603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509650 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2509650 : Nat := 118140960795 + 2509650 * 2 ^ 59
def prefixEnd_2509650 : Nat := 4983230072969 + 3 ^ 40 * 2509650 * 2
def baseEnd_2509650 : Nat := 859104483037474144355557

theorem tailTrace_2509650 : CollatzResearch.WordTrace tailWord_2509650 prefixEnd_2509650 859104483037474144355557 := by
  unfold tailWord_2509650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22883613839493534735349601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61022970238649425960932269 22883613839493534735349601)
  ·
    refine ⟨17162710379620151051512201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22883613839493534735349601 17162710379620151051512201)
    ·
      refine ⟨12872032784715113288634151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17162710379620151051512201 12872032784715113288634151)
      ·
        refine ⟨19308049177072669932951227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872032784715113288634151 19308049177072669932951227)
        ·
          refine ⟨28962073765609004899426841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19308049177072669932951227 28962073765609004899426841)
          ·
            refine ⟨21721555324206753674570131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28962073765609004899426841 21721555324206753674570131)
            ·
              refine ⟨32582332986310130511855197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21721555324206753674570131 32582332986310130511855197)
              ·
                refine ⟨12218374869866298941945699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32582332986310130511855197 12218374869866298941945699)
                ·
                  refine ⟨18327562304799448412918549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12218374869866298941945699 18327562304799448412918549)
                  ·
                    refine ⟨859104483037474144355557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18327562304799448412918549 859104483037474144355557)
                    ·
                      rfl

theorem cell22_2509650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2509650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509650 prefixEnd_2509650 := by exact prefixLift 2509650
  have htrace : WordTrace (prefixWord ++ tailWord_2509650) baseStart_2509650 baseEnd_2509650 := by
    simpa [prefixWord, tailWord_2509650, baseEnd_2509650] using wordTrace_append hprefix tailTrace_2509650
  have hstable : (prefixWord ++ tailWord_2509650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509650).length < 2 ^ (prefixWord ++ tailWord_2509650).sum := by decide
  have hdescent : baseEnd_2509650 < baseStart_2509650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509667 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 2, 4]
def baseStart_2509667 : Nat := 118140960795 + 2509667 * 2 ^ 59
def prefixEnd_2509667 : Nat := 4983230072969 + 3 ^ 40 * 2509667 * 2
def baseEnd_2509667 : Nat := 859110302484891766680505

theorem tailTrace_2509667 : CollatzResearch.WordTrace tailWord_2509667 prefixEnd_2509667 859110302484891766680505 := by
  unfold tailWord_2509667
  simp only [CollatzResearch.WordTrace]
  refine ⟨91535075398912550844767255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61023383599275033896511503 91535075398912550844767255)
  ·
    refine ⟨137302613098368826267150883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91535075398912550844767255 137302613098368826267150883)
    ·
      refine ⟨205953919647553239400726325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137302613098368826267150883 205953919647553239400726325)
      ·
        refine ⟨19308179966958116193818093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205953919647553239400726325 19308179966958116193818093)
        ·
          refine ⟨7240567487609293572681785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19308179966958116193818093 7240567487609293572681785)
          ·
            refine ⟨5430425615706970179511339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240567487609293572681785 5430425615706970179511339)
            ·
              refine ⟨8145638423560455269267009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430425615706970179511339 8145638423560455269267009)
              ·
                refine ⟨6109228817670341451950257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8145638423560455269267009 6109228817670341451950257)
                ·
                  refine ⟨4581921613252756088962693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6109228817670341451950257 4581921613252756088962693)
                  ·
                    refine ⟨859110302484891766680505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581921613252756088962693 859110302484891766680505)
                    ·
                      rfl

theorem cell22_2509667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_2509667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509667 prefixEnd_2509667 := by exact prefixLift 2509667
  have htrace : WordTrace (prefixWord ++ tailWord_2509667) baseStart_2509667 baseEnd_2509667 := by
    simpa [prefixWord, tailWord_2509667, baseEnd_2509667] using wordTrace_append hprefix tailTrace_2509667
  have hstable : (prefixWord ++ tailWord_2509667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509667).length < 2 ^ (prefixWord ++ tailWord_2509667).sum := by decide
  have hdescent : baseEnd_2509667 < baseStart_2509667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509686 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_2509686 : Nat := 118140960795 + 2509686 * 2 ^ 59
def prefixEnd_2509686 : Nat := 4983230072969 + 3 ^ 40 * 2509686 * 2
def baseEnd_2509686 : Nat := 859116806573182050455447

theorem tailTrace_2509686 : CollatzResearch.WordTrace tailWord_2509686 prefixEnd_2509686 859116806573182050455447 := by
  unfold tailWord_2509686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720985524115232318106807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61023845590562478059805941 5720985524115232318106807)
  ·
    refine ⟨8581478286172848477160211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5720985524115232318106807 8581478286172848477160211)
    ·
      refine ⟨12872217429259272715740317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8581478286172848477160211 12872217429259272715740317)
      ·
        refine ⟨4827081535972227268402619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12872217429259272715740317 4827081535972227268402619)
        ·
          refine ⟨7240622303958340902603929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827081535972227268402619 7240622303958340902603929)
          ·
            refine ⟨5430466727968755676952947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240622303958340902603929 5430466727968755676952947)
            ·
              refine ⟨8145700091953133515429421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430466727968755676952947 8145700091953133515429421)
              ·
                refine ⟨3054637534482425068286033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8145700091953133515429421 3054637534482425068286033)
                ·
                  refine ⟨2290978150861818801214525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054637534482425068286033 2290978150861818801214525)
                  ·
                    refine ⟨859116806573182050455447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2290978150861818801214525 859116806573182050455447)
                    ·
                      rfl

theorem cell22_2509686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_2509686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509686 prefixEnd_2509686 := by exact prefixLift 2509686
  have htrace : WordTrace (prefixWord ++ tailWord_2509686) baseStart_2509686 baseEnd_2509686 := by
    simpa [prefixWord, tailWord_2509686, baseEnd_2509686] using wordTrace_append hprefix tailTrace_2509686
  have hstable : (prefixWord ++ tailWord_2509686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509686).length < 2 ^ (prefixWord ++ tailWord_2509686).sum := by decide
  have hdescent : baseEnd_2509686 < baseStart_2509686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509727 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 5]
def baseStart_2509727 : Nat := 118140960795 + 2509727 * 2 ^ 59
def prefixEnd_2509727 : Nat := 4983230072969 + 3 ^ 40 * 2509727 * 2
def baseEnd_2509727 : Nat := 286376947237023870060107

theorem tailTrace_2509727 : CollatzResearch.WordTrace tailWord_2509727 prefixEnd_2509727 286376947237023870060107 := by
  unfold tailWord_2509727
  simp only [CollatzResearch.WordTrace]
  refine ⟨91537263778695181091951435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61024842519130120727967623 91537263778695181091951435)
  ·
    refine ⟨137305895668042771637927153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91537263778695181091951435 137305895668042771637927153)
    ·
      refine ⟨102979421751032078728445365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137305895668042771637927153 102979421751032078728445365)
      ·
        refine ⟨9654320789159257380791753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102979421751032078728445365 9654320789159257380791753)
        ·
          refine ⟨7240740591869443035593815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9654320789159257380791753 7240740591869443035593815)
          ·
            refine ⟨10861110887804164553390723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240740591869443035593815 10861110887804164553390723)
            ·
              refine ⟨16291666331706246830086085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10861110887804164553390723 16291666331706246830086085)
              ·
                refine ⟨3054687437194921280641141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16291666331706246830086085 3054687437194921280641141)
                ·
                  refine ⟨286376947237023870060107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3054687437194921280641141 286376947237023870060107)
                  ·
                    rfl

theorem cell22_2509727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 5].length) (baseStart_2509727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509727 prefixEnd_2509727 := by exact prefixLift 2509727
  have htrace : WordTrace (prefixWord ++ tailWord_2509727) baseStart_2509727 baseEnd_2509727 := by
    simpa [prefixWord, tailWord_2509727, baseEnd_2509727] using wordTrace_append hprefix tailTrace_2509727
  have hstable : (prefixWord ++ tailWord_2509727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509727).length < 2 ^ (prefixWord ++ tailWord_2509727).sum := by decide
  have hdescent : baseEnd_2509727 < baseStart_2509727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509731 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 1, 3]
def baseStart_2509731 : Nat := 118140960795 + 2509731 * 2 ^ 59
def prefixEnd_2509731 : Nat := 4983230072969 + 3 ^ 40 * 2509731 * 2
def baseEnd_2509731 : Nat := 859132210992816933080309

theorem tailTrace_2509731 : CollatzResearch.WordTrace tailWord_2509731 prefixEnd_2509731 859132210992816933080309 := by
  unfold tailWord_2509731
  simp only [CollatzResearch.WordTrace]
  refine ⟨91537409670680689775097047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61024939780453793183398031 91537409670680689775097047)
  ·
    refine ⟨137306114506021034662645571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91537409670680689775097047 137306114506021034662645571)
    ·
      refine ⟨205959171759031551993968357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137306114506021034662645571 205959171759031551993968357)
      ·
        refine ⟨38617344704818415998869067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205959171759031551993968357 38617344704818415998869067)
        ·
          refine ⟨57926017057227623998303601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38617344704818415998869067 57926017057227623998303601)
          ·
            refine ⟨43444512792920717998727701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57926017057227623998303601 43444512792920717998727701)
            ·
              refine ⟨2036461537168158656190361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43444512792920717998727701 2036461537168158656190361)
              ·
                refine ⟨1527346152876118992142771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036461537168158656190361 1527346152876118992142771)
                ·
                  refine ⟨2291019229314178488214157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527346152876118992142771 2291019229314178488214157)
                  ·
                    refine ⟨859132210992816933080309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291019229314178488214157 859132210992816933080309)
                    ·
                      rfl

theorem cell22_2509731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 3].length) (baseStart_2509731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509731 prefixEnd_2509731 := by exact prefixLift 2509731
  have htrace : WordTrace (prefixWord ++ tailWord_2509731) baseStart_2509731 baseEnd_2509731 := by
    simpa [prefixWord, tailWord_2509731, baseEnd_2509731] using wordTrace_append hprefix tailTrace_2509731
  have hstable : (prefixWord ++ tailWord_2509731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509731).length < 2 ^ (prefixWord ++ tailWord_2509731).sum := by decide
  have hdescent : baseEnd_2509731 < baseStart_2509731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509774 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2509774 : Nat := 118140960795 + 2509774 * 2 ^ 59
def prefixEnd_2509774 : Nat := 4983230072969 + 3 ^ 40 * 2509774 * 2
def baseEnd_2509774 : Nat := 859146930771579154255177

theorem tailTrace_2509774 : CollatzResearch.WordTrace tailWord_2509774 prefixEnd_2509774 859146930771579154255177 := by
  unfold tailWord_2509774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442372251190613514864047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61025985339683272079274917 11442372251190613514864047)
  ·
    refine ⟨17163558376785920272296071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11442372251190613514864047 17163558376785920272296071)
    ·
      refine ⟨25745337565178880408444107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17163558376785920272296071 25745337565178880408444107)
      ·
        refine ⟨38618006347768320612666161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25745337565178880408444107 38618006347768320612666161)
        ·
          refine ⟨28963504760826240459499621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38618006347768320612666161 28963504760826240459499621)
          ·
            refine ⟨5430657142654920086156179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28963504760826240459499621 5430657142654920086156179)
            ·
              refine ⟨8145985713982380129234269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430657142654920086156179 8145985713982380129234269)
              ·
                refine ⟨3054744642743392548462851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8145985713982380129234269 3054744642743392548462851)
                ·
                  refine ⟨4582116964115088822694277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054744642743392548462851 4582116964115088822694277)
                  ·
                    refine ⟨859146930771579154255177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582116964115088822694277 859146930771579154255177)
                    ·
                      rfl

theorem cell22_2509774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2509774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509774 prefixEnd_2509774 := by exact prefixLift 2509774
  have htrace : WordTrace (prefixWord ++ tailWord_2509774) baseStart_2509774 baseEnd_2509774 := by
    simpa [prefixWord, tailWord_2509774, baseEnd_2509774] using wordTrace_append hprefix tailTrace_2509774
  have hstable : (prefixWord ++ tailWord_2509774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509774).length < 2 ^ (prefixWord ++ tailWord_2509774).sum := by decide
  have hdescent : baseEnd_2509774 < baseStart_2509774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509789 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2509789 : Nat := 118140960795 + 2509789 * 2 ^ 59
def prefixEnd_2509789 : Nat := 4983230072969 + 3 ^ 40 * 2509789 * 2
def baseEnd_2509789 : Nat := 286384021859374705043377

theorem tailTrace_2509789 : CollatzResearch.WordTrace tailWord_2509789 prefixEnd_2509789 286384021859374705043377 := by
  unfold tailWord_2509789
  simp only [CollatzResearch.WordTrace]
  refine ⟨91539525104470565680708421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61026350069647043787138947 91539525104470565680708421)
  ·
    refine ⟨17163660957088231065132829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91539525104470565680708421 17163660957088231065132829)
    ·
      refine ⟨6436372858908086649424811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17163660957088231065132829 6436372858908086649424811)
      ·
        refine ⟨9654559288362129974137217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6436372858908086649424811 9654559288362129974137217)
        ·
          refine ⟨7240919466271597480602913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9654559288362129974137217 7240919466271597480602913)
          ·
            refine ⟨5430689599703698110452185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240919466271597480602913 5430689599703698110452185)
            ·
              refine ⟨4073017199777773582839139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430689599703698110452185 4073017199777773582839139)
              ·
                refine ⟨6109525799666660374258709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073017199777773582839139 6109525799666660374258709)
                ·
                  refine ⟨286384021859374705043377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6109525799666660374258709 286384021859374705043377)
                  ·
                    rfl

theorem cell22_2509789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2509789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509789 prefixEnd_2509789 := by exact prefixLift 2509789
  have htrace : WordTrace (prefixWord ++ tailWord_2509789) baseStart_2509789 baseEnd_2509789 := by
    simpa [prefixWord, tailWord_2509789, baseEnd_2509789] using wordTrace_append hprefix tailTrace_2509789
  have hstable : (prefixWord ++ tailWord_2509789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509789).length < 2 ^ (prefixWord ++ tailWord_2509789).sum := by decide
  have hdescent : baseEnd_2509789 < baseStart_2509789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509802 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2509802 : Nat := 118140960795 + 2509802 * 2 ^ 59
def prefixEnd_2509802 : Nat := 4983230072969 + 3 ^ 40 * 2509802 * 2
def baseEnd_2509802 : Nat := 859156515743796414555091

theorem tailTrace_2509802 : CollatzResearch.WordTrace tailWord_2509802 prefixEnd_2509802 859156515743796414555091 := by
  unfold tailWord_2509802
  simp only [CollatzResearch.WordTrace]
  refine ⟨22884999813355867225232915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61026666168948979267287773 22884999813355867225232915)
  ·
    refine ⟨34327499720033800837849373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22884999813355867225232915 34327499720033800837849373)
    ·
      refine ⟨12872812395012675314193515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34327499720033800837849373 12872812395012675314193515)
      ·
        refine ⟨19309218592519012971290273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872812395012675314193515 19309218592519012971290273)
        ·
          refine ⟨14481913944389259728467705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19309218592519012971290273 14481913944389259728467705)
          ·
            refine ⟨10861435458291944796350779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14481913944389259728467705 10861435458291944796350779)
            ·
              refine ⟨16292153187437917194526169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10861435458291944796350779 16292153187437917194526169)
              ·
                refine ⟨12219114890578437895894627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16292153187437917194526169 12219114890578437895894627)
                ·
                  refine ⟨18328672335867656843841941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12219114890578437895894627 18328672335867656843841941)
                  ·
                    refine ⟨859156515743796414555091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18328672335867656843841941 859156515743796414555091)
                    ·
                      rfl

theorem cell22_2509802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2509802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509802 prefixEnd_2509802 := by exact prefixLift 2509802
  have htrace : WordTrace (prefixWord ++ tailWord_2509802) baseStart_2509802 baseEnd_2509802 := by
    simpa [prefixWord, tailWord_2509802, baseEnd_2509802] using wordTrace_append hprefix tailTrace_2509802
  have hstable : (prefixWord ++ tailWord_2509802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509802).length < 2 ^ (prefixWord ++ tailWord_2509802).sum := by decide
  have hdescent : baseEnd_2509802 < baseStart_2509802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509849 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_2509849 : Nat := 118140960795 + 2509849 * 2 ^ 59
def prefixEnd_2509849 : Nat := 4983230072969 + 3 ^ 40 * 2509849 * 2
def baseEnd_2509849 : Nat := 859172604804303958629947

theorem tailTrace_2509849 : CollatzResearch.WordTrace tailWord_2509849 prefixEnd_2509849 859172604804303958629947 := by
  unfold tailWord_2509849
  simp only [CollatzResearch.WordTrace]
  refine ⟨91541713484253195927892601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61027808989502130618595067 91541713484253195927892601)
  ·
    refine ⟨68656285113189896945919451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91541713484253195927892601 68656285113189896945919451)
    ·
      refine ⟨102984427669784845418879177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68656285113189896945919451 102984427669784845418879177)
      ·
        refine ⟨77238320752338634064159383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102984427669784845418879177 77238320752338634064159383)
        ·
          refine ⟨115857481128507951096239075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77238320752338634064159383 115857481128507951096239075)
          ·
            refine ⟨173786221692761926644358613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115857481128507951096239075 173786221692761926644358613)
            ·
              refine ⟨4073114570924107655727155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173786221692761926644358613 4073114570924107655727155)
              ·
                refine ⟨6109671856386161483590733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073114570924107655727155 6109671856386161483590733)
                ·
                  refine ⟨2291126946144810556346525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6109671856386161483590733 2291126946144810556346525)
                  ·
                    refine ⟨859172604804303958629947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291126946144810556346525 859172604804303958629947)
                    ·
                      rfl

theorem cell22_2509849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_2509849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509849 prefixEnd_2509849 := by exact prefixLift 2509849
  have htrace : WordTrace (prefixWord ++ tailWord_2509849) baseStart_2509849 baseEnd_2509849 := by
    simpa [prefixWord, tailWord_2509849, baseEnd_2509849] using wordTrace_append hprefix tailTrace_2509849
  have hstable : (prefixWord ++ tailWord_2509849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509849).length < 2 ^ (prefixWord ++ tailWord_2509849).sum := by decide
  have hdescent : baseEnd_2509849 < baseStart_2509849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509877 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2509877 : Nat := 118140960795 + 2509877 * 2 ^ 59
def prefixEnd_2509877 : Nat := 4983230072969 + 3 ^ 40 * 2509877 * 2
def baseEnd_2509877 : Nat := 859182189776521218929861

theorem tailTrace_2509877 : CollatzResearch.WordTrace tailWord_2509877 prefixEnd_2509877 859182189776521218929861 := by
  unfold tailWord_2509877
  simp only [CollatzResearch.WordTrace]
  refine ⟨91542734728151756709911885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61028489818767837806607923 91542734728151756709911885)
  ·
    refine ⟨34328525523056908766216957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91542734728151756709911885 34328525523056908766216957)
    ·
      refine ⟨12873197071146340787331359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34328525523056908766216957 12873197071146340787331359)
      ·
        refine ⟨19309795606719511180997039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12873197071146340787331359 19309795606719511180997039)
        ·
          refine ⟨28964693410079266771495559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19309795606719511180997039 28964693410079266771495559)
          ·
            refine ⟨43447040115118900157243339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28964693410079266771495559 43447040115118900157243339)
            ·
              refine ⟨65170560172678350235865009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43447040115118900157243339 65170560172678350235865009)
              ·
                refine ⟨48877920129508762676898757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65170560172678350235865009 48877920129508762676898757)
                ·
                  refine ⟨9164610024282893001918517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48877920129508762676898757 9164610024282893001918517)
                  ·
                    refine ⟨859182189776521218929861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9164610024282893001918517 859182189776521218929861)
                    ·
                      rfl

theorem cell22_2509877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2509877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509877 prefixEnd_2509877 := by exact prefixLift 2509877
  have htrace : WordTrace (prefixWord ++ tailWord_2509877) baseStart_2509877 baseEnd_2509877 := by
    simpa [prefixWord, tailWord_2509877, baseEnd_2509877] using wordTrace_append hprefix tailTrace_2509877
  have hstable : (prefixWord ++ tailWord_2509877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509877).length < 2 ^ (prefixWord ++ tailWord_2509877).sum := by decide
  have hdescent : baseEnd_2509877 < baseStart_2509877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509956 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_2509956 : Nat := 118140960795 + 2509956 * 2 ^ 59
def prefixEnd_2509956 : Nat := 4983230072969 + 3 ^ 40 * 2509956 * 2
def baseEnd_2509956 : Nat := 859209233090991346204619

theorem tailTrace_2509956 : CollatzResearch.WordTrace tailWord_2509956 prefixEnd_2509956 859209233090991346204619 := by
  unfold tailWord_2509956
  simp only [CollatzResearch.WordTrace]
  refine ⟨45772808047432776601018861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61030410729910368801358481 45772808047432776601018861)
  ·
    refine ⟨17164803017787291225382073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45772808047432776601018861 17164803017787291225382073)
    ·
      refine ⟨12873602263340468419036555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17164803017787291225382073 12873602263340468419036555)
      ·
        refine ⟨19310403395010702628554833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12873602263340468419036555 19310403395010702628554833)
        ·
          refine ⟨14482802546258026971416125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19310403395010702628554833 14482802546258026971416125)
          ·
            refine ⟨5431050954846760114281047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14482802546258026971416125 5431050954846760114281047)
            ·
              refine ⟨8146576432270140171421571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431050954846760114281047 8146576432270140171421571)
              ·
                refine ⟨12219864648405210257132357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8146576432270140171421571 12219864648405210257132357)
                ·
                  refine ⟨2291224621575976923212317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12219864648405210257132357 2291224621575976923212317)
                  ·
                    refine ⟨859209233090991346204619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291224621575976923212317 859209233090991346204619)
                    ·
                      rfl

theorem cell22_2509956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_2509956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509956 prefixEnd_2509956 := by exact prefixLift 2509956
  have htrace : WordTrace (prefixWord ++ tailWord_2509956) baseStart_2509956 baseEnd_2509956 := by
    simpa [prefixWord, tailWord_2509956, baseEnd_2509956] using wordTrace_append hprefix tailTrace_2509956
  have hstable : (prefixWord ++ tailWord_2509956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509956).length < 2 ^ (prefixWord ++ tailWord_2509956).sum := by decide
  have hdescent : baseEnd_2509956 < baseStart_2509956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509986 : List Nat := [3, 3, 1, 3, 2, 1, 1, 8]
def baseStart_2509986 : Nat := 118140960795 + 2509986 * 2 ^ 59
def prefixEnd_2509986 : Nat := 4983230072969 + 3 ^ 40 * 2509986 * 2
def baseEnd_2509986 : Nat := 95468833633786807550503

theorem tailTrace_2509986 : CollatzResearch.WordTrace tailWord_2509986 prefixEnd_2509986 95468833633786807550503 := by
  unfold tailWord_2509986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22886677571189217081407453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61031140189837912217086541 22886677571189217081407453)
  ·
    refine ⟨8582504089195956405527795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22886677571189217081407453 8582504089195956405527795)
    ·
      refine ⟨12873756133793934608291693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582504089195956405527795 12873756133793934608291693)
      ·
        refine ⟨4827658550172725478109385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12873756133793934608291693 4827658550172725478109385)
        ·
          refine ⟨3620743912629544108582039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4827658550172725478109385 3620743912629544108582039)
          ·
            refine ⟨5431115868944316162873059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620743912629544108582039 5431115868944316162873059)
            ·
              refine ⟨8146673803416474244309589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431115868944316162873059 8146673803416474244309589)
              ·
                refine ⟨95468833633786807550503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8146673803416474244309589 95468833633786807550503)
                ·
                  rfl

theorem cell22_2509986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_2509986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2509986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2509986 prefixEnd_2509986 := by exact prefixLift 2509986
  have htrace : WordTrace (prefixWord ++ tailWord_2509986) baseStart_2509986 baseEnd_2509986 := by
    simpa [prefixWord, tailWord_2509986, baseEnd_2509986] using wordTrace_append hprefix tailTrace_2509986
  have hstable : (prefixWord ++ tailWord_2509986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509986).length < 2 ^ (prefixWord ++ tailWord_2509986).sum := by decide
  have hdescent : baseEnd_2509986 < baseStart_2509986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510074 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_2510074 : Nat := 118140960795 + 2510074 * 2 ^ 59
def prefixEnd_2510074 : Nat := 4983230072969 + 3 ^ 40 * 2510074 * 2
def baseEnd_2510074 : Nat := 859249626902478371754257

theorem tailTrace_2510074 : CollatzResearch.WordTrace tailWord_2510074 prefixEnd_2510074 859249626902478371754257 := by
  unfold tailWord_2510074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22887479977109514838708319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61033279938958706236555517 22887479977109514838708319)
  ·
    refine ⟨34331219965664272258062479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22887479977109514838708319 34331219965664272258062479)
    ·
      refine ⟨51496829948496408387093719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34331219965664272258062479 51496829948496408387093719)
      ·
        refine ⟨77245244922744612580640579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51496829948496408387093719 77245244922744612580640579)
        ·
          refine ⟨115867867384116918870960869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77245244922744612580640579 115867867384116918870960869)
          ·
            refine ⟨21725225134521922288305163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115867867384116918870960869 21725225134521922288305163)
            ·
              refine ⟨32587837701782883432457745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21725225134521922288305163 32587837701782883432457745)
              ·
                refine ⟨24440878276337162574343309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32587837701782883432457745 24440878276337162574343309)
                ·
                  refine ⟨9165329353626435965378741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24440878276337162574343309 9165329353626435965378741)
                  ·
                    refine ⟨859249626902478371754257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9165329353626435965378741 859249626902478371754257)
                    ·
                      rfl

theorem cell22_2510074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_2510074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510074 prefixEnd_2510074 := by exact prefixLift 2510074
  have htrace : WordTrace (prefixWord ++ tailWord_2510074) baseStart_2510074 baseEnd_2510074 := by
    simpa [prefixWord, tailWord_2510074, baseEnd_2510074] using wordTrace_append hprefix tailTrace_2510074
  have hstable : (prefixWord ++ tailWord_2510074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510074).length < 2 ^ (prefixWord ++ tailWord_2510074).sum := by decide
  have hdescent : baseEnd_2510074 < baseStart_2510074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510089 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_2510089 : Nat := 118140960795 + 2510089 * 2 ^ 59
def prefixEnd_2510089 : Nat := 4983230072969 + 3 ^ 40 * 2510089 * 2
def baseEnd_2510089 : Nat := 859254761709023332629211

theorem tailTrace_2510089 : CollatzResearch.WordTrace tailWord_2510089 prefixEnd_2510089 859254761709023332629211 := by
  unfold tailWord_2510089
  simp only [CollatzResearch.WordTrace]
  refine ⟨91550467003383716916629321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61033644668922477944419547 91550467003383716916629321)
  ·
    refine ⟨68662850252537787687471991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91550467003383716916629321 68662850252537787687471991)
    ·
      refine ⟨102994275378806681531207987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68662850252537787687471991 102994275378806681531207987)
      ·
        refine ⟨154491413068210022296811981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102994275378806681531207987 154491413068210022296811981)
        ·
          refine ⟨57934279900578758361304493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154491413068210022296811981 57934279900578758361304493)
          ·
            refine ⟨21725354962717034385489185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57934279900578758361304493 21725354962717034385489185)
            ·
              refine ⟨16294016222037775789116889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21725354962717034385489185 16294016222037775789116889)
              ·
                refine ⟨12220512166528331841837667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16294016222037775789116889 12220512166528331841837667)
                ·
                  refine ⟨18330768249792497762756501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12220512166528331841837667 18330768249792497762756501)
                  ·
                    refine ⟨859254761709023332629211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18330768249792497762756501 859254761709023332629211)
                    ·
                      rfl

theorem cell22_2510089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_2510089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510089 prefixEnd_2510089 := by exact prefixLift 2510089
  have htrace : WordTrace (prefixWord ++ tailWord_2510089) baseStart_2510089 baseEnd_2510089 := by
    simpa [prefixWord, tailWord_2510089, baseEnd_2510089] using wordTrace_append hprefix tailTrace_2510089
  have hstable : (prefixWord ++ tailWord_2510089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510089).length < 2 ^ (prefixWord ++ tailWord_2510089).sum := by decide
  have hdescent : baseEnd_2510089 < baseStart_2510089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510091 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 1, 5]
def baseStart_2510091 : Nat := 118140960795 + 2510091 * 2 ^ 59
def prefixEnd_2510091 : Nat := 4983230072969 + 3 ^ 40 * 2510091 * 2
def baseEnd_2510091 : Nat := 859255446349895994079205

theorem tailTrace_2510091 : CollatzResearch.WordTrace tailWord_2510091 prefixEnd_2510091 859255446349895994079205 := by
  unfold tailWord_2510091
  simp only [CollatzResearch.WordTrace]
  refine ⟨91550539949376471258202127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61033693299584314172134751 91550539949376471258202127)
  ·
    refine ⟨137325809924064706887303191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91550539949376471258202127 137325809924064706887303191)
    ·
      refine ⟨205988714886097060330954787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137325809924064706887303191 205988714886097060330954787)
      ·
        refine ⟨308983072329145590496432181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205988714886097060330954787 308983072329145590496432181)
        ·
          refine ⟨28967163030857399109040517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308983072329145590496432181 28967163030857399109040517)
          ·
            refine ⟨5431343068285762332945097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28967163030857399109040517 5431343068285762332945097)
            ·
              refine ⟨4073507301214321749708823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5431343068285762332945097 4073507301214321749708823)
              ·
                refine ⟨6110260951821482624563235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073507301214321749708823 6110260951821482624563235)
                ·
                  refine ⟨9165391427732223936844853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6110260951821482624563235 9165391427732223936844853)
                  ·
                    refine ⟨859255446349895994079205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9165391427732223936844853 859255446349895994079205)
                    ·
                      rfl

theorem cell22_2510091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 5].length) (baseStart_2510091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510091 prefixEnd_2510091 := by exact prefixLift 2510091
  have htrace : WordTrace (prefixWord ++ tailWord_2510091) baseStart_2510091 baseEnd_2510091 := by
    simpa [prefixWord, tailWord_2510091, baseEnd_2510091] using wordTrace_append hprefix tailTrace_2510091
  have hstable : (prefixWord ++ tailWord_2510091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510091).length < 2 ^ (prefixWord ++ tailWord_2510091).sum := by decide
  have hdescent : baseEnd_2510091 < baseStart_2510091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510106 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_2510106 : Nat := 118140960795 + 2510106 * 2 ^ 59
def prefixEnd_2510106 : Nat := 4983230072969 + 3 ^ 40 * 2510106 * 2
def baseEnd_2510106 : Nat := 859260581156440954954159

theorem tailTrace_2510106 : CollatzResearch.WordTrace tailWord_2510106 prefixEnd_2510106 859260581156440954954159 := by
  unfold tailWord_2510106
  simp only [CollatzResearch.WordTrace]
  refine ⟨22887771761080532204999543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61034058029548085879998781 22887771761080532204999543)
  ·
    refine ⟨34331657641620798307499315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22887771761080532204999543 34331657641620798307499315)
    ·
      refine ⟨51497486462431197461248973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34331657641620798307499315 51497486462431197461248973)
      ·
        refine ⟨19311557423411699047968365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51497486462431197461248973 19311557423411699047968365)
        ·
          refine ⟨7241834033779387142988137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19311557423411699047968365 7241834033779387142988137)
          ·
            refine ⟨5431375525334540357241103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7241834033779387142988137 5431375525334540357241103)
            ·
              refine ⟨8147063288001810535861655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431375525334540357241103 8147063288001810535861655)
              ·
                refine ⟨12220594932002715803792483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8147063288001810535861655 12220594932002715803792483)
                ·
                  refine ⟨18330892398004073705688725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12220594932002715803792483 18330892398004073705688725)
                  ·
                    refine ⟨859260581156440954954159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18330892398004073705688725 859260581156440954954159)
                    ·
                      rfl

theorem cell22_2510106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_2510106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510106 prefixEnd_2510106 := by exact prefixLift 2510106
  have htrace : WordTrace (prefixWord ++ tailWord_2510106) baseStart_2510106 baseEnd_2510106 := by
    simpa [prefixWord, tailWord_2510106, baseEnd_2510106] using wordTrace_append hprefix tailTrace_2510106
  have hstable : (prefixWord ++ tailWord_2510106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510106).length < 2 ^ (prefixWord ++ tailWord_2510106).sum := by decide
  have hdescent : baseEnd_2510106 < baseStart_2510106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510112 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 1, 4]
def baseStart_2510112 : Nat := 118140960795 + 2510112 * 2 ^ 59
def prefixEnd_2510112 : Nat := 4983230072969 + 3 ^ 40 * 2510112 * 2
def baseEnd_2510112 : Nat := 859262635079058939304141

theorem tailTrace_2510112 : CollatzResearch.WordTrace tailWord_2510112 prefixEnd_2510112 859262635079058939304141 := by
  unfold tailWord_2510112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45775652941150195922358295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61034203921533594563144393 45775652941150195922358295)
  ·
    refine ⟨68663479411725293883537443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45775652941150195922358295 68663479411725293883537443)
    ·
      refine ⟨102995219117587940825306165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68663479411725293883537443 102995219117587940825306165)
      ·
        refine ⟨9655801792273869452372453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102995219117587940825306165 9655801792273869452372453)
        ·
          refine ⟨1810462836051350522319835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9655801792273869452372453 1810462836051350522319835)
          ·
            refine ⟨2715694254077025783479753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810462836051350522319835 2715694254077025783479753)
            ·
              refine ⟨2036770690557769337609815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715694254077025783479753 2036770690557769337609815)
              ·
                refine ⟨3055156035836654006414723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036770690557769337609815 3055156035836654006414723)
                ·
                  refine ⟨4582734053754981009622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055156035836654006414723 4582734053754981009622085)
                  ·
                    refine ⟨859262635079058939304141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582734053754981009622085 859262635079058939304141)
                    ·
                      rfl

theorem cell22_2510112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_2510112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510112 prefixEnd_2510112 := by exact prefixLift 2510112
  have htrace : WordTrace (prefixWord ++ tailWord_2510112) baseStart_2510112 baseEnd_2510112 := by
    simpa [prefixWord, tailWord_2510112, baseEnd_2510112] using wordTrace_append hprefix tailTrace_2510112
  have hstable : (prefixWord ++ tailWord_2510112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510112).length < 2 ^ (prefixWord ++ tailWord_2510112).sum := by decide
  have hdescent : baseEnd_2510112 < baseStart_2510112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510125 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2510125 : Nat := 118140960795 + 2510125 * 2 ^ 59
def prefixEnd_2510125 : Nat := 4983230072969 + 3 ^ 40 * 2510125 * 2
def baseEnd_2510125 : Nat := 859267085244731238729101

theorem tailTrace_2510125 : CollatzResearch.WordTrace tailWord_2510125 prefixEnd_2510125 859267085244731238729101 := by
  unfold tailWord_2510125
  simp only [CollatzResearch.WordTrace]
  refine ⟨91551780031253295064939829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61034520020835530043293219 91551780031253295064939829)
  ·
    refine ⟨8582979377929996412338109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91551780031253295064939829 8582979377929996412338109)
    ·
      refine ⟨3218617266723748654626791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8582979377929996412338109 3218617266723748654626791)
      ·
        refine ⟨4827925900085622981940187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218617266723748654626791 4827925900085622981940187)
        ·
          refine ⟨7241888850128434472910281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827925900085622981940187 7241888850128434472910281)
          ·
            refine ⟨5431416637596325854682711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7241888850128434472910281 5431416637596325854682711)
            ·
              refine ⟨8147124956394488782024067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431416637596325854682711 8147124956394488782024067)
              ·
                refine ⟨12220687434591733173036101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8147124956394488782024067 12220687434591733173036101)
                ·
                  refine ⟨2291378893985949969944269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12220687434591733173036101 2291378893985949969944269)
                  ·
                    refine ⟨859267085244731238729101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291378893985949969944269 859267085244731238729101)
                    ·
                      rfl

theorem cell22_2510125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2510125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510125 prefixEnd_2510125 := by exact prefixLift 2510125
  have htrace : WordTrace (prefixWord ++ tailWord_2510125) baseStart_2510125 baseEnd_2510125 := by
    simpa [prefixWord, tailWord_2510125, baseEnd_2510125] using wordTrace_append hprefix tailTrace_2510125
  have hstable : (prefixWord ++ tailWord_2510125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510125).length < 2 ^ (prefixWord ++ tailWord_2510125).sum := by decide
  have hdescent : baseEnd_2510125 < baseStart_2510125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510170 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_2510170 : Nat := 118140960795 + 2510170 * 2 ^ 59
def prefixEnd_2510170 : Nat := 4983230072969 + 3 ^ 40 * 2510170 * 2
def baseEnd_2510170 : Nat := 859282489664366121353963

theorem tailTrace_2510170 : CollatzResearch.WordTrace tailWord_2510170 prefixEnd_2510170 859282489664366121353963 := by
  unfold tailWord_2510170
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888355329022566937581991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61035614210726845166885309 22888355329022566937581991)
  ·
    refine ⟨34332532993533850406372987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888355329022566937581991 34332532993533850406372987)
    ·
      refine ⟨51498799490300775609559481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34332532993533850406372987 51498799490300775609559481)
      ·
        refine ⟨38624099617725581707169611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51498799490300775609559481 38624099617725581707169611)
        ·
          refine ⟨57936149426588372560754417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38624099617725581707169611 57936149426588372560754417)
          ·
            refine ⟨43452112069941279420565813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57936149426588372560754417 43452112069941279420565813)
            ·
              refine ⟨4073635506556994945678045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43452112069941279420565813 4073635506556994945678045)
              ·
                refine ⟨1527613314958873104629267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4073635506556994945678045 1527613314958873104629267)
                ·
                  refine ⟨2291419972438309656943901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527613314958873104629267 2291419972438309656943901)
                  ·
                    refine ⟨859282489664366121353963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291419972438309656943901 859282489664366121353963)
                    ·
                      rfl

theorem cell22_2510170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_2510170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510170 prefixEnd_2510170 := by exact prefixLift 2510170
  have htrace : WordTrace (prefixWord ++ tailWord_2510170) baseStart_2510170 baseEnd_2510170 := by
    simpa [prefixWord, tailWord_2510170, baseEnd_2510170] using wordTrace_append hprefix tailTrace_2510170
  have hstable : (prefixWord ++ tailWord_2510170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510170).length < 2 ^ (prefixWord ++ tailWord_2510170).sum := by decide
  have hdescent : baseEnd_2510170 < baseStart_2510170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510213 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_2510213 : Nat := 118140960795 + 2510213 * 2 ^ 59
def prefixEnd_2510213 : Nat := 4983230072969 + 3 ^ 40 * 2510213 * 2
def baseEnd_2510213 : Nat := 859297209443128342528831

theorem tailTrace_2510213 : CollatzResearch.WordTrace tailWord_2510213 prefixEnd_2510213 859297209443128342528831 := by
  unfold tailWord_2510213
  simp only [CollatzResearch.WordTrace]
  refine ⟨91554989654934486094143293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61036659769956324062762195 91554989654934486094143293)
  ·
    refine ⟨34333121120600432285303735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91554989654934486094143293 34333121120600432285303735)
    ·
      refine ⟨51499681680900648427955603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34333121120600432285303735 51499681680900648427955603)
      ·
        refine ⟨77249522521350972641933405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51499681680900648427955603 77249522521350972641933405)
        ·
          refine ⟨28968570945506614740725027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77249522521350972641933405 28968570945506614740725027)
          ·
            refine ⟨43452856418259922111087541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28968570945506614740725027 43452856418259922111087541)
            ·
              refine ⟨4073705289211867697914457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43452856418259922111087541 4073705289211867697914457)
              ·
                refine ⟨3055278966908900773435843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4073705289211867697914457 3055278966908900773435843)
                ·
                  refine ⟨4582918450363351160153765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055278966908900773435843 4582918450363351160153765)
                  ·
                    refine ⟨859297209443128342528831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582918450363351160153765 859297209443128342528831)
                    ·
                      rfl

theorem cell22_2510213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_2510213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510213 prefixEnd_2510213 := by exact prefixLift 2510213
  have htrace : WordTrace (prefixWord ++ tailWord_2510213) baseStart_2510213 baseEnd_2510213 := by
    simpa [prefixWord, tailWord_2510213, baseEnd_2510213] using wordTrace_append hprefix tailTrace_2510213
  have hstable : (prefixWord ++ tailWord_2510213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510213).length < 2 ^ (prefixWord ++ tailWord_2510213).sum := by decide
  have hdescent : baseEnd_2510213 < baseStart_2510213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510238 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2510238 : Nat := 118140960795 + 2510238 * 2 ^ 59
def prefixEnd_2510238 : Nat := 4983230072969 + 3 ^ 40 * 2510238 * 2
def baseEnd_2510238 : Nat := 859305767454036610653755

theorem tailTrace_2510238 : CollatzResearch.WordTrace tailWord_2510238 prefixEnd_2510238 859305767454036610653755 := by
  unfold tailWord_2510238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444487684980489420475421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61037267653229276909202245 11444487684980489420475421)
  ·
    refine ⟨4291682881867683532678283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11444487684980489420475421 4291682881867683532678283)
    ·
      refine ⟨6437524322801525299017425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4291682881867683532678283 6437524322801525299017425)
      ·
        refine ⟨4828143242101143974263069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6437524322801525299017425 4828143242101143974263069)
        ·
          refine ⟨1810553715787928990348651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4828143242101143974263069 1810553715787928990348651)
          ·
            refine ⟨2715830573681893485522977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810553715787928990348651 2715830573681893485522977)
            ·
              refine ⟨2036872930261420114142233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715830573681893485522977 2036872930261420114142233)
              ·
                refine ⟨1527654697696065085606675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036872930261420114142233 1527654697696065085606675)
                ·
                  refine ⟨2291482046544097628410013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527654697696065085606675 2291482046544097628410013)
                  ·
                    refine ⟨859305767454036610653755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291482046544097628410013 859305767454036610653755)
                    ·
                      rfl

theorem cell22_2510238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2510238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510238 prefixEnd_2510238 := by exact prefixLift 2510238
  have htrace : WordTrace (prefixWord ++ tailWord_2510238) baseStart_2510238 baseEnd_2510238 := by
    simpa [prefixWord, tailWord_2510238, baseEnd_2510238] using wordTrace_append hprefix tailTrace_2510238
  have hstable : (prefixWord ++ tailWord_2510238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510238).length < 2 ^ (prefixWord ++ tailWord_2510238).sum := by decide
  have hdescent : baseEnd_2510238 < baseStart_2510238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510294 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2510294 : Nat := 118140960795 + 2510294 * 2 ^ 59
def prefixEnd_2510294 : Nat := 4983230072969 + 3 ^ 40 * 2510294 * 2
def baseEnd_2510294 : Nat := 859324937398471131253583

theorem tailTrace_2510294 : CollatzResearch.WordTrace tailWord_2510294 prefixEnd_2510294 859324937398471131253583 := by
  unfold tailWord_2510294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722371497977564807990121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61038629311760691285227957 5722371497977564807990121)
  ·
    refine ⟨4291778623483173605992591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5722371497977564807990121 4291778623483173605992591)
    ·
      refine ⟨6437667935224760408988887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4291778623483173605992591 6437667935224760408988887)
      ·
        refine ⟨9656501902837140613483331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437667935224760408988887 9656501902837140613483331)
        ·
          refine ⟨14484752854255710920224997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9656501902837140613483331 14484752854255710920224997)
          ·
            refine ⟨2715891160172945797542187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14484752854255710920224997 2715891160172945797542187)
            ·
              refine ⟨4073836740259418696313281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715891160172945797542187 4073836740259418696313281)
              ·
                refine ⟨3055377555194564022234961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4073836740259418696313281 3055377555194564022234961)
                ·
                  refine ⟨2291533166395923016676221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055377555194564022234961 2291533166395923016676221)
                  ·
                    refine ⟨859324937398471131253583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291533166395923016676221 859324937398471131253583)
                    ·
                      rfl

theorem cell22_2510294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2510294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510294 prefixEnd_2510294 := by exact prefixLift 2510294
  have htrace : WordTrace (prefixWord ++ tailWord_2510294) baseStart_2510294 baseEnd_2510294 := by
    simpa [prefixWord, tailWord_2510294, baseEnd_2510294] using wordTrace_append hprefix tailTrace_2510294
  have hstable : (prefixWord ++ tailWord_2510294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510294).length < 2 ^ (prefixWord ++ tailWord_2510294).sum := by decide
  have hdescent : baseEnd_2510294 < baseStart_2510294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510305 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_2510305 : Nat := 118140960795 + 2510305 * 2 ^ 59
def prefixEnd_2510305 : Nat := 4983230072969 + 3 ^ 40 * 2510305 * 2
def baseEnd_2510305 : Nat := 859328702923270769228549

theorem tailTrace_2510305 : CollatzResearch.WordTrace tailWord_2510305 prefixEnd_2510305 859328702923270769228549 := by
  unfold tailWord_2510305
  simp only [CollatzResearch.WordTrace]
  refine ⟨91558345170601185806492369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61038896780400790537661579 91558345170601185806492369)
  ·
    refine ⟨68668758877950889354869277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91558345170601185806492369 68668758877950889354869277)
    ·
      refine ⟨25750784579231583508075979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68668758877950889354869277 25750784579231583508075979)
      ·
        refine ⟨38626176868847375262113969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25750784579231583508075979 38626176868847375262113969)
        ·
          refine ⟨28969632651635531446585477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38626176868847375262113969 28969632651635531446585477)
          ·
            refine ⟨5431806122181662146234777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28969632651635531446585477 5431806122181662146234777)
            ·
              refine ⟨4073854591636246609676083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5431806122181662146234777 4073854591636246609676083)
              ·
                refine ⟨6110781887454369914514125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073854591636246609676083 6110781887454369914514125)
                ·
                  refine ⟨2291543207795388717942797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6110781887454369914514125 2291543207795388717942797)
                  ·
                    refine ⟨859328702923270769228549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291543207795388717942797 859328702923270769228549)
                    ·
                      rfl

theorem cell22_2510305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_2510305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510305 prefixEnd_2510305 := by exact prefixLift 2510305
  have htrace : WordTrace (prefixWord ++ tailWord_2510305) baseStart_2510305 baseEnd_2510305 := by
    simpa [prefixWord, tailWord_2510305, baseEnd_2510305] using wordTrace_append hprefix tailTrace_2510305
  have hstable : (prefixWord ++ tailWord_2510305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510305).length < 2 ^ (prefixWord ++ tailWord_2510305).sum := by decide
  have hdescent : baseEnd_2510305 < baseStart_2510305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510316 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2510316 : Nat := 118140960795 + 2510316 * 2 ^ 59
def prefixEnd_2510316 : Nat := 4983230072969 + 3 ^ 40 * 2510316 * 2
def baseEnd_2510316 : Nat := 859332468448070407203515

theorem tailTrace_2510316 : CollatzResearch.WordTrace tailWord_2510316 prefixEnd_2510316 859332468448070407203515 := by
  unfold tailWord_2510316
  simp only [CollatzResearch.WordTrace]
  refine ⟨45779373186780667342571401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61039164249040889790095201 45779373186780667342571401)
  ·
    refine ⟨34334529890085500506928551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45779373186780667342571401 34334529890085500506928551)
    ·
      refine ⟨51501794835128250760392827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34334529890085500506928551 51501794835128250760392827)
      ·
        refine ⟨77252692252692376140589241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51501794835128250760392827 77252692252692376140589241)
        ·
          refine ⟨57939519189519282105441931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77252692252692376140589241 57939519189519282105441931)
          ·
            refine ⟨86909278784278923158162897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57939519189519282105441931 86909278784278923158162897)
            ·
              refine ⟨65181959088209192368622173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86909278784278923158162897 65181959088209192368622173)
              ·
                refine ⟨24443234658078447138233315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65181959088209192368622173 24443234658078447138233315)
                ·
                  refine ⟨36664851987117670707349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24443234658078447138233315 36664851987117670707349973)
                  ·
                    refine ⟨859332468448070407203515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36664851987117670707349973 859332468448070407203515)
                    ·
                      rfl

theorem cell22_2510316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2510316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510316 prefixEnd_2510316 := by exact prefixLift 2510316
  have htrace : WordTrace (prefixWord ++ tailWord_2510316) baseStart_2510316 baseEnd_2510316 := by
    simpa [prefixWord, tailWord_2510316, baseEnd_2510316] using wordTrace_append hprefix tailTrace_2510316
  have hstable : (prefixWord ++ tailWord_2510316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510316).length < 2 ^ (prefixWord ++ tailWord_2510316).sum := by decide
  have hdescent : baseEnd_2510316 < baseStart_2510316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510356 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2510356 : Nat := 118140960795 + 2510356 * 2 ^ 59
def prefixEnd_2510356 : Nat := 4983230072969 + 3 ^ 40 * 2510356 * 2
def baseEnd_2510356 : Nat := 859346161265523636203393

theorem tailTrace_2510356 : CollatzResearch.WordTrace tailWord_2510356 prefixEnd_2510356 859346161265523636203393 := by
  unfold tailWord_2510356
  simp only [CollatzResearch.WordTrace]
  refine ⟨45780102646708210758299461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61040136862277614344399281 45780102646708210758299461)
  ·
    refine ⟨8583769246257789517181149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45780102646708210758299461 8583769246257789517181149)
    ·
      refine ⟨3218913467346671068942931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8583769246257789517181149 3218913467346671068942931)
      ·
        refine ⟨4828370201020006603414397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218913467346671068942931 4828370201020006603414397)
        ·
          refine ⟨1810638825382502476280399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4828370201020006603414397 1810638825382502476280399)
          ·
            refine ⟨2715958238073753714420599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810638825382502476280399 2715958238073753714420599)
            ·
              refine ⟨4073937357110630571630899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715958238073753714420599 4073937357110630571630899)
              ·
                refine ⟨6110906035665945857446349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073937357110630571630899 6110906035665945857446349)
                ·
                  refine ⟨2291589763374729696542381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6110906035665945857446349 2291589763374729696542381)
                  ·
                    refine ⟨859346161265523636203393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291589763374729696542381 859346161265523636203393)
                    ·
                      rfl

theorem cell22_2510356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2510356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510356 prefixEnd_2510356 := by exact prefixLift 2510356
  have htrace : WordTrace (prefixWord ++ tailWord_2510356) baseStart_2510356 baseEnd_2510356 := by
    simpa [prefixWord, tailWord_2510356, baseEnd_2510356] using wordTrace_append hprefix tailTrace_2510356
  have hstable : (prefixWord ++ tailWord_2510356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510356).length < 2 ^ (prefixWord ++ tailWord_2510356).sum := by decide
  have hdescent : baseEnd_2510356 < baseStart_2510356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510361 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_2510361 : Nat := 118140960795 + 2510361 * 2 ^ 59
def prefixEnd_2510361 : Nat := 4983230072969 + 3 ^ 40 * 2510361 * 2
def baseEnd_2510361 : Nat := 859347872867705289828377

theorem tailTrace_2510361 : CollatzResearch.WordTrace tailWord_2510361 prefixEnd_2510361 859347872867705289828377 := by
  unfold tailWord_2510361
  simp only [CollatzResearch.WordTrace]
  refine ⟨91560387658398307370530937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61040258438932204913687291 91560387658398307370530937)
  ·
    refine ⟨68670290743798730527898203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91560387658398307370530937 68670290743798730527898203)
    ·
      refine ⟨103005436115698095791847305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68670290743798730527898203 103005436115698095791847305)
      ·
        refine ⟨77254077086773571843885479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103005436115698095791847305 77254077086773571843885479)
        ·
          refine ⟨115881115630160357765828219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77254077086773571843885479 115881115630160357765828219)
          ·
            refine ⟨173821673445240536648742329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115881115630160357765828219 173821673445240536648742329)
            ·
              refine ⟨130366255083930402486556747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173821673445240536648742329 130366255083930402486556747)
              ·
                refine ⟨195549382625895603729835121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130366255083930402486556747 195549382625895603729835121)
                ·
                  refine ⟨146662036969421702797376341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195549382625895603729835121 146662036969421702797376341)
                  ·
                    refine ⟨859347872867705289828377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146662036969421702797376341 859347872867705289828377)
                    ·
                      rfl

theorem cell22_2510361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_2510361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510361 prefixEnd_2510361 := by exact prefixLift 2510361
  have htrace : WordTrace (prefixWord ++ tailWord_2510361) baseStart_2510361 baseEnd_2510361 := by
    simpa [prefixWord, tailWord_2510361, baseEnd_2510361] using wordTrace_append hprefix tailTrace_2510361
  have hstable : (prefixWord ++ tailWord_2510361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510361).length < 2 ^ (prefixWord ++ tailWord_2510361).sum := by decide
  have hdescent : baseEnd_2510361 < baseStart_2510361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510382 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2510382 : Nat := 118140960795 + 2510382 * 2 ^ 59
def prefixEnd_2510382 : Nat := 4983230072969 + 3 ^ 40 * 2510382 * 2
def baseEnd_2510382 : Nat := 859355061596868235053313

theorem tailTrace_2510382 : CollatzResearch.WordTrace tailWord_2510382 prefixEnd_2510382 859355061596868235053313 := by
  unfold tailWord_2510382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445144198915278494630675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61040769060881485304696933 11445144198915278494630675)
  ·
    refine ⟨17167716298372917741946013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11445144198915278494630675 17167716298372917741946013)
    ·
      refine ⟨6437893611889844153229755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17167716298372917741946013 6437893611889844153229755)
      ·
        refine ⟨9656840417834766229844633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437893611889844153229755 9656840417834766229844633)
        ·
          refine ⟨7242630313376074672383475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9656840417834766229844633 7242630313376074672383475)
          ·
            refine ⟨10863945470064112008575213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242630313376074672383475 10863945470064112008575213)
            ·
              refine ⟨4073979551274042003215705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10863945470064112008575213 4073979551274042003215705)
              ·
                refine ⟨3055484663455531502411779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4073979551274042003215705 3055484663455531502411779)
                ·
                  refine ⟨4583226995183297253617669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055484663455531502411779 4583226995183297253617669)
                  ·
                    refine ⟨859355061596868235053313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4583226995183297253617669 859355061596868235053313)
                    ·
                      rfl

theorem cell22_2510382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2510382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510382 prefixEnd_2510382 := by exact prefixLift 2510382
  have htrace : WordTrace (prefixWord ++ tailWord_2510382) baseStart_2510382 baseEnd_2510382 := by
    simpa [prefixWord, tailWord_2510382, baseEnd_2510382] using wordTrace_append hprefix tailTrace_2510382
  have hstable : (prefixWord ++ tailWord_2510382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510382).length < 2 ^ (prefixWord ++ tailWord_2510382).sum := by decide
  have hdescent : baseEnd_2510382 < baseStart_2510382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510412 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_2510412 : Nat := 118140960795 + 2510412 * 2 ^ 59
def prefixEnd_2510412 : Nat := 4983230072969 + 3 ^ 40 * 2510412 * 2
def baseEnd_2510412 : Nat := 859365331209958156803221

theorem tailTrace_2510412 : CollatzResearch.WordTrace tailWord_2510412 prefixEnd_2510412 859365331209958156803221 := by
  unfold tailWord_2510412
  simp only [CollatzResearch.WordTrace]
  refine ⟨45781123890606771540318745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61041498520809028720424993 45781123890606771540318745)
  ·
    refine ⟨34335842917955078655239059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45781123890606771540318745 34335842917955078655239059)
    ·
      refine ⟨51503764376932617982858589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34335842917955078655239059 51503764376932617982858589)
      ·
        refine ⟨19313911641349731743571971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51503764376932617982858589 19313911641349731743571971)
        ·
          refine ⟨28970867462024597615357957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19313911641349731743571971 28970867462024597615357957)
          ·
            refine ⟨5432037649129612052879617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28970867462024597615357957 5432037649129612052879617)
            ·
              refine ⟨4074028236847209039659713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5432037649129612052879617 4074028236847209039659713)
              ·
                refine ⟨3055521177635406779744785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074028236847209039659713 3055521177635406779744785)
                ·
                  refine ⟨2291640883226555084808589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055521177635406779744785 2291640883226555084808589)
                  ·
                    refine ⟨859365331209958156803221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291640883226555084808589 859365331209958156803221)
                    ·
                      rfl

theorem cell22_2510412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_2510412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510412 prefixEnd_2510412 := by exact prefixLift 2510412
  have htrace : WordTrace (prefixWord ++ tailWord_2510412) baseStart_2510412 baseEnd_2510412 := by
    simpa [prefixWord, tailWord_2510412, baseEnd_2510412] using wordTrace_append hprefix tailTrace_2510412
  have hstable : (prefixWord ++ tailWord_2510412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510412).length < 2 ^ (prefixWord ++ tailWord_2510412).sum := by decide
  have hdescent : baseEnd_2510412 < baseStart_2510412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510429 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2510429 : Nat := 118140960795 + 2510429 * 2 ^ 59
def prefixEnd_2510429 : Nat := 4983230072969 + 3 ^ 40 * 2510429 * 2
def baseEnd_2510429 : Nat := 859371150657375779128169

theorem tailTrace_2510429 : CollatzResearch.WordTrace tailWord_2510429 prefixEnd_2510429 859371150657375779128169 := by
  unfold tailWord_2510429
  simp only [CollatzResearch.WordTrace]
  refine ⟨91562867822151954984006341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61041911881434636656004227 91562867822151954984006341)
  ·
    refine ⟨17168037716653491559501189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91562867822151954984006341 17168037716653491559501189)
    ·
      refine ⟨3219007071872529667406473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17168037716653491559501189 3219007071872529667406473)
      ·
        refine ⟨2414255303904397250554855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3219007071872529667406473 2414255303904397250554855)
        ·
          refine ⟨3621382955856595875832283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414255303904397250554855 3621382955856595875832283)
          ·
            refine ⟨5432074433784893813748425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621382955856595875832283 5432074433784893813748425)
            ·
              refine ⟨4074055825338670360311319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5432074433784893813748425 4074055825338670360311319)
              ·
                refine ⟨6111083738008005540466979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074055825338670360311319 6111083738008005540466979)
                ·
                  refine ⟨9166625607012008310700469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6111083738008005540466979 9166625607012008310700469)
                  ·
                    refine ⟨859371150657375779128169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9166625607012008310700469 859371150657375779128169)
                    ·
                      rfl

theorem cell22_2510429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2510429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510429 prefixEnd_2510429 := by exact prefixLift 2510429
  have htrace : WordTrace (prefixWord ++ tailWord_2510429) baseStart_2510429 baseEnd_2510429 := by
    simpa [prefixWord, tailWord_2510429, baseEnd_2510429] using wordTrace_append hprefix tailTrace_2510429
  have hstable : (prefixWord ++ tailWord_2510429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510429).length < 2 ^ (prefixWord ++ tailWord_2510429).sum := by decide
  have hdescent : baseEnd_2510429 < baseStart_2510429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510474 : List Nat := [3, 1, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_2510474 : Nat := 118140960795 + 2510474 * 2 ^ 59
def prefixEnd_2510474 : Nat := 4983230072969 + 3 ^ 40 * 2510474 * 2
def baseEnd_2510474 : Nat := 859386555077010661753031

theorem tailTrace_2510474 : CollatzResearch.WordTrace tailWord_2510474 prefixEnd_2510474 859386555077010661753031 := by
  unfold tailWord_2510474
  simp only [CollatzResearch.WordTrace]
  refine ⟨22891127276747231917348619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61043006071325951779596317 22891127276747231917348619)
  ·
    refine ⟨34336690915120847876022929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22891127276747231917348619 34336690915120847876022929)
    ·
      refine ⟨25752518186340635907017197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34336690915120847876022929 25752518186340635907017197)
      ·
        refine ⟨9657194319877738465131449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25752518186340635907017197 9657194319877738465131449)
        ·
          refine ⟨7242895739908303848848587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9657194319877738465131449 7242895739908303848848587)
          ·
            refine ⟨10864343609862455773272881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242895739908303848848587 10864343609862455773272881)
            ·
              refine ⟨8148257707396841829954661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10864343609862455773272881 8148257707396841829954661)
              ·
                refine ⟨1527798320136907843116499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8148257707396841829954661 1527798320136907843116499)
                ·
                  refine ⟨2291697480205361764674749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527798320136907843116499 2291697480205361764674749)
                  ·
                    refine ⟨859386555077010661753031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291697480205361764674749 859386555077010661753031)
                    ·
                      rfl

theorem cell22_2510474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_2510474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510474 prefixEnd_2510474 := by exact prefixLift 2510474
  have htrace : WordTrace (prefixWord ++ tailWord_2510474) baseStart_2510474 baseEnd_2510474 := by
    simpa [prefixWord, tailWord_2510474, baseEnd_2510474] using wordTrace_append hprefix tailTrace_2510474
  have hstable : (prefixWord ++ tailWord_2510474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510474).length < 2 ^ (prefixWord ++ tailWord_2510474).sum := by decide
  have hdescent : baseEnd_2510474 < baseStart_2510474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510487 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 5]
def baseStart_2510487 : Nat := 118140960795 + 2510487 * 2 ^ 59
def prefixEnd_2510487 : Nat := 4983230072969 + 3 ^ 40 * 2510487 * 2
def baseEnd_2510487 : Nat := 286463668414227653725997

theorem tailTrace_2510487 : CollatzResearch.WordTrace tailWord_2510487 prefixEnd_2510487 286463668414227653725997 := by
  unfold tailWord_2510487
  simp only [CollatzResearch.WordTrace]
  refine ⟨91564983255941830889617715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61043322170627887259745143 91564983255941830889617715)
  ·
    refine ⟨137347474883912746334426573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91564983255941830889617715 137347474883912746334426573)
    ·
      refine ⟨51505303081467279875409965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137347474883912746334426573 51505303081467279875409965)
      ·
        refine ⟨19314488655550229953278737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51505303081467279875409965 19314488655550229953278737)
        ·
          refine ⟨14485866491662672464959053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19314488655550229953278737 14485866491662672464959053)
          ·
            refine ⟨5432199934373502174359645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14485866491662672464959053 5432199934373502174359645)
            ·
              refine ⟨2037074975390063315384867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5432199934373502174359645 2037074975390063315384867)
              ·
                refine ⟨3055612463085094973077301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037074975390063315384867 3055612463085094973077301)
                ·
                  refine ⟨286463668414227653725997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3055612463085094973077301 286463668414227653725997)
                  ·
                    rfl

theorem cell22_2510487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 5].length) (baseStart_2510487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510487 prefixEnd_2510487 := by exact prefixLift 2510487
  have htrace : WordTrace (prefixWord ++ tailWord_2510487) baseStart_2510487 baseEnd_2510487 := by
    simpa [prefixWord, tailWord_2510487, baseEnd_2510487] using wordTrace_append hprefix tailTrace_2510487
  have hstable : (prefixWord ++ tailWord_2510487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510487).length < 2 ^ (prefixWord ++ tailWord_2510487).sum := by decide
  have hdescent : baseEnd_2510487 < baseStart_2510487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510620 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2510620 : Nat := 118140960795 + 2510620 * 2 ^ 59
def prefixEnd_2510620 : Nat := 4983230072969 + 3 ^ 40 * 2510620 * 2
def baseEnd_2510620 : Nat := 859436533860714947602583

theorem tailTrace_2510620 : CollatzResearch.WordTrace tailWord_2510620 prefixEnd_2510620 859436533860714947602583 := by
  unfold tailWord_2510620
  simp only [CollatzResearch.WordTrace]
  refine ⟨45784917082229997302104657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61046556109639996402806209 45784917082229997302104657)
  ·
    refine ⟨34338687811672497976578493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45784917082229997302104657 34338687811672497976578493)
    ·
      refine ⟨12877007929377186741216935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34338687811672497976578493 12877007929377186741216935)
      ·
        refine ⟨19315511894065780111825403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12877007929377186741216935 19315511894065780111825403)
        ·
          refine ⟨28973267841098670167738105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19315511894065780111825403 28973267841098670167738105)
          ·
            refine ⟨21729950880824002625803579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28973267841098670167738105 21729950880824002625803579)
            ·
              refine ⟨32594926321236003938705369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21729950880824002625803579 32594926321236003938705369)
              ·
                refine ⟨24446194740927002954029027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32594926321236003938705369 24446194740927002954029027)
                ·
                  refine ⟨36669292111390504431043541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24446194740927002954029027 36669292111390504431043541)
                  ·
                    refine ⟨859436533860714947602583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36669292111390504431043541 859436533860714947602583)
                    ·
                      rfl

theorem cell22_2510620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2510620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510620 prefixEnd_2510620 := by exact prefixLift 2510620
  have htrace : WordTrace (prefixWord ++ tailWord_2510620) baseStart_2510620 baseEnd_2510620 := by
    simpa [prefixWord, tailWord_2510620, baseEnd_2510620] using wordTrace_append hprefix tailTrace_2510620
  have hstable : (prefixWord ++ tailWord_2510620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510620).length < 2 ^ (prefixWord ++ tailWord_2510620).sum := by decide
  have hdescent : baseEnd_2510620 < baseStart_2510620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510626 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2510626 : Nat := 118140960795 + 2510626 * 2 ^ 59
def prefixEnd_2510626 : Nat := 4983230072969 + 3 ^ 40 * 2510626 * 2
def baseEnd_2510626 : Nat := 859438587783332931952565

theorem tailTrace_2510626 : CollatzResearch.WordTrace tailWord_2510626 prefixEnd_2510626 859438587783332931952565 := by
  unfold tailWord_2510626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22892513250609564407231933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61046702001625505085951821 22892513250609564407231933)
  ·
    refine ⟨8584692468978586652711975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22892513250609564407231933 8584692468978586652711975)
    ·
      refine ⟨12877038703467879979067963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8584692468978586652711975 12877038703467879979067963)
      ·
        refine ⟨19315558055201819968601945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12877038703467879979067963 19315558055201819968601945)
        ·
          refine ⟨14486668541401364976451459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19315558055201819968601945 14486668541401364976451459)
          ·
            refine ⟨21730002812102047464677189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14486668541401364976451459 21730002812102047464677189)
            ·
              refine ⟨4074375527269133899626973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21730002812102047464677189 4074375527269133899626973)
              ·
                refine ⟨1527890822725925212360115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4074375527269133899626973 1527890822725925212360115)
                ·
                  refine ⟨2291836234088887818540173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527890822725925212360115 2291836234088887818540173)
                  ·
                    refine ⟨859438587783332931952565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291836234088887818540173 859438587783332931952565)
                    ·
                      rfl

theorem cell22_2510626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2510626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510626 prefixEnd_2510626 := by exact prefixLift 2510626
  have htrace : WordTrace (prefixWord ++ tailWord_2510626) baseStart_2510626 baseEnd_2510626 := by
    simpa [prefixWord, tailWord_2510626, baseEnd_2510626] using wordTrace_append hprefix tailTrace_2510626
  have hstable : (prefixWord ++ tailWord_2510626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510626).length < 2 ^ (prefixWord ++ tailWord_2510626).sum := by decide
  have hdescent : baseEnd_2510626 < baseStart_2510626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510682 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_2510682 : Nat := 118140960795 + 2510682 * 2 ^ 59
def prefixEnd_2510682 : Nat := 4983230072969 + 3 ^ 40 * 2510682 * 2
def baseEnd_2510682 : Nat := 859457757727767452552393

theorem tailTrace_2510682 : CollatzResearch.WordTrace tailWord_2510682 prefixEnd_2510682 859457757727767452552393 := by
  unfold tailWord_2510682
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893023872558844798241575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61048063660156919461977533 22893023872558844798241575)
  ·
    refine ⟨34339535808838267197362363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22893023872558844798241575 34339535808838267197362363)
    ·
      refine ⟨51509303713257400796043545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34339535808838267197362363 51509303713257400796043545)
      ·
        refine ⟨38631977784943050597032659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51509303713257400796043545 38631977784943050597032659)
        ·
          refine ⟨57947966677414575895548989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38631977784943050597032659 57947966677414575895548989)
          ·
            refine ⟨21730487504030465960830871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57947966677414575895548989 21730487504030465960830871)
            ·
              refine ⟨32595731256045698941246307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21730487504030465960830871 32595731256045698941246307)
              ·
                refine ⟨48893596884068548411869461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32595731256045698941246307 48893596884068548411869461)
                ·
                  refine ⟨2291887353940713206806381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48893596884068548411869461 2291887353940713206806381)
                  ·
                    refine ⟨859457757727767452552393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291887353940713206806381 859457757727767452552393)
                    ·
                      rfl

theorem cell22_2510682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_2510682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510682 prefixEnd_2510682 := by exact prefixLift 2510682
  have htrace : WordTrace (prefixWord ++ tailWord_2510682) baseStart_2510682 baseEnd_2510682 := by
    simpa [prefixWord, tailWord_2510682, baseEnd_2510682] using wordTrace_append hprefix tailTrace_2510682
  have hstable : (prefixWord ++ tailWord_2510682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510682).length < 2 ^ (prefixWord ++ tailWord_2510682).sum := by decide
  have hdescent : baseEnd_2510682 < baseStart_2510682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510750 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2510750 : Nat := 118140960795 + 2510750 * 2 ^ 59
def prefixEnd_2510750 : Nat := 4983230072969 + 3 ^ 40 * 2510750 * 2
def baseEnd_2510750 : Nat := 859481035517437941852185

theorem tailTrace_2510750 : CollatzResearch.WordTrace tailWord_2510750 prefixEnd_2510750 859481035517437941852185 := by
  unfold tailWord_2510750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11446821956748628350805213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61049717102659351204294469 11446821956748628350805213)
  ·
    refine ⟨4292558233780735631551955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11446821956748628350805213 4292558233780735631551955)
    ·
      refine ⟨6438837350671103447327933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4292558233780735631551955 6438837350671103447327933)
      ·
        refine ⟨2414564006501663792747975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6438837350671103447327933 2414564006501663792747975)
        ·
          refine ⟨3621846009752495689121963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414564006501663792747975 3621846009752495689121963)
          ·
            refine ⟨5432769014628743533682945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621846009752495689121963 5432769014628743533682945)
            ·
              refine ⟨4074576760971557650262209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5432769014628743533682945 4074576760971557650262209)
              ·
                refine ⟨3055932570728668237696657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074576760971557650262209 3055932570728668237696657)
                ·
                  refine ⟨2291949428046501178272493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055932570728668237696657 2291949428046501178272493)
                  ·
                    refine ⟨859481035517437941852185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291949428046501178272493 859481035517437941852185)
                    ·
                      rfl

theorem cell22_2510750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2510750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510750 prefixEnd_2510750 := by exact prefixLift 2510750
  have htrace : WordTrace (prefixWord ++ tailWord_2510750) baseStart_2510750 baseEnd_2510750 := by
    simpa [prefixWord, tailWord_2510750, baseEnd_2510750] using wordTrace_append hprefix tailTrace_2510750
  have hstable : (prefixWord ++ tailWord_2510750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510750).length < 2 ^ (prefixWord ++ tailWord_2510750).sum := by decide
  have hdescent : baseEnd_2510750 < baseStart_2510750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510817 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_2510817 : Nat := 118140960795 + 2510817 * 2 ^ 59
def prefixEnd_2510817 : Nat := 4983230072969 + 3 ^ 40 * 2510817 * 2
def baseEnd_2510817 : Nat := 859503970986672100426979

theorem tailTrace_2510817 : CollatzResearch.WordTrace tailWord_2510817 prefixEnd_2510817 859503970986672100426979 := by
  unfold tailWord_2510817
  simp only [CollatzResearch.WordTrace]
  refine ⟨91577019344746297249130705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61051346229830864832753803 91577019344746297249130705)
  ·
    refine ⟨68682764508559722936848029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91577019344746297249130705 68682764508559722936848029)
    ·
      refine ⟨25756036690709896101318011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68682764508559722936848029 25756036690709896101318011)
      ·
        refine ⟨38634055036064844151977017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25756036690709896101318011 38634055036064844151977017)
        ·
          refine ⟨28975541277048633113982763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38634055036064844151977017 28975541277048633113982763)
          ·
            refine ⟨43463311915572949670974145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28975541277048633113982763 43463311915572949670974145)
            ·
              refine ⟨32597483936679712253230609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43463311915572949670974145 32597483936679712253230609)
              ·
                refine ⟨24448112952509784189922957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32597483936679712253230609 24448112952509784189922957)
                ·
                  refine ⟨9168042357191169071221109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24448112952509784189922957 9168042357191169071221109)
                  ·
                    refine ⟨859503970986672100426979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9168042357191169071221109 859503970986672100426979)
                    ·
                      rfl

theorem cell22_2510817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_2510817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510817 prefixEnd_2510817 := by exact prefixLift 2510817
  have htrace : WordTrace (prefixWord ++ tailWord_2510817) baseStart_2510817 baseEnd_2510817 := by
    simpa [prefixWord, tailWord_2510817, baseEnd_2510817] using wordTrace_append hprefix tailTrace_2510817
  have hstable : (prefixWord ++ tailWord_2510817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510817).length < 2 ^ (prefixWord ++ tailWord_2510817).sum := by decide
  have hdescent : baseEnd_2510817 < baseStart_2510817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510819 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 6]
def baseStart_2510819 : Nat := 118140960795 + 2510819 * 2 ^ 59
def prefixEnd_2510819 : Nat := 4983230072969 + 3 ^ 40 * 2510819 * 2
def baseEnd_2510819 : Nat := 286501551875848253958991

theorem tailTrace_2510819 : CollatzResearch.WordTrace tailWord_2510819 prefixEnd_2510819 286501551875848253958991 := by
  unfold tailWord_2510819
  simp only [CollatzResearch.WordTrace]
  refine ⟨91577092290739051590703511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61051394860492701060469007 91577092290739051590703511)
  ·
    refine ⟨137365638436108577386055267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91577092290739051590703511 137365638436108577386055267)
    ·
      refine ⟨206048457654162866079082901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137365638436108577386055267 206048457654162866079082901)
      ·
        refine ⟨9658521452538884347457011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 206048457654162866079082901 9658521452538884347457011)
        ·
          refine ⟨14487782178808326521185517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9658521452538884347457011 14487782178808326521185517)
          ·
            refine ⟨5432918317053122445444569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14487782178808326521185517 5432918317053122445444569)
            ·
              refine ⟨4074688737789841834083427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5432918317053122445444569 4074688737789841834083427)
              ·
                refine ⟨6112033106684762751125141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074688737789841834083427 6112033106684762751125141)
                ·
                  refine ⟨286501551875848253958991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6112033106684762751125141 286501551875848253958991)
                  ·
                    rfl

theorem cell22_2510819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 6].length) (baseStart_2510819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510819 prefixEnd_2510819 := by exact prefixLift 2510819
  have htrace : WordTrace (prefixWord ++ tailWord_2510819) baseStart_2510819 baseEnd_2510819 := by
    simpa [prefixWord, tailWord_2510819, baseEnd_2510819] using wordTrace_append hprefix tailTrace_2510819
  have hstable : (prefixWord ++ tailWord_2510819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510819).length < 2 ^ (prefixWord ++ tailWord_2510819).sum := by decide
  have hdescent : baseEnd_2510819 < baseStart_2510819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510832 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_2510832 : Nat := 118140960795 + 2510832 * 2 ^ 59
def prefixEnd_2510832 : Nat := 4983230072969 + 3 ^ 40 * 2510832 * 2
def baseEnd_2510832 : Nat := 859509105793217061301933

theorem tailTrace_2510832 : CollatzResearch.WordTrace tailWord_2510832 prefixEnd_2510832 859509105793217061301933 := by
  unfold tailWord_2510832
  simp only [CollatzResearch.WordTrace]
  refine ⟨45788783219845977405463375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61051710959794636540617833 45788783219845977405463375)
  ·
    refine ⟨68683174829768966108195063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45788783219845977405463375 68683174829768966108195063)
    ·
      refine ⟨103024762244653449162292595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68683174829768966108195063 103024762244653449162292595)
      ·
        refine ⟨154537143366980173743438893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103024762244653449162292595 154537143366980173743438893)
        ·
          refine ⟨57951428762617565153789585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154537143366980173743438893 57951428762617565153789585)
          ·
            refine ⟨43463571571963173865342189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57951428762617565153789585 43463571571963173865342189)
            ·
              refine ⟨16298839339486190199503321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43463571571963173865342189 16298839339486190199503321)
              ·
                refine ⟨12224129504614642649627491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16298839339486190199503321 12224129504614642649627491)
                ·
                  refine ⟨18336194256921963974441237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12224129504614642649627491 18336194256921963974441237)
                  ·
                    refine ⟨859509105793217061301933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18336194256921963974441237 859509105793217061301933)
                    ·
                      rfl

theorem cell22_2510832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_2510832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510832 prefixEnd_2510832 := by exact prefixLift 2510832
  have htrace : WordTrace (prefixWord ++ tailWord_2510832) baseStart_2510832 baseEnd_2510832 := by
    simpa [prefixWord, tailWord_2510832, baseEnd_2510832] using wordTrace_append hprefix tailTrace_2510832
  have hstable : (prefixWord ++ tailWord_2510832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510832).length < 2 ^ (prefixWord ++ tailWord_2510832).sum := by decide
  have hdescent : baseEnd_2510832 < baseStart_2510832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510838 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2510838 : Nat := 118140960795 + 2510838 * 2 ^ 59
def prefixEnd_2510838 : Nat := 4983230072969 + 3 ^ 40 * 2510838 * 2
def baseEnd_2510838 : Nat := 859511159715835045651915

theorem tailTrace_2510838 : CollatzResearch.WordTrace tailWord_2510838 prefixEnd_2510838 859511159715835045651915 := by
  unfold tailWord_2510838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723611579854388614727823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61051856851780145223763445 5723611579854388614727823)
  ·
    refine ⟨8585417369781582922091735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5723611579854388614727823 8585417369781582922091735)
    ·
      refine ⟨12878126054672374383137603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8585417369781582922091735 12878126054672374383137603)
      ·
        refine ⟨19317189082008561574706405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12878126054672374383137603 19317189082008561574706405)
        ·
          refine ⟨3621972952876605295257451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19317189082008561574706405 3621972952876605295257451)
          ·
            refine ⟨5432959429314907942886177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621972952876605295257451 5432959429314907942886177)
            ·
              refine ⟨4074719571986180957164633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5432959429314907942886177 4074719571986180957164633)
              ·
                refine ⟨3056039678989635717873475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074719571986180957164633 3056039678989635717873475)
                ·
                  refine ⟨4584059518484453576810213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056039678989635717873475 4584059518484453576810213)
                  ·
                    refine ⟨859511159715835045651915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584059518484453576810213 859511159715835045651915)
                    ·
                      rfl

theorem cell22_2510838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2510838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510838 prefixEnd_2510838 := by exact prefixLift 2510838
  have htrace : WordTrace (prefixWord ++ tailWord_2510838) baseStart_2510838 baseEnd_2510838 := by
    simpa [prefixWord, tailWord_2510838, baseEnd_2510838] using wordTrace_append hprefix tailTrace_2510838
  have hstable : (prefixWord ++ tailWord_2510838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510838).length < 2 ^ (prefixWord ++ tailWord_2510838).sum := by decide
  have hdescent : baseEnd_2510838 < baseStart_2510838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510849 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2510849 : Nat := 118140960795 + 2510849 * 2 ^ 59
def prefixEnd_2510849 : Nat := 4983230072969 + 3 ^ 40 * 2510849 * 2
def baseEnd_2510849 : Nat := 859514925240634683626881

theorem tailTrace_2510849 : CollatzResearch.WordTrace tailWord_2510849 prefixEnd_2510849 859514925240634683626881 := by
  unfold tailWord_2510849
  simp only [CollatzResearch.WordTrace]
  refine ⟨91578186480630366714295601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61052124320420244476197067 91578186480630366714295601)
  ·
    refine ⟨68683639860472775035721701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91578186480630366714295601 68683639860472775035721701)
    ·
      refine ⟨12878182473838645319197819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68683639860472775035721701 12878182473838645319197819)
      ·
        refine ⟨19317273710757967978796729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12878182473838645319197819 19317273710757967978796729)
        ·
          refine ⟨14487955283068475984097547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19317273710757967978796729 14487955283068475984097547)
          ·
            refine ⟨21731932924602713976146321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14487955283068475984097547 21731932924602713976146321)
            ·
              refine ⟨16298949693452035482109741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21731932924602713976146321 16298949693452035482109741)
              ·
                refine ⟨6112106135044513305791153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16298949693452035482109741 6112106135044513305791153)
                ·
                  refine ⟨4584079601283384979343365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112106135044513305791153 4584079601283384979343365)
                  ·
                    refine ⟨859514925240634683626881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584079601283384979343365 859514925240634683626881)
                    ·
                      rfl

theorem cell22_2510849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2510849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510849 prefixEnd_2510849 := by exact prefixLift 2510849
  have htrace : WordTrace (prefixWord ++ tailWord_2510849) baseStart_2510849 baseEnd_2510849 := by
    simpa [prefixWord, tailWord_2510849, baseEnd_2510849] using wordTrace_append hprefix tailTrace_2510849
  have hstable : (prefixWord ++ tailWord_2510849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510849).length < 2 ^ (prefixWord ++ tailWord_2510849).sum := by decide
  have hdescent : baseEnd_2510849 < baseStart_2510849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510892 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_2510892 : Nat := 118140960795 + 2510892 * 2 ^ 59
def prefixEnd_2510892 : Nat := 4983230072969 + 3 ^ 40 * 2510892 * 2
def baseEnd_2510892 : Nat := 286509881673132301600583

theorem tailTrace_2510892 : CollatzResearch.WordTrace tailWord_2510892 prefixEnd_2510892 286509881673132301600583 := by
  unfold tailWord_2510892
  simp only [CollatzResearch.WordTrace]
  refine ⟨45789877409737292529055465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61053169879649723372073953 45789877409737292529055465)
  ·
    refine ⟨34342408057302969396791599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45789877409737292529055465 34342408057302969396791599)
    ·
      refine ⟨51513612085954454095187399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34342408057302969396791599 51513612085954454095187399)
      ·
        refine ⟨77270418128931681142781099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51513612085954454095187399 77270418128931681142781099)
        ·
          refine ⟨115905627193397521714171649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77270418128931681142781099 115905627193397521714171649)
          ·
            refine ⟨86929220395048141285628737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115905627193397521714171649 86929220395048141285628737)
            ·
              refine ⟨65196915296286105964221553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86929220395048141285628737 65196915296286105964221553)
              ·
                refine ⟨48897686472214579473166165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65196915296286105964221553 48897686472214579473166165)
                ·
                  refine ⟨286509881673132301600583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48897686472214579473166165 286509881673132301600583)
                  ·
                    rfl

theorem cell22_2510892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_2510892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510892 prefixEnd_2510892 := by exact prefixLift 2510892
  have htrace : WordTrace (prefixWord ++ tailWord_2510892) baseStart_2510892 baseEnd_2510892 := by
    simpa [prefixWord, tailWord_2510892, baseEnd_2510892] using wordTrace_append hprefix tailTrace_2510892
  have hstable : (prefixWord ++ tailWord_2510892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510892).length < 2 ^ (prefixWord ++ tailWord_2510892).sum := by decide
  have hdescent : baseEnd_2510892 < baseStart_2510892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510907 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_2510907 : Nat := 118140960795 + 2510907 * 2 ^ 59
def prefixEnd_2510907 : Nat := 4983230072969 + 3 ^ 40 * 2510907 * 2
def baseEnd_2510907 : Nat := 859534779825941865676703

theorem tailTrace_2510907 : CollatzResearch.WordTrace tailWord_2510907 prefixEnd_2510907 859534779825941865676703 := by
  unfold tailWord_2510907
  simp only [CollatzResearch.WordTrace]
  refine ⟨91580301914420242619906975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61053534609613495079937983 91580301914420242619906975)
  ·
    refine ⟨137370452871630363929860463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91580301914420242619906975 137370452871630363929860463)
    ·
      refine ⟨206055679307445545894790695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137370452871630363929860463 206055679307445545894790695)
      ·
        refine ⟨309083518961168318842186043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206055679307445545894790695 309083518961168318842186043)
        ·
          refine ⟨463625278441752478263279065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309083518961168318842186043 463625278441752478263279065)
          ·
            refine ⟨347718958831314358697459299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463625278441752478263279065 347718958831314358697459299)
            ·
              refine ⟨521578438246971538046188949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347718958831314358697459299 521578438246971538046188949)
              ·
                refine ⟨24448989292826790845915107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 521578438246971538046188949 24448989292826790845915107)
                ·
                  refine ⟨36673483939240186268872661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24448989292826790845915107 36673483939240186268872661)
                  ·
                    refine ⟨859534779825941865676703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36673483939240186268872661 859534779825941865676703)
                    ·
                      rfl

theorem cell22_2510907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_2510907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510907 prefixEnd_2510907 := by exact prefixLift 2510907
  have htrace : WordTrace (prefixWord ++ tailWord_2510907) baseStart_2510907 baseEnd_2510907 := by
    simpa [prefixWord, tailWord_2510907, baseEnd_2510907] using wordTrace_append hprefix tailTrace_2510907
  have hstable : (prefixWord ++ tailWord_2510907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510907).length < 2 ^ (prefixWord ++ tailWord_2510907).sum := by decide
  have hdescent : baseEnd_2510907 < baseStart_2510907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510926 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_2510926 : Nat := 118140960795 + 2510926 * 2 ^ 59
def prefixEnd_2510926 : Nat := 4983230072969 + 3 ^ 40 * 2510926 * 2
def baseEnd_2510926 : Nat := 286513761304744049817215

theorem tailTrace_2510926 : CollatzResearch.WordTrace tailWord_2510926 prefixEnd_2510926 286513761304744049817215 := by
  unfold tailWord_2510926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447624362668926108106079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61053996600900939243232421 11447624362668926108106079)
  ·
    refine ⟨17171436544003389162159119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11447624362668926108106079 17171436544003389162159119)
    ·
      refine ⟨25757154816005083743238679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17171436544003389162159119 25757154816005083743238679)
      ·
        refine ⟨38635732224007625614858019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25757154816005083743238679 38635732224007625614858019)
        ·
          refine ⟨57953598336011438422287029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38635732224007625614858019 57953598336011438422287029)
          ·
            refine ⟨5433149844001072352089409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57953598336011438422287029 5433149844001072352089409)
            ·
              refine ⟨4074862383000804264067057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433149844001072352089409 4074862383000804264067057)
              ·
                refine ⟨3056146787250603198050293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074862383000804264067057 3056146787250603198050293)
                ·
                  refine ⟨286513761304744049817215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056146787250603198050293 286513761304744049817215)
                  ·
                    rfl

theorem cell22_2510926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_2510926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510926 prefixEnd_2510926 := by exact prefixLift 2510926
  have htrace : WordTrace (prefixWord ++ tailWord_2510926) baseStart_2510926 baseEnd_2510926 := by
    simpa [prefixWord, tailWord_2510926, baseEnd_2510926] using wordTrace_append hprefix tailTrace_2510926
  have hstable : (prefixWord ++ tailWord_2510926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510926).length < 2 ^ (prefixWord ++ tailWord_2510926).sum := by decide
  have hdescent : baseEnd_2510926 < baseStart_2510926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510930 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_2510930 : Nat := 118140960795 + 2510930 * 2 ^ 59
def prefixEnd_2510930 : Nat := 4983230072969 + 3 ^ 40 * 2510930 * 2
def baseEnd_2510930 : Nat := 859542653195977472351633

theorem tailTrace_2510930 : CollatzResearch.WordTrace tailWord_2510930 prefixEnd_2510930 859542653195977472351633 := by
  unfold tailWord_2510930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22895285198334229386998561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61054093862224611698662829 22895285198334229386998561)
  ·
    refine ⟨17171463898750672040248921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22895285198334229386998561 17171463898750672040248921)
    ·
      refine ⟨12878597924063004030186691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17171463898750672040248921 12878597924063004030186691)
      ·
        refine ⟨19317896886094506045280037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12878597924063004030186691 19317896886094506045280037)
        ·
          refine ⟨3622105666142719883490007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19317896886094506045280037 3622105666142719883490007)
          ·
            refine ⟨5433158499214079825235011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622105666142719883490007 5433158499214079825235011)
            ·
              refine ⟨8149737748821119737852517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433158499214079825235011 8149737748821119737852517)
              ·
                refine ⟨1528075827903959950847347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8149737748821119737852517 1528075827903959950847347)
                ·
                  refine ⟨2292113741855939926271021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528075827903959950847347 2292113741855939926271021)
                  ·
                    refine ⟨859542653195977472351633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2292113741855939926271021 859542653195977472351633)
                    ·
                      rfl

theorem cell22_2510930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_2510930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510930 prefixEnd_2510930 := by exact prefixLift 2510930
  have htrace : WordTrace (prefixWord ++ tailWord_2510930) baseStart_2510930 baseEnd_2510930 := by
    simpa [prefixWord, tailWord_2510930, baseEnd_2510930] using wordTrace_append hprefix tailTrace_2510930
  have hstable : (prefixWord ++ tailWord_2510930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510930).length < 2 ^ (prefixWord ++ tailWord_2510930).sum := by decide
  have hdescent : baseEnd_2510930 < baseStart_2510930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510941 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2510941 : Nat := 118140960795 + 2510941 * 2 ^ 59
def prefixEnd_2510941 : Nat := 4983230072969 + 3 ^ 40 * 2510941 * 2
def baseEnd_2510941 : Nat := 859546418720777110326599

theorem tailTrace_2510941 : CollatzResearch.WordTrace tailWord_2510941 prefixEnd_2510941 859546418720777110326599 := by
  unfold tailWord_2510941
  simp only [CollatzResearch.WordTrace]
  refine ⟨91581541996297066426644677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61054361330864710951096451 91581541996297066426644677)
  ·
    refine ⟨17171539124305699954995877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91581541996297066426644677 17171539124305699954995877)
    ·
      refine ⟨3219663585807318741561727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17171539124305699954995877 3219663585807318741561727)
      ·
        refine ⟨4829495378710978112342591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219663585807318741561727 4829495378710978112342591)
        ·
          refine ⟨7244243068066467168513887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829495378710978112342591 7244243068066467168513887)
          ·
            refine ⟨10866364602099700752770831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244243068066467168513887 10866364602099700752770831)
            ·
              refine ⟨16299546903149551129156247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10866364602099700752770831 16299546903149551129156247)
              ·
                refine ⟨24449320354724326693734371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16299546903149551129156247 24449320354724326693734371)
                ·
                  refine ⟨36673980532086490040601557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24449320354724326693734371 36673980532086490040601557)
                  ·
                    refine ⟨859546418720777110326599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36673980532086490040601557 859546418720777110326599)
                    ·
                      rfl

theorem cell22_2510941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2510941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510941 prefixEnd_2510941 := by exact prefixLift 2510941
  have htrace : WordTrace (prefixWord ++ tailWord_2510941) baseStart_2510941 baseEnd_2510941 := by
    simpa [prefixWord, tailWord_2510941, baseEnd_2510941] using wordTrace_append hprefix tailTrace_2510941
  have hstable : (prefixWord ++ tailWord_2510941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510941).length < 2 ^ (prefixWord ++ tailWord_2510941).sum := by decide
  have hdescent : baseEnd_2510941 < baseStart_2510941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510973 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_2510973 : Nat := 118140960795 + 2510973 * 2 ^ 59
def prefixEnd_2510973 : Nat := 4983230072969 + 3 ^ 40 * 2510973 * 2
def baseEnd_2510973 : Nat := 859557372974739693526501

theorem tailTrace_2510973 : CollatzResearch.WordTrace tailWord_2510973 prefixEnd_2510973 859557372974739693526501 := by
  unfold tailWord_2510973
  simp only [CollatzResearch.WordTrace]
  refine ⟨91582709132181135891809573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61055139421454090594539715 91582709132181135891809573)
  ·
    refine ⟨17171757962283962979714295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91582709132181135891809573 17171757962283962979714295)
    ·
      refine ⟨25757636943425944469571443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17171757962283962979714295 25757636943425944469571443)
      ·
        refine ⟨38636455415138916704357165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25757636943425944469571443 38636455415138916704357165)
        ·
          refine ⟨14488670780677093764133937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38636455415138916704357165 14488670780677093764133937)
          ·
            refine ⟨10866503085507820323100453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14488670780677093764133937 10866503085507820323100453)
            ·
              refine ⟨2037469328532716310581335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10866503085507820323100453 2037469328532716310581335)
              ·
                refine ⟨3056203992799074465872003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037469328532716310581335 3056203992799074465872003)
                ·
                  refine ⟨4584305989198611698808005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056203992799074465872003 4584305989198611698808005)
                  ·
                    refine ⟨859557372974739693526501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584305989198611698808005 859557372974739693526501)
                    ·
                      rfl

theorem cell22_2510973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_2510973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2510973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2510973 prefixEnd_2510973 := by exact prefixLift 2510973
  have htrace : WordTrace (prefixWord ++ tailWord_2510973) baseStart_2510973 baseEnd_2510973 := by
    simpa [prefixWord, tailWord_2510973, baseEnd_2510973] using wordTrace_append hprefix tailTrace_2510973
  have hstable : (prefixWord ++ tailWord_2510973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510973).length < 2 ^ (prefixWord ++ tailWord_2510973).sum := by decide
  have hdescent : baseEnd_2510973 < baseStart_2510973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511121 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_2511121 : Nat := 118140960795 + 2511121 * 2 ^ 59
def prefixEnd_2511121 : Nat := 4983230072969 + 3 ^ 40 * 2511121 * 2
def baseEnd_2511121 : Nat := 859608036399316640826047

theorem tailTrace_2511121 : CollatzResearch.WordTrace tailWord_2511121 prefixEnd_2511121 859608036399316640826047 := by
  unfold tailWord_2511121
  simp only [CollatzResearch.WordTrace]
  refine ⟨91588107135644957168197217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61058738090429971445464811 91588107135644957168197217)
  ·
    refine ⟨68691080351733717876147913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91588107135644957168197217 68691080351733717876147913)
    ·
      refine ⟨51518310263800288407110935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68691080351733717876147913 51518310263800288407110935)
      ·
        refine ⟨77277465395700432610666403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51518310263800288407110935 77277465395700432610666403)
        ·
          refine ⟨115916198093550648915999605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77277465395700432610666403 115916198093550648915999605)
          ·
            refine ⟨10867143571270373335874963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115916198093550648915999605 10867143571270373335874963)
            ·
              refine ⟨16300715356905560003812445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867143571270373335874963 16300715356905560003812445)
              ·
                refine ⟨6112768258839585001429667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16300715356905560003812445 6112768258839585001429667)
                ·
                  refine ⟨9169152388259377502144501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6112768258839585001429667 9169152388259377502144501)
                  ·
                    refine ⟨859608036399316640826047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169152388259377502144501 859608036399316640826047)
                    ·
                      rfl

theorem cell22_2511121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_2511121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511121 prefixEnd_2511121 := by exact prefixLift 2511121
  have htrace : WordTrace (prefixWord ++ tailWord_2511121) baseStart_2511121 baseEnd_2511121 := by
    simpa [prefixWord, tailWord_2511121, baseEnd_2511121] using wordTrace_append hprefix tailTrace_2511121
  have hstable : (prefixWord ++ tailWord_2511121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511121).length < 2 ^ (prefixWord ++ tailWord_2511121).sum := by decide
  have hdescent : baseEnd_2511121 < baseStart_2511121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511138 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2511138 : Nat := 118140960795 + 2511138 * 2 ^ 59
def prefixEnd_2511138 : Nat := 4983230072969 + 3 ^ 40 * 2511138 * 2
def baseEnd_2511138 : Nat := 859613855846734263150995

theorem tailTrace_2511138 : CollatzResearch.WordTrace tailWord_2511138 prefixEnd_2511138 859613855846734263150995 := by
  unfold tailWord_2511138
  simp only [CollatzResearch.WordTrace]
  refine ⟨22897181794145842267891517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61059151451055579381044045 22897181794145842267891517)
  ·
    refine ⟨8586443172804690850459319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22897181794145842267891517 8586443172804690850459319)
    ·
      refine ⟨12879664759207036275688979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8586443172804690850459319 12879664759207036275688979)
      ·
        refine ⟨19319497138810554413533469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12879664759207036275688979 19319497138810554413533469)
        ·
          refine ⟨7244811427053957905075051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19319497138810554413533469 7244811427053957905075051)
          ·
            refine ⟨10867217140580936857612577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244811427053957905075051 10867217140580936857612577)
            ·
              refine ⟨8150412855435702643209433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10867217140580936857612577 8150412855435702643209433)
              ·
                refine ⟨6112809641576776982407075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8150412855435702643209433 6112809641576776982407075)
                ·
                  refine ⟨9169214462365165473610613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6112809641576776982407075 9169214462365165473610613)
                  ·
                    refine ⟨859613855846734263150995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169214462365165473610613 859613855846734263150995)
                    ·
                      rfl

theorem cell22_2511138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2511138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511138 prefixEnd_2511138 := by exact prefixLift 2511138
  have htrace : WordTrace (prefixWord ++ tailWord_2511138) baseStart_2511138 baseEnd_2511138 := by
    simpa [prefixWord, tailWord_2511138, baseEnd_2511138] using wordTrace_append hprefix tailTrace_2511138
  have hstable : (prefixWord ++ tailWord_2511138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511138).length < 2 ^ (prefixWord ++ tailWord_2511138).sum := by decide
  have hdescent : baseEnd_2511138 < baseStart_2511138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511140 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 4]
def baseStart_2511140 : Nat := 118140960795 + 2511140 * 2 ^ 59
def prefixEnd_2511140 : Nat := 4983230072969 + 3 ^ 40 * 2511140 * 2
def baseEnd_2511140 : Nat := 286538180162535641533663

theorem tailTrace_2511140 : CollatzResearch.WordTrace tailWord_2511140 prefixEnd_2511140 286538180162535641533663 := by
  unfold tailWord_2511140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45794400061288061706569437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61059200081717415608759249 45794400061288061706569437)
  ·
    refine ⟨17172900022983023139963539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45794400061288061706569437 17172900022983023139963539)
    ·
      refine ⟨25759350034474534709945309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17172900022983023139963539 25759350034474534709945309)
      ·
        refine ⟨9659756262927950516229491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25759350034474534709945309 9659756262927950516229491)
        ·
          refine ⟨14489634394391925774344237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9659756262927950516229491 14489634394391925774344237)
          ·
            refine ⟨5433612897896972165379089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14489634394391925774344237 5433612897896972165379089)
            ·
              refine ⟨4075209673422729124034317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433612897896972165379089 4075209673422729124034317)
              ·
                refine ⟨1528203627533523421512869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4075209673422729124034317 1528203627533523421512869)
                ·
                  refine ⟨286538180162535641533663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528203627533523421512869 286538180162535641533663)
                  ·
                    rfl

theorem cell22_2511140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_2511140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511140 prefixEnd_2511140 := by exact prefixLift 2511140
  have htrace : WordTrace (prefixWord ++ tailWord_2511140) baseStart_2511140 baseEnd_2511140 := by
    simpa [prefixWord, tailWord_2511140, baseEnd_2511140] using wordTrace_append hprefix tailTrace_2511140
  have hstable : (prefixWord ++ tailWord_2511140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511140).length < 2 ^ (prefixWord ++ tailWord_2511140).sum := by decide
  have hdescent : baseEnd_2511140 < baseStart_2511140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511172 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2511172 : Nat := 118140960795 + 2511172 * 2 ^ 59
def prefixEnd_2511172 : Nat := 4983230072969 + 3 ^ 40 * 2511172 * 2
def baseEnd_2511172 : Nat := 859625494741569507800891

theorem tailTrace_2511172 : CollatzResearch.WordTrace tailWord_2511172 prefixEnd_2511172 859625494741569507800891 := by
  unfold tailWord_2511172
  simp only [CollatzResearch.WordTrace]
  refine ⟨45794983629230096439151885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61059978172306795252202513 45794983629230096439151885)
  ·
    refine ⟨17173118860961286164681957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45794983629230096439151885 17173118860961286164681957)
    ·
      refine ⟨3219959786430241155877867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17173118860961286164681957 3219959786430241155877867)
      ·
        refine ⟨4829939679645361733816801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219959786430241155877867 4829939679645361733816801)
        ·
          refine ⟨3622454759734021300362601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829939679645361733816801 3622454759734021300362601)
          ·
            refine ⟨2716841069800515975271951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3622454759734021300362601 2716841069800515975271951)
            ·
              refine ⟨4075261604700773962907927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716841069800515975271951 4075261604700773962907927)
              ·
                refine ⟨6112892407051160944361891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4075261604700773962907927 6112892407051160944361891)
                ·
                  refine ⟨9169338610576741416542837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6112892407051160944361891 9169338610576741416542837)
                  ·
                    refine ⟨859625494741569507800891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169338610576741416542837 859625494741569507800891)
                    ·
                      rfl

theorem cell22_2511172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2511172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511172 prefixEnd_2511172 := by exact prefixLift 2511172
  have htrace : WordTrace (prefixWord ++ tailWord_2511172) baseStart_2511172 baseEnd_2511172 := by
    simpa [prefixWord, tailWord_2511172, baseEnd_2511172] using wordTrace_append hprefix tailTrace_2511172
  have hstable : (prefixWord ++ tailWord_2511172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511172).length < 2 ^ (prefixWord ++ tailWord_2511172).sum := by decide
  have hdescent : baseEnd_2511172 < baseStart_2511172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511213 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2511213 : Nat := 118140960795 + 2511213 * 2 ^ 59
def prefixEnd_2511213 : Nat := 4983230072969 + 3 ^ 40 * 2511213 * 2
def baseEnd_2511213 : Nat := 286546509959819689175255

theorem tailTrace_2511213 : CollatzResearch.WordTrace tailWord_2511213 prefixEnd_2511213 286546509959819689175255 := by
  unfold tailWord_2511213
  simp only [CollatzResearch.WordTrace]
  refine ⟨91591462651311656880546293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61060975100874437920364195 91591462651311656880546293)
  ·
    refine ⟨8586699623560467832551215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91591462651311656880546293 8586699623560467832551215)
    ·
      refine ⟨12880049435340701748826823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8586699623560467832551215 12880049435340701748826823)
      ·
        refine ⟨19320074153011052623240235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12880049435340701748826823 19320074153011052623240235)
        ·
          refine ⟨28980111229516578934860353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19320074153011052623240235 28980111229516578934860353)
          ·
            refine ⟨21735083422137434201145265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28980111229516578934860353 21735083422137434201145265)
            ·
              refine ⟨16301312566603075650858949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21735083422137434201145265 16301312566603075650858949)
              ·
                refine ⟨3056496106238076684536053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16301312566603075650858949 3056496106238076684536053)
                ·
                  refine ⟨286546509959819689175255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056496106238076684536053 286546509959819689175255)
                  ·
                    rfl

theorem cell22_2511213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2511213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511213 prefixEnd_2511213 := by exact prefixLift 2511213
  have htrace : WordTrace (prefixWord ++ tailWord_2511213) baseStart_2511213 baseEnd_2511213 := by
    simpa [prefixWord, tailWord_2511213, baseEnd_2511213] using wordTrace_append hprefix tailTrace_2511213
  have hstable : (prefixWord ++ tailWord_2511213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511213).length < 2 ^ (prefixWord ++ tailWord_2511213).sum := by decide
  have hdescent : baseEnd_2511213 < baseStart_2511213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511243 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 3, 4]
def baseStart_2511243 : Nat := 118140960795 + 2511243 * 2 ^ 59
def prefixEnd_2511243 : Nat := 4983230072969 + 3 ^ 40 * 2511243 * 2
def baseEnd_2511243 : Nat := 859649799492548989275673

theorem tailTrace_2511243 : CollatzResearch.WordTrace tailWord_2511243 prefixEnd_2511243 859649799492548989275673 := by
  unfold tailWord_2511243
  simp only [CollatzResearch.WordTrace]
  refine ⟨91592556841202972004138383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61061704560801981336092255 91592556841202972004138383)
  ·
    refine ⟨137388835261804458006207575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91592556841202972004138383 137388835261804458006207575)
    ·
      refine ⟨206083252892706687009311363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137388835261804458006207575 206083252892706687009311363)
      ·
        refine ⟨309124879339060030513967045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206083252892706687009311363 309124879339060030513967045)
        ·
          refine ⟨57960914876073755721368821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309124879339060030513967045 57960914876073755721368821)
          ·
            refine ⟨5433835769631914598878327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57960914876073755721368821 5433835769631914598878327)
            ·
              refine ⟨8150753654447871898317491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433835769631914598878327 8150753654447871898317491)
              ·
                refine ⟨12226130481671807847476237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8150753654447871898317491 12226130481671807847476237)
                ·
                  refine ⟨4584798930626927942803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12226130481671807847476237 4584798930626927942803589)
                  ·
                    refine ⟨859649799492548989275673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584798930626927942803589 859649799492548989275673)
                    ·
                      rfl

theorem cell22_2511243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_2511243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511243 prefixEnd_2511243 := by exact prefixLift 2511243
  have htrace : WordTrace (prefixWord ++ tailWord_2511243) baseStart_2511243 baseEnd_2511243 := by
    simpa [prefixWord, tailWord_2511243, baseEnd_2511243] using wordTrace_append hprefix tailTrace_2511243
  have hstable : (prefixWord ++ tailWord_2511243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511243).length < 2 ^ (prefixWord ++ tailWord_2511243).sum := by decide
  have hdescent : baseEnd_2511243 < baseStart_2511243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511273 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_2511273 : Nat := 118140960795 + 2511273 * 2 ^ 59
def prefixEnd_2511273 : Nat := 4983230072969 + 3 ^ 40 * 2511273 * 2
def baseEnd_2511273 : Nat := 859660069105638911025581

theorem tailTrace_2511273 : CollatzResearch.WordTrace tailWord_2511273 prefixEnd_2511273 859660069105638911025581 := by
  unfold tailWord_2511273
  simp only [CollatzResearch.WordTrace]
  refine ⟨91593651031094287127730473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61062434020729524751820315 91593651031094287127730473)
  ·
    refine ⟨68695238273320715345797855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91593651031094287127730473 68695238273320715345797855)
    ·
      refine ⟨103042857409981073018696783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68695238273320715345797855 103042857409981073018696783)
      ·
        refine ⟨154564286114971609528045175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103042857409981073018696783 154564286114971609528045175)
        ·
          refine ⟨231846429172457414292067763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154564286114971609528045175 231846429172457414292067763)
          ·
            refine ⟨347769643758686121438101645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231846429172457414292067763 347769643758686121438101645)
            ·
              refine ⟨130413616409507295539288117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347769643758686121438101645 130413616409507295539288117)
              ·
                refine ⟨12226276538391308956808261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130413616409507295539288117 12226276538391308956808261)
                ·
                  refine ⟨2292426850948370429401549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12226276538391308956808261 2292426850948370429401549)
                  ·
                    refine ⟨859660069105638911025581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2292426850948370429401549 859660069105638911025581)
                    ·
                      rfl

theorem cell22_2511273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_2511273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511273 prefixEnd_2511273 := by exact prefixLift 2511273
  have htrace : WordTrace (prefixWord ++ tailWord_2511273) baseStart_2511273 baseEnd_2511273 := by
    simpa [prefixWord, tailWord_2511273, baseEnd_2511273] using wordTrace_append hprefix tailTrace_2511273
  have hstable : (prefixWord ++ tailWord_2511273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511273).length < 2 ^ (prefixWord ++ tailWord_2511273).sum := by decide
  have hdescent : baseEnd_2511273 < baseStart_2511273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511399 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 5]
def baseStart_2511399 : Nat := 118140960795 + 2511399 * 2 ^ 59
def prefixEnd_2511399 : Nat := 4983230072969 + 3 ^ 40 * 2511399 * 2
def baseEnd_2511399 : Nat := 286567733826872194125065

theorem tailTrace_2511399 : CollatzResearch.WordTrace tailWord_2511399 prefixEnd_2511399 286567733826872194125065 := by
  unfold tailWord_2511399
  simp only [CollatzResearch.WordTrace]
  refine ⟨91598246628637810646817251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61065497752425207097878167 91598246628637810646817251)
  ·
    refine ⟨137397369942956715970225877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91598246628637810646817251 137397369942956715970225877)
    ·
      refine ⟨3220250858038048030552169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 137397369942956715970225877 3220250858038048030552169)
      ·
        refine ⟨2415188143528536022914127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3220250858038048030552169 2415188143528536022914127)
        ·
          refine ⟨3622782215292804034371191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415188143528536022914127 3622782215292804034371191)
          ·
            refine ⟨5434173322939206051556787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622782215292804034371191 5434173322939206051556787)
            ·
              refine ⟨8151259984408809077335181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5434173322939206051556787 8151259984408809077335181)
              ·
                refine ⟨3056722494153303404000693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8151259984408809077335181 3056722494153303404000693)
                ·
                  refine ⟨286567733826872194125065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056722494153303404000693 286567733826872194125065)
                  ·
                    rfl

theorem cell22_2511399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 5].length) (baseStart_2511399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511399 prefixEnd_2511399 := by exact prefixLift 2511399
  have htrace : WordTrace (prefixWord ++ tailWord_2511399) baseStart_2511399 baseEnd_2511399 := by
    simpa [prefixWord, tailWord_2511399, baseEnd_2511399] using wordTrace_append hprefix tailTrace_2511399
  have hstable : (prefixWord ++ tailWord_2511399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511399).length < 2 ^ (prefixWord ++ tailWord_2511399).sum := by decide
  have hdescent : baseEnd_2511399 < baseStart_2511399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511425 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2511425 : Nat := 118140960795 + 2511425 * 2 ^ 59
def prefixEnd_2511425 : Nat := 4983230072969 + 3 ^ 40 * 2511425 * 2
def baseEnd_2511425 : Nat := 859712101811961181225115

theorem tailTrace_2511425 : CollatzResearch.WordTrace tailWord_2511425 prefixEnd_2511425 859712101811961181225115 := by
  unfold tailWord_2511425
  simp only [CollatzResearch.WordTrace]
  refine ⟨91599194926543617087263729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61066129951029078058175819 91599194926543617087263729)
  ·
    refine ⟨68699396194907712815447797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91599194926543617087263729 68699396194907712815447797)
    ·
      refine ⟨6440568393272598076448231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68699396194907712815447797 6440568393272598076448231)
      ·
        refine ⟨9660852589908897114672347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440568393272598076448231 9660852589908897114672347)
        ·
          refine ⟨14491278884863345672008521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9660852589908897114672347 14491278884863345672008521)
          ·
            refine ⟨10868459163647509254006391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14491278884863345672008521 10868459163647509254006391)
            ·
              refine ⟨16302688745471263881009587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868459163647509254006391 16302688745471263881009587)
              ·
                refine ⟨24454033118206895821514381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16302688745471263881009587 24454033118206895821514381)
                ·
                  refine ⟨9170262419327585933067893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24454033118206895821514381 9170262419327585933067893)
                  ·
                    refine ⟨859712101811961181225115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9170262419327585933067893 859712101811961181225115)
                    ·
                      rfl

theorem cell22_2511425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2511425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511425 prefixEnd_2511425 := by exact prefixLift 2511425
  have htrace : WordTrace (prefixWord ++ tailWord_2511425) baseStart_2511425 baseEnd_2511425 := by
    simpa [prefixWord, tailWord_2511425, baseEnd_2511425] using wordTrace_append hprefix tailTrace_2511425
  have hstable : (prefixWord ++ tailWord_2511425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511425).length < 2 ^ (prefixWord ++ tailWord_2511425).sum := by decide
  have hdescent : baseEnd_2511425 < baseStart_2511425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511444 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 4]
def baseStart_2511444 : Nat := 118140960795 + 2511444 * 2 ^ 59
def prefixEnd_2511444 : Nat := 4983230072969 + 3 ^ 40 * 2511444 * 2
def baseEnd_2511444 : Nat := 286572868633417155000019

theorem tailTrace_2511444 : CollatzResearch.WordTrace tailWord_2511444 prefixEnd_2511444 286572868633417155000019 := by
  unfold tailWord_2511444
  simp only [CollatzResearch.WordTrace]
  refine ⟨45799943956737391666102693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61066591942316522221470257 45799943956737391666102693)
  ·
    refine ⟨8587489491888260937394255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45799943956737391666102693 8587489491888260937394255)
    ·
      refine ⟨12881234237832391406091383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8587489491888260937394255 12881234237832391406091383)
      ·
        refine ⟨19321851356748587109137075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12881234237832391406091383 19321851356748587109137075)
        ·
          refine ⟨28982777035122880663705613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19321851356748587109137075 28982777035122880663705613)
          ·
            refine ⟨10868541388171080248889605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28982777035122880663705613 10868541388171080248889605)
            ·
              refine ⟨2037851510282077546666801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10868541388171080248889605 2037851510282077546666801)
              ·
                refine ⟨1528388632711558160000101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037851510282077546666801 1528388632711558160000101)
                ·
                  refine ⟨286572868633417155000019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528388632711558160000101 286572868633417155000019)
                  ·
                    rfl

theorem cell22_2511444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_2511444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511444 prefixEnd_2511444 := by exact prefixLift 2511444
  have htrace : WordTrace (prefixWord ++ tailWord_2511444) baseStart_2511444 baseEnd_2511444 := by
    simpa [prefixWord, tailWord_2511444, baseEnd_2511444] using wordTrace_append hprefix tailTrace_2511444
  have hstable : (prefixWord ++ tailWord_2511444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511444).length < 2 ^ (prefixWord ++ tailWord_2511444).sum := by decide
  have hdescent : baseEnd_2511444 < baseStart_2511444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511472 : List Nat := [2, 1, 1, 1, 7, 1, 3, 6]
def baseStart_2511472 : Nat := 118140960795 + 2511472 * 2 ^ 59
def prefixEnd_2511472 : Nat := 4983230072969 + 3 ^ 40 * 2511472 * 2
def baseEnd_2511472 : Nat := 95525354541385413922219

theorem tailTrace_2511472 : CollatzResearch.WordTrace tailWord_2511472 prefixEnd_2511472 95525354541385413922219 := by
  unfold tailWord_2511472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45800454578686672057112335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61067272771582229409483113 45800454578686672057112335)
  ·
    refine ⟨68700681868030008085668503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45800454578686672057112335 68700681868030008085668503)
    ·
      refine ⟨103051022802045012128502755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68700681868030008085668503 103051022802045012128502755)
      ·
        refine ⟨154576534203067518192754133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103051022802045012128502755 154576534203067518192754133)
        ·
          refine ⟨3622887520384394957642675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 154576534203067518192754133 3622887520384394957642675)
          ·
            refine ⟨5434331280576592436464013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622887520384394957642675 5434331280576592436464013)
            ·
              refine ⟨2037874230216222163674005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5434331280576592436464013 2037874230216222163674005)
              ·
                refine ⟨95525354541385413922219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2037874230216222163674005 95525354541385413922219)
                ·
                  rfl

theorem cell22_2511472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_2511472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511472 prefixEnd_2511472 := by exact prefixLift 2511472
  have htrace : WordTrace (prefixWord ++ tailWord_2511472) baseStart_2511472 baseEnd_2511472 := by
    simpa [prefixWord, tailWord_2511472, baseEnd_2511472] using wordTrace_append hprefix tailTrace_2511472
  have hstable : (prefixWord ++ tailWord_2511472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511472).length < 2 ^ (prefixWord ++ tailWord_2511472).sum := by decide
  have hdescent : baseEnd_2511472 < baseStart_2511472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511474 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_2511474 : Nat := 118140960795 + 2511474 * 2 ^ 59
def prefixEnd_2511474 : Nat := 4983230072969 + 3 ^ 40 * 2511474 * 2
def baseEnd_2511474 : Nat := 859728875513341386749965

theorem tailTrace_2511474 : CollatzResearch.WordTrace tailWord_2511474 prefixEnd_2511474 859728875513341386749965 := by
  unfold tailWord_2511474
  simp only [CollatzResearch.WordTrace]
  refine ⟨22900245525841524613949369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61067321402244065637198317 22900245525841524613949369)
  ·
    refine ⟨17175184144381143460462027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22900245525841524613949369 17175184144381143460462027)
    ·
      refine ⟨25762776216571715190693041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17175184144381143460462027 25762776216571715190693041)
      ·
        refine ⟨19322082162428786393019781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25762776216571715190693041 19322082162428786393019781)
        ·
          refine ⟨3622890405455397448691209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19322082162428786393019781 3622890405455397448691209)
          ·
            refine ⟨2717167804091548086518407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3622890405455397448691209 2717167804091548086518407)
            ·
              refine ⟨4075751706137322129777611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717167804091548086518407 4075751706137322129777611)
              ·
                refine ⟨6113627559205983194666417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4075751706137322129777611 6113627559205983194666417)
                ·
                  refine ⟨4585220669404487395999813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6113627559205983194666417 4585220669404487395999813)
                  ·
                    refine ⟨859728875513341386749965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4585220669404487395999813 859728875513341386749965)
                    ·
                      rfl

theorem cell22_2511474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_2511474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511474 prefixEnd_2511474 := by exact prefixLift 2511474
  have htrace : WordTrace (prefixWord ++ tailWord_2511474) baseStart_2511474 baseEnd_2511474 := by
    simpa [prefixWord, tailWord_2511474, baseEnd_2511474] using wordTrace_append hprefix tailTrace_2511474
  have hstable : (prefixWord ++ tailWord_2511474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511474).length < 2 ^ (prefixWord ++ tailWord_2511474).sum := by decide
  have hdescent : baseEnd_2511474 < baseStart_2511474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511500 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_2511500 : Nat := 118140960795 + 2511500 * 2 ^ 59
def prefixEnd_2511500 : Nat := 4983230072969 + 3 ^ 40 * 2511500 * 2
def baseEnd_2511500 : Nat := 286579258614895328533295

theorem tailTrace_2511500 : CollatzResearch.WordTrace tailWord_2511500 prefixEnd_2511500 286579258614895328533295 := by
  unfold tailWord_2511500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45800965200635952448121977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61067953600847936597495969 45800965200635952448121977)
  ·
    refine ⟨34350723900476964336091483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45800965200635952448121977 34350723900476964336091483)
    ·
      refine ⟨51526085850715446504137225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34350723900476964336091483 51526085850715446504137225)
      ·
        refine ⟨38644564388036584878102919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51526085850715446504137225 38644564388036584878102919)
        ·
          refine ⟨57966846582054877317154379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38644564388036584878102919 57966846582054877317154379)
          ·
            refine ⟨86950269873082315975731569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57966846582054877317154379 86950269873082315975731569)
            ·
              refine ⟨65212702404811736981798677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86950269873082315975731569 65212702404811736981798677)
              ·
                refine ⟨3056845425225550171021813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65212702404811736981798677 3056845425225550171021813)
                ·
                  refine ⟨286579258614895328533295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056845425225550171021813 286579258614895328533295)
                  ·
                    rfl

theorem cell22_2511500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_2511500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511500 prefixEnd_2511500 := by exact prefixLift 2511500
  have htrace : WordTrace (prefixWord ++ tailWord_2511500) baseStart_2511500 baseEnd_2511500 := by
    simpa [prefixWord, tailWord_2511500, baseEnd_2511500] using wordTrace_append hprefix tailTrace_2511500
  have hstable : (prefixWord ++ tailWord_2511500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511500).length < 2 ^ (prefixWord ++ tailWord_2511500).sum := by decide
  have hdescent : baseEnd_2511500 < baseStart_2511500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511562 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_2511562 : Nat := 118140960795 + 2511562 * 2 ^ 59
def prefixEnd_2511562 : Nat := 4983230072969 + 3 ^ 40 * 2511562 * 2
def baseEnd_2511562 : Nat := 286586333237246163516565

theorem tailTrace_2511562 : CollatzResearch.WordTrace tailWord_2511562 prefixEnd_2511562 286586333237246163516565 := by
  unfold tailWord_2511562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22901047931761822371250235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61069461151364859656667293 22901047931761822371250235)
  ·
    refine ⟨34351571897642733556875353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22901047931761822371250235 34351571897642733556875353)
    ·
      refine ⟨25763678923232050167656515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34351571897642733556875353 25763678923232050167656515)
      ·
        refine ⟨38645518384848075251484773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25763678923232050167656515 38645518384848075251484773)
        ·
          refine ⟨7246034697159014109653395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38645518384848075251484773 7246034697159014109653395)
          ·
            refine ⟨10869052045738521164480093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246034697159014109653395 10869052045738521164480093)
            ·
              refine ⟨4075894517151945436680035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10869052045738521164480093 4075894517151945436680035)
              ·
                refine ⟨6113841775727918155020053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4075894517151945436680035 6113841775727918155020053)
                ·
                  refine ⟨286586333237246163516565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6113841775727918155020053 286586333237246163516565)
                  ·
                    rfl

theorem cell22_2511562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_2511562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511562 prefixEnd_2511562 := by exact prefixLift 2511562
  have htrace : WordTrace (prefixWord ++ tailWord_2511562) baseStart_2511562 baseEnd_2511562 := by
    simpa [prefixWord, tailWord_2511562, baseEnd_2511562] using wordTrace_append hprefix tailTrace_2511562
  have hstable : (prefixWord ++ tailWord_2511562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511562).length < 2 ^ (prefixWord ++ tailWord_2511562).sum := by decide
  have hdescent : baseEnd_2511562 < baseStart_2511562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511667 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 2, 5]
def baseStart_2511667 : Nat := 118140960795 + 2511667 * 2 ^ 59
def prefixEnd_2511667 : Nat := 4983230072969 + 3 ^ 40 * 2511667 * 2
def baseEnd_2511667 : Nat := 859794943357553216674373

theorem tailTrace_2511667 : CollatzResearch.WordTrace tailWord_2511667 prefixEnd_2511667 859794943357553216674373 := by
  unfold tailWord_2511667
  simp only [CollatzResearch.WordTrace]
  refine ⟨91608021391666892417573255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61072014261111261611715503 91608021391666892417573255)
  ·
    refine ⟨137412032087500338626359883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91608021391666892417573255 137412032087500338626359883)
    ·
      refine ⟨206118048131250507939539825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137412032087500338626359883 206118048131250507939539825)
      ·
        refine ⟨154588536098437880954654869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206118048131250507939539825 154588536098437880954654869)
        ·
          refine ⟨7246337629614275669749447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154588536098437880954654869 7246337629614275669749447)
          ·
            refine ⟨10869506444421413504624171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246337629614275669749447 10869506444421413504624171)
            ·
              refine ⟨16304259666632120256936257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10869506444421413504624171 16304259666632120256936257)
              ·
                refine ⟨12228194749974090192702193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16304259666632120256936257 12228194749974090192702193)
                ·
                  refine ⟨9171146062480567644526645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12228194749974090192702193 9171146062480567644526645)
                  ·
                    refine ⟨859794943357553216674373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9171146062480567644526645 859794943357553216674373)
                    ·
                      rfl

theorem cell22_2511667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_2511667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511667 prefixEnd_2511667 := by exact prefixLift 2511667
  have htrace : WordTrace (prefixWord ++ tailWord_2511667) baseStart_2511667 baseEnd_2511667 := by
    simpa [prefixWord, tailWord_2511667, baseEnd_2511667] using wordTrace_append hprefix tailTrace_2511667
  have hstable : (prefixWord ++ tailWord_2511667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511667).length < 2 ^ (prefixWord ++ tailWord_2511667).sum := by decide
  have hdescent : baseEnd_2511667 < baseStart_2511667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511669 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 5]
def baseStart_2511669 : Nat := 118140960795 + 2511669 * 2 ^ 59
def prefixEnd_2511669 : Nat := 4983230072969 + 3 ^ 40 * 2511669 * 2
def baseEnd_2511669 : Nat := 286598542666141959374789

theorem tailTrace_2511669 : CollatzResearch.WordTrace tailWord_2511669 prefixEnd_2511669 286598542666141959374789 := by
  unfold tailWord_2511669
  simp only [CollatzResearch.WordTrace]
  refine ⟨91608094337659646759146061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61072062891773097839430707 91608094337659646759146061)
  ·
    refine ⟨34353035376622367534679773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91608094337659646759146061 34353035376622367534679773)
    ·
      refine ⟨12882388266233387825504915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34353035376622367534679773 12882388266233387825504915)
      ·
        refine ⟨19323582399350081738257373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12882388266233387825504915 19323582399350081738257373)
        ·
          refine ⟨7246343399756280651846515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19323582399350081738257373 7246343399756280651846515)
          ·
            refine ⟨10869515099634420977769773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246343399756280651846515 10869515099634420977769773)
            ·
              refine ⟨4076068162362907866663665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10869515099634420977769773 4076068162362907866663665)
              ·
                refine ⟨3057051121772180899997749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4076068162362907866663665 3057051121772180899997749)
                ·
                  refine ⟨286598542666141959374789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057051121772180899997749 286598542666141959374789)
                  ·
                    rfl

theorem cell22_2511669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_2511669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511669 prefixEnd_2511669 := by exact prefixLift 2511669
  have htrace : WordTrace (prefixWord ++ tailWord_2511669) baseStart_2511669 baseEnd_2511669 := by
    simpa [prefixWord, tailWord_2511669, baseEnd_2511669] using wordTrace_append hprefix tailTrace_2511669
  have hstable : (prefixWord ++ tailWord_2511669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511669).length < 2 ^ (prefixWord ++ tailWord_2511669).sum := by decide
  have hdescent : baseEnd_2511669 < baseStart_2511669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511712 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_2511712 : Nat := 118140960795 + 2511712 * 2 ^ 59
def prefixEnd_2511712 : Nat := 4983230072969 + 3 ^ 40 * 2511712 * 2
def baseEnd_2511712 : Nat := 859810347777188099299235

theorem tailTrace_2511712 : CollatzResearch.WordTrace tailWord_2511712 prefixEnd_2511712 859810347777188099299235 := by
  unfold tailWord_2511712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45804831338251932551480695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61073108451002576735307593 45804831338251932551480695)
  ·
    refine ⟨68707247007377898827221043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45804831338251932551480695 68707247007377898827221043)
    ·
      refine ⟨103060870511066848240831565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68707247007377898827221043 103060870511066848240831565)
      ·
        refine ⟨38647826441650068090311837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103060870511066848240831565 38647826441650068090311837)
        ·
          refine ⟨14492934915618775533866939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38647826441650068090311837 14492934915618775533866939)
          ·
            refine ⟨21739402373428163300800409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14492934915618775533866939 21739402373428163300800409)
            ·
              refine ⟨16304551780071122475600307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21739402373428163300800409 16304551780071122475600307)
              ·
                refine ⟨24456827670106683713400461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16304551780071122475600307 24456827670106683713400461)
                ·
                  refine ⟨9171310376290006392525173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24456827670106683713400461 9171310376290006392525173)
                  ·
                    refine ⟨859810347777188099299235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9171310376290006392525173 859810347777188099299235)
                    ·
                      rfl

theorem cell22_2511712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_2511712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511712 prefixEnd_2511712 := by exact prefixLift 2511712
  have htrace : WordTrace (prefixWord ++ tailWord_2511712) baseStart_2511712 baseEnd_2511712 := by
    simpa [prefixWord, tailWord_2511712, baseEnd_2511712] using wordTrace_append hprefix tailTrace_2511712
  have hstable : (prefixWord ++ tailWord_2511712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511712).length < 2 ^ (prefixWord ++ tailWord_2511712).sum := by decide
  have hdescent : baseEnd_2511712 < baseStart_2511712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511729 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_2511729 : Nat := 118140960795 + 2511729 * 2 ^ 59
def prefixEnd_2511729 : Nat := 4983230072969 + 3 ^ 40 * 2511729 * 2
def baseEnd_2511729 : Nat := 859816167224605721624183

theorem tailTrace_2511729 : CollatzResearch.WordTrace tailWord_2511729 prefixEnd_2511729 859816167224605721624183 := by
  unfold tailWord_2511729
  simp only [CollatzResearch.WordTrace]
  refine ⟨91610282717442277006330241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61073521811628184670886827 91610282717442277006330241)
  ·
    refine ⟨68707712038081707754747681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91610282717442277006330241 68707712038081707754747681)
    ·
      refine ⟨51530784028561280816060761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68707712038081707754747681 51530784028561280816060761)
      ·
        refine ⟨38648088021420960612045571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51530784028561280816060761 38648088021420960612045571)
        ·
          refine ⟨57972132032131440918068357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38648088021420960612045571 57972132032131440918068357)
          ·
            refine ⟨10869774756024645172137817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57972132032131440918068357 10869774756024645172137817)
            ·
              refine ⟨8152331067018483879103363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10869774756024645172137817 8152331067018483879103363)
              ·
                refine ⟨12228496600527725818655045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8152331067018483879103363 12228496600527725818655045)
                ·
                  refine ⟨2292843112598948590997821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12228496600527725818655045 2292843112598948590997821)
                  ·
                    refine ⟨859816167224605721624183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2292843112598948590997821 859816167224605721624183)
                    ·
                      rfl

theorem cell22_2511729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_2511729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511729 prefixEnd_2511729 := by exact prefixLift 2511729
  have htrace : WordTrace (prefixWord ++ tailWord_2511729) baseStart_2511729 baseEnd_2511729 := by
    simpa [prefixWord, tailWord_2511729, baseEnd_2511729] using wordTrace_append hprefix tailTrace_2511729
  have hstable : (prefixWord ++ tailWord_2511729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511729).length < 2 ^ (prefixWord ++ tailWord_2511729).sum := by decide
  have hdescent : baseEnd_2511729 < baseStart_2511729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511879 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2511879 : Nat := 118140960795 + 2511879 * 2 ^ 59
def prefixEnd_2511879 : Nat := 4983230072969 + 3 ^ 40 * 2511879 * 2
def baseEnd_2511879 : Nat := 859867515290055330373723

theorem tailTrace_2511879 : CollatzResearch.WordTrace tailWord_2511879 prefixEnd_2511879 859867515290055330373723 := by
  unfold tailWord_2511879
  simp only [CollatzResearch.WordTrace]
  refine ⟨91615753666898852624290691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61077169111265901749527127 91615753666898852624290691)
  ·
    refine ⟨137423630500348278936436037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91615753666898852624290691 137423630500348278936436037)
    ·
      refine ⟨25766930718815302300581757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137423630500348278936436037 25766930718815302300581757)
      ·
        refine ⟨9662599019555738362718159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25766930718815302300581757 9662599019555738362718159)
        ·
          refine ⟨14493898529333607544077239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9662599019555738362718159 14493898529333607544077239)
          ·
            refine ⟨21740847794000411316115859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14493898529333607544077239 21740847794000411316115859)
            ·
              refine ⟨32611271691000616974173789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21740847794000411316115859 32611271691000616974173789)
              ·
                refine ⟨12229226884125231365315171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32611271691000616974173789 12229226884125231365315171)
                ·
                  refine ⟨18343840326187847047972757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12229226884125231365315171 18343840326187847047972757)
                  ·
                    refine ⟨859867515290055330373723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18343840326187847047972757 859867515290055330373723)
                    ·
                      rfl

theorem cell22_2511879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2511879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511879 prefixEnd_2511879 := by exact prefixLift 2511879
  have htrace : WordTrace (prefixWord ++ tailWord_2511879) baseStart_2511879 baseEnd_2511879 := by
    simpa [prefixWord, tailWord_2511879, baseEnd_2511879] using wordTrace_append hprefix tailTrace_2511879
  have hstable : (prefixWord ++ tailWord_2511879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511879).length < 2 ^ (prefixWord ++ tailWord_2511879).sum := by decide
  have hdescent : baseEnd_2511879 < baseStart_2511879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511883 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 4]
def baseStart_2511883 : Nat := 118140960795 + 2511883 * 2 ^ 59
def prefixEnd_2511883 : Nat := 4983230072969 + 3 ^ 40 * 2511883 * 2
def baseEnd_2511883 : Nat := 286622961523933551091237

theorem tailTrace_2511883 : CollatzResearch.WordTrace tailWord_2511883 prefixEnd_2511883 286622961523933551091237 := by
  unfold tailWord_2511883
  simp only [CollatzResearch.WordTrace]
  refine ⟨91615899558884361307436303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61077266372589574204957535 91615899558884361307436303)
  ·
    refine ⟨137423849338326541961154455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91615899558884361307436303 137423849338326541961154455)
    ·
      refine ⟨206135774007489812941731683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137423849338326541961154455 206135774007489812941731683)
      ·
        refine ⟨309203661011234719412597525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206135774007489812941731683 309203661011234719412597525)
        ·
          refine ⟨14493921609901627472465509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 309203661011234719412597525 14493921609901627472465509)
          ·
            refine ⟨2717610301856555151087283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14493921609901627472465509 2717610301856555151087283)
            ·
              refine ⟨4076415452784832726630925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717610301856555151087283 4076415452784832726630925)
              ·
                refine ⟨1528655794794312272486597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4076415452784832726630925 1528655794794312272486597)
                ·
                  refine ⟨286622961523933551091237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528655794794312272486597 286622961523933551091237)
                  ·
                    rfl

theorem cell22_2511883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 4].length) (baseStart_2511883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511883 prefixEnd_2511883 := by exact prefixLift 2511883
  have htrace : WordTrace (prefixWord ++ tailWord_2511883) baseStart_2511883 baseEnd_2511883 := by
    simpa [prefixWord, tailWord_2511883, baseEnd_2511883] using wordTrace_append hprefix tailTrace_2511883
  have hstable : (prefixWord ++ tailWord_2511883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511883).length < 2 ^ (prefixWord ++ tailWord_2511883).sum := by decide
  have hdescent : baseEnd_2511883 < baseStart_2511883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511896 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_2511896 : Nat := 118140960795 + 2511896 * 2 ^ 59
def prefixEnd_2511896 : Nat := 4983230072969 + 3 ^ 40 * 2511896 * 2
def baseEnd_2511896 : Nat := 859873334737472952698671

theorem tailTrace_2511896 : CollatzResearch.WordTrace tailWord_2511896 prefixEnd_2511896 859873334737472952698671 := by
  unfold tailWord_2511896
  simp only [CollatzResearch.WordTrace]
  refine ⟨45808186853918632263829771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61077582471891509685106361 45808186853918632263829771)
  ·
    refine ⟨68712280280877948395744657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45808186853918632263829771 68712280280877948395744657)
    ·
      refine ⟨51534210210658461296808493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68712280280877948395744657 51534210210658461296808493)
      ·
        refine ⟨19325328828996922986303185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51534210210658461296808493 19325328828996922986303185)
        ·
          refine ⟨14493996621747692239727389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19325328828996922986303185 14493996621747692239727389)
          ·
            refine ⟨5435248733155384589897771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14493996621747692239727389 5435248733155384589897771)
            ·
              refine ⟨8152873099733076884846657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435248733155384589897771 8152873099733076884846657)
              ·
                refine ⟨6114654824799807663634993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8152873099733076884846657 6114654824799807663634993)
                ·
                  refine ⟨4585991118599855747726245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6114654824799807663634993 4585991118599855747726245)
                  ·
                    refine ⟨859873334737472952698671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4585991118599855747726245 859873334737472952698671)
                    ·
                      rfl

theorem cell22_2511896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_2511896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511896 prefixEnd_2511896 := by exact prefixLift 2511896
  have htrace : WordTrace (prefixWord ++ tailWord_2511896) baseStart_2511896 baseEnd_2511896 := by
    simpa [prefixWord, tailWord_2511896, baseEnd_2511896] using wordTrace_append hprefix tailTrace_2511896
  have hstable : (prefixWord ++ tailWord_2511896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511896).length < 2 ^ (prefixWord ++ tailWord_2511896).sum := by decide
  have hdescent : baseEnd_2511896 < baseStart_2511896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511900 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 4]
def baseStart_2511900 : Nat := 118140960795 + 2511900 * 2 ^ 59
def prefixEnd_2511900 : Nat := 4983230072969 + 3 ^ 40 * 2511900 * 2
def baseEnd_2511900 : Nat := 286624901339739425199553

theorem tailTrace_2511900 : CollatzResearch.WordTrace tailWord_2511900 prefixEnd_2511900 286624901339739425199553 := by
  unfold tailWord_2511900
  simp only [CollatzResearch.WordTrace]
  refine ⟨45808259799911386605402577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61077679733215182140536769 45808259799911386605402577)
  ·
    refine ⟨34356194849933539954051933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45808259799911386605402577 34356194849933539954051933)
    ·
      refine ⟨12883573068725077482769475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34356194849933539954051933 12883573068725077482769475)
      ·
        refine ⟨19325359603087616224154213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12883573068725077482769475 19325359603087616224154213)
        ·
          refine ⟨3623504925578928042028915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19325359603087616224154213 3623504925578928042028915)
          ·
            refine ⟨5435257388368392063043373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623504925578928042028915 5435257388368392063043373)
            ·
              refine ⟨2038221520638147023641265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5435257388368392063043373 2038221520638147023641265)
              ·
                refine ⟨1528666140478610267730949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038221520638147023641265 1528666140478610267730949)
                ·
                  refine ⟨286624901339739425199553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528666140478610267730949 286624901339739425199553)
                  ·
                    rfl

theorem cell22_2511900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_2511900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511900 prefixEnd_2511900 := by exact prefixLift 2511900
  have htrace : WordTrace (prefixWord ++ tailWord_2511900) baseStart_2511900 baseEnd_2511900 := by
    simpa [prefixWord, tailWord_2511900, baseEnd_2511900] using wordTrace_append hprefix tailTrace_2511900
  have hstable : (prefixWord ++ tailWord_2511900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511900).length < 2 ^ (prefixWord ++ tailWord_2511900).sum := by decide
  have hdescent : baseEnd_2511900 < baseStart_2511900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511911 : List Nat := [1, 1, 7, 1, 1, 1, 1, 9]
def baseStart_2511911 : Nat := 118140960795 + 2511911 * 2 ^ 59
def prefixEnd_2511911 : Nat := 4983230072969 + 3 ^ 40 * 2511911 * 2
def baseEnd_2511911 : Nat := 95542052171557545952625

theorem tailTrace_2511911 : CollatzResearch.WordTrace tailWord_2511911 prefixEnd_2511911 95542052171557545952625 := by
  unfold tailWord_2511911
  simp only [CollatzResearch.WordTrace]
  refine ⟨91616920802782922089455587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61077947201855281392970391 91616920802782922089455587)
  ·
    refine ⟨137425381204174383134183381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91616920802782922089455587 137425381204174383134183381)
    ·
      refine ⟨3220907371972837104707423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 137425381204174383134183381 3220907371972837104707423)
      ·
        refine ⟨4831361057959255657061135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3220907371972837104707423 4831361057959255657061135)
        ·
          refine ⟨7247041586938883485591703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4831361057959255657061135 7247041586938883485591703)
          ·
            refine ⟨10870562380408325228387555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7247041586938883485591703 10870562380408325228387555)
            ·
              refine ⟨16305843570612487842581333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10870562380408325228387555 16305843570612487842581333)
              ·
                refine ⟨95542052171557545952625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16305843570612487842581333 95542052171557545952625)
                ·
                  rfl

theorem cell22_2511911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 9].length) (baseStart_2511911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511911 prefixEnd_2511911 := by exact prefixLift 2511911
  have htrace : WordTrace (prefixWord ++ tailWord_2511911) baseStart_2511911 baseEnd_2511911 := by
    simpa [prefixWord, tailWord_2511911, baseEnd_2511911] using wordTrace_append hprefix tailTrace_2511911
  have hstable : (prefixWord ++ tailWord_2511911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511911).length < 2 ^ (prefixWord ++ tailWord_2511911).sum := by decide
  have hdescent : baseEnd_2511911 < baseStart_2511911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511956 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2511956 : Nat := 118140960795 + 2511956 * 2 ^ 59
def prefixEnd_2511956 : Nat := 4983230072969 + 3 ^ 40 * 2511956 * 2
def baseEnd_2511956 : Nat := 286631291321217598732829

theorem tailTrace_2511956 : CollatzResearch.WordTrace tailWord_2511956 prefixEnd_2511956 286631291321217598732829 := by
  unfold tailWord_2511956
  simp only [CollatzResearch.WordTrace]
  refine ⟨45809281043809947387421861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61079041391746596516562481 45809281043809947387421861)
  ·
    refine ⟨8589240195714365135141599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45809281043809947387421861 8589240195714365135141599)
    ·
      refine ⟨12883860293571547702712399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8589240195714365135141599 12883860293571547702712399)
      ·
        refine ⟨19325790440357321554068599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12883860293571547702712399 19325790440357321554068599)
        ·
          refine ⟨28988685660535982331102899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19325790440357321554068599 28988685660535982331102899)
          ·
            refine ⟨43483028490803973496654349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28988685660535982331102899 43483028490803973496654349)
            ·
              refine ⟨16306135684051490061245381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43483028490803973496654349 16306135684051490061245381)
              ·
                refine ⟨3057400440759654386483509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16306135684051490061245381 3057400440759654386483509)
                ·
                  refine ⟨286631291321217598732829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057400440759654386483509 286631291321217598732829)
                  ·
                    rfl

theorem cell22_2511956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2511956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511956 prefixEnd_2511956 := by exact prefixLift 2511956
  have htrace : WordTrace (prefixWord ++ tailWord_2511956) baseStart_2511956 baseEnd_2511956 := by
    simpa [prefixWord, tailWord_2511956, baseEnd_2511956] using wordTrace_append hprefix tailTrace_2511956
  have hstable : (prefixWord ++ tailWord_2511956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511956).length < 2 ^ (prefixWord ++ tailWord_2511956).sum := by decide
  have hdescent : baseEnd_2511956 < baseStart_2511956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511986 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2511986 : Nat := 118140960795 + 2511986 * 2 ^ 59
def prefixEnd_2511986 : Nat := 4983230072969 + 3 ^ 40 * 2511986 * 2
def baseEnd_2511986 : Nat := 859904143576742717948395

theorem tailTrace_2511986 : CollatzResearch.WordTrace tailWord_2511986 prefixEnd_2511986 859904143576742717948395 := by
  unfold tailWord_2511986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22904914069377802474608953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61079770851674139932290541 22904914069377802474608953)
  ·
    refine ⟨17178685552033351855956715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22904914069377802474608953 17178685552033351855956715)
    ·
      refine ⟨25768028328050027783935073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17178685552033351855956715 25768028328050027783935073)
      ·
        refine ⟨19326021246037520837951305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25768028328050027783935073 19326021246037520837951305)
        ·
          refine ⟨14494515934528140628463479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19326021246037520837951305 14494515934528140628463479)
          ·
            refine ⟨21741773901792210942695219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14494515934528140628463479 21741773901792210942695219)
            ·
              refine ⟨32612660852688316414042829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21741773901792210942695219 32612660852688316414042829)
              ·
                refine ⟨12229747819758118655266061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32612660852688316414042829 12229747819758118655266061)
                ·
                  refine ⟨4586155432409294495724773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12229747819758118655266061 4586155432409294495724773)
                  ·
                    refine ⟨859904143576742717948395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586155432409294495724773 859904143576742717948395)
                    ·
                      rfl

theorem cell22_2511986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2511986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2511986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2511986 prefixEnd_2511986 := by exact prefixLift 2511986
  have htrace : WordTrace (prefixWord ++ tailWord_2511986) baseStart_2511986 baseEnd_2511986 := by
    simpa [prefixWord, tailWord_2511986, baseEnd_2511986] using wordTrace_append hprefix tailTrace_2511986
  have hstable : (prefixWord ++ tailWord_2511986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511986).length < 2 ^ (prefixWord ++ tailWord_2511986).sum := by decide
  have hdescent : baseEnd_2511986 < baseStart_2511986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512018 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_2512018 : Nat := 118140960795 + 2512018 * 2 ^ 59
def prefixEnd_2512018 : Nat := 4983230072969 + 3 ^ 40 * 2512018 * 2
def baseEnd_2512018 : Nat := 286638365943568433716099

theorem tailTrace_2512018 : CollatzResearch.WordTrace tailWord_2512018 prefixEnd_2512018 286638365943568433716099 := by
  unfold tailWord_2512018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22905205853348819840900177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61080548942263519575733805 22905205853348819840900177)
  ·
    refine ⟨17178904390011614880675133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22905205853348819840900177 17178904390011614880675133)
    ·
      refine ⟨6442089146254355580253175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17178904390011614880675133 6442089146254355580253175)
      ·
        refine ⟨9663133719381533370379763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442089146254355580253175 9663133719381533370379763)
        ·
          refine ⟨14494700579072300055569645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663133719381533370379763 14494700579072300055569645)
          ·
            refine ⟨5435512717152112520838617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14494700579072300055569645 5435512717152112520838617)
            ·
              refine ⟨4076634537864084390628963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5435512717152112520838617 4076634537864084390628963)
              ·
                refine ⟨6114951806796126585943445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4076634537864084390628963 6114951806796126585943445)
                ·
                  refine ⟨286638365943568433716099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6114951806796126585943445 286638365943568433716099)
                  ·
                    rfl

theorem cell22_2512018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_2512018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512018 prefixEnd_2512018 := by exact prefixLift 2512018
  have htrace : WordTrace (prefixWord ++ tailWord_2512018) baseStart_2512018 baseEnd_2512018 := by
    simpa [prefixWord, tailWord_2512018, baseEnd_2512018] using wordTrace_append hprefix tailTrace_2512018
  have hstable : (prefixWord ++ tailWord_2512018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512018).length < 2 ^ (prefixWord ++ tailWord_2512018).sum := by decide
  have hdescent : baseEnd_2512018 < baseStart_2512018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512065 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2512065 : Nat := 118140960795 + 2512065 * 2 ^ 59
def prefixEnd_2512065 : Nat := 4983230072969 + 3 ^ 40 * 2512065 * 2
def baseEnd_2512065 : Nat := 859931186891212845223153

theorem tailTrace_2512065 : CollatzResearch.WordTrace tailWord_2512065 prefixEnd_2512065 859931186891212845223153 := by
  unfold tailWord_2512065
  simp only [CollatzResearch.WordTrace]
  refine ⟨91622537644225006390561649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61081691762816670927041099 91622537644225006390561649)
  ·
    refine ⟨68716903233168754792921237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91622537644225006390561649 68716903233168754792921237)
    ·
      refine ⟨3221104839054785380918183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68716903233168754792921237 3221104839054785380918183)
      ·
        refine ⟨4831657258582178071377275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221104839054785380918183 4831657258582178071377275)
        ·
          refine ⟨7247485887873267107065913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4831657258582178071377275 7247485887873267107065913)
          ·
            refine ⟨5435614415904950330299435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7247485887873267107065913 5435614415904950330299435)
            ·
              refine ⟨8153421623857425495449153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435614415904950330299435 8153421623857425495449153)
              ·
                refine ⟨6115066217893069121586865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8153421623857425495449153 6115066217893069121586865)
                ·
                  refine ⟨4586299663419801841190149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6115066217893069121586865 4586299663419801841190149)
                  ·
                    refine ⟨859931186891212845223153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586299663419801841190149 859931186891212845223153)
                    ·
                      rfl

theorem cell22_2512065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2512065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512065 prefixEnd_2512065 := by exact prefixLift 2512065
  have htrace : WordTrace (prefixWord ++ tailWord_2512065) baseStart_2512065 baseEnd_2512065 := by
    simpa [prefixWord, tailWord_2512065, baseEnd_2512065] using wordTrace_append hprefix tailTrace_2512065
  have hstable : (prefixWord ++ tailWord_2512065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512065).length < 2 ^ (prefixWord ++ tailWord_2512065).sum := by decide
  have hdescent : baseEnd_2512065 < baseStart_2512065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512129 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2512129 : Nat := 118140960795 + 2512129 * 2 ^ 59
def prefixEnd_2512129 : Nat := 4983230072969 + 3 ^ 40 * 2512129 * 2
def baseEnd_2512129 : Nat := 859953095399138011622957

theorem tailTrace_2512129 : CollatzResearch.WordTrace tailWord_2512129 prefixEnd_2512129 859953095399138011622957 := by
  unfold tailWord_2512129
  simp only [CollatzResearch.WordTrace]
  refine ⟨91624871915993145320891441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61083247943995430213927627 91624871915993145320891441)
  ·
    refine ⟨68718653936994858990668581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91624871915993145320891441 68718653936994858990668581)
    ·
      refine ⟨12884747613186536060750359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68718653936994858990668581 12884747613186536060750359)
      ·
        refine ⟨19327121419779804091125539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12884747613186536060750359 19327121419779804091125539)
        ·
          refine ⟨28990682129669706136688309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19327121419779804091125539 28990682129669706136688309)
          ·
            refine ⟨2717876449656534950314529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28990682129669706136688309 2717876449656534950314529)
            ·
              refine ⟨2038407337242401212735897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717876449656534950314529 2038407337242401212735897)
              ·
                refine ⟨1528805502931800909551923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038407337242401212735897 1528805502931800909551923)
                ·
                  refine ⟨2293208254397701364327885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528805502931800909551923 2293208254397701364327885)
                  ·
                    refine ⟨859953095399138011622957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2293208254397701364327885 859953095399138011622957)
                    ·
                      rfl

theorem cell22_2512129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2512129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512129 prefixEnd_2512129 := by exact prefixLift 2512129
  have htrace : WordTrace (prefixWord ++ tailWord_2512129) baseStart_2512129 baseEnd_2512129 := by
    simpa [prefixWord, tailWord_2512129, baseEnd_2512129] using wordTrace_append hprefix tailTrace_2512129
  have hstable : (prefixWord ++ tailWord_2512129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512129).length < 2 ^ (prefixWord ++ tailWord_2512129).sum := by decide
  have hdescent : baseEnd_2512129 < baseStart_2512129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512215 : List Nat := [1, 1, 3, 2, 3, 4, 2, 6]
def baseStart_2512215 : Nat := 118140960795 + 2512215 * 2 ^ 59
def prefixEnd_2512215 : Nat := 4983230072969 + 3 ^ 40 * 2512215 * 2
def baseEnd_2512215 : Nat := 95553614995184717108077

theorem tailTrace_2512215 : CollatzResearch.WordTrace tailWord_2512215 prefixEnd_2512215 95553614995184717108077 := by
  unfold tailWord_2512215
  simp only [CollatzResearch.WordTrace]
  refine ⟨91628008593681582008522099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61085339062454388005681399 91628008593681582008522099)
  ·
    refine ⟨137442012890522373012783149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91628008593681582008522099 137442012890522373012783149)
    ·
      refine ⟨51540754833945889879793681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137442012890522373012783149 51540754833945889879793681)
      ·
        refine ⟨38655566125459417409845261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51540754833945889879793681 38655566125459417409845261)
        ·
          refine ⟨14495837297047281528691973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38655566125459417409845261 14495837297047281528691973)
          ·
            refine ⟨2717969493196365286629745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14495837297047281528691973 2717969493196365286629745)
            ·
              refine ⟨2038477119897273964972309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717969493196365286629745 2038477119897273964972309)
              ·
                refine ⟨95553614995184717108077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2038477119897273964972309 95553614995184717108077)
                ·
                  rfl

theorem cell22_2512215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 6].length) (baseStart_2512215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512215 prefixEnd_2512215 := by exact prefixLift 2512215
  have htrace : WordTrace (prefixWord ++ tailWord_2512215) baseStart_2512215 baseEnd_2512215 := by
    simpa [prefixWord, tailWord_2512215, baseEnd_2512215] using wordTrace_append hprefix tailTrace_2512215
  have hstable : (prefixWord ++ tailWord_2512215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512215).length < 2 ^ (prefixWord ++ tailWord_2512215).sum := by decide
  have hdescent : baseEnd_2512215 < baseStart_2512215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512260 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_2512260 : Nat := 118140960795 + 2512260 * 2 ^ 59
def prefixEnd_2512260 : Nat := 4983230072969 + 3 ^ 40 * 2512260 * 2
def baseEnd_2512260 : Nat := 286665979792099112199185

theorem tailTrace_2512260 : CollatzResearch.WordTrace tailWord_2512260 prefixEnd_2512260 286665979792099112199185 := by
  unfold tailWord_2512260
  simp only [CollatzResearch.WordTrace]
  refine ⟨45814824939259277346955117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61086433252345703129273489 45814824939259277346955117)
  ·
    refine ⟨17180559352222229005108169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45814824939259277346955117 17180559352222229005108169)
    ·
      refine ⟨12885419514166671753831127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17180559352222229005108169 12885419514166671753831127)
      ·
        refine ⟨19328129271250007630746691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12885419514166671753831127 19328129271250007630746691)
        ·
          refine ⟨28992193906875011446120037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19328129271250007630746691 28992193906875011446120037)
          ·
            refine ⟨5436036357539064646147507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28992193906875011446120037 5436036357539064646147507)
            ·
              refine ⟨8154054536308596969221261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436036357539064646147507 8154054536308596969221261)
              ·
                refine ⟨3057770451115723863457973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8154054536308596969221261 3057770451115723863457973)
                ·
                  refine ⟨286665979792099112199185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057770451115723863457973 286665979792099112199185)
                  ·
                    rfl

theorem cell22_2512260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_2512260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512260 prefixEnd_2512260 := by exact prefixLift 2512260
  have htrace : WordTrace (prefixWord ++ tailWord_2512260) baseStart_2512260 baseEnd_2512260 := by
    simpa [prefixWord, tailWord_2512260, baseEnd_2512260] using wordTrace_append hprefix tailTrace_2512260
  have hstable : (prefixWord ++ tailWord_2512260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512260).length < 2 ^ (prefixWord ++ tailWord_2512260).sum := by decide
  have hdescent : baseEnd_2512260 < baseStart_2512260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512273 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_2512273 : Nat := 118140960795 + 2512273 * 2 ^ 59
def prefixEnd_2512273 : Nat := 4983230072969 + 3 ^ 40 * 2512273 * 2
def baseEnd_2512273 : Nat := 860002389541969636022515

theorem tailTrace_2512273 : CollatzResearch.WordTrace tailWord_2512273 prefixEnd_2512273 860002389541969636022515 := by
  unfold tailWord_2512273
  simp only [CollatzResearch.WordTrace]
  refine ⟨91630124027471457914133473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61086749351647638609422315 91630124027471457914133473)
  ·
    refine ⟨68722593020603593435600105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91630124027471457914133473 68722593020603593435600105)
    ·
      refine ⟨51541944765452695076700079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68722593020603593435600105 51541944765452695076700079)
      ·
        refine ⟨77312917148179042615050119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51541944765452695076700079 77312917148179042615050119)
        ·
          refine ⟨115969375722268563922575179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77312917148179042615050119 115969375722268563922575179)
          ·
            refine ⟨173954063583402845883862769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115969375722268563922575179 173954063583402845883862769)
            ·
              refine ⟨130465547687552134412897077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173954063583402845883862769 130465547687552134412897077)
              ·
                refine ⟨12231145095708012601209101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130465547687552134412897077 12231145095708012601209101)
                ·
                  refine ⟨4586679410890504725453413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12231145095708012601209101 4586679410890504725453413)
                  ·
                    refine ⟨860002389541969636022515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586679410890504725453413 860002389541969636022515)
                    ·
                      rfl

theorem cell22_2512273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_2512273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512273 prefixEnd_2512273 := by exact prefixLift 2512273
  have htrace : WordTrace (prefixWord ++ tailWord_2512273) baseStart_2512273 baseEnd_2512273 := by
    simpa [prefixWord, tailWord_2512273, baseEnd_2512273] using wordTrace_append hprefix tailTrace_2512273
  have hstable : (prefixWord ++ tailWord_2512273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512273).length < 2 ^ (prefixWord ++ tailWord_2512273).sum := by decide
  have hdescent : baseEnd_2512273 < baseStart_2512273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512335 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 2, 4]
def baseStart_2512335 : Nat := 118140960795 + 2512335 * 2 ^ 59
def prefixEnd_2512335 : Nat := 4983230072969 + 3 ^ 40 * 2512335 * 2
def baseEnd_2512335 : Nat := 860023613409022140972325

theorem tailTrace_2512335 : CollatzResearch.WordTrace tailWord_2512335 prefixEnd_2512335 860023613409022140972325 := by
  unfold tailWord_2512335
  simp only [CollatzResearch.WordTrace]
  refine ⟨91632385353246842502890459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61088256902164561668593639 91632385353246842502890459)
  ·
    refine ⟨137448578029870263754335689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91632385353246842502890459 137448578029870263754335689)
    ·
      refine ⟨103086433522402697815751767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137448578029870263754335689 103086433522402697815751767)
      ·
        refine ⟨154629650283604046723627651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103086433522402697815751767 154629650283604046723627651)
        ·
          refine ⟨231944475425406070085441477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154629650283604046723627651 231944475425406070085441477)
          ·
            refine ⟨43489589142263638141020277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231944475425406070085441477 43489589142263638141020277)
            ·
              refine ⟨4077148982087216075720651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43489589142263638141020277 4077148982087216075720651)
              ·
                refine ⟨6115723473130824113580977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077148982087216075720651 6115723473130824113580977)
                ·
                  refine ⟨4586792604848118085185733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6115723473130824113580977 4586792604848118085185733)
                  ·
                    refine ⟨860023613409022140972325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586792604848118085185733 860023613409022140972325)
                    ·
                      rfl

theorem cell22_2512335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_2512335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512335 prefixEnd_2512335 := by exact prefixLift 2512335
  have htrace : WordTrace (prefixWord ++ tailWord_2512335) baseStart_2512335 baseEnd_2512335 := by
    simpa [prefixWord, tailWord_2512335, baseEnd_2512335] using wordTrace_append hprefix tailTrace_2512335
  have hstable : (prefixWord ++ tailWord_2512335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512335).length < 2 ^ (prefixWord ++ tailWord_2512335).sum := by decide
  have hdescent : baseEnd_2512335 < baseStart_2512335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512363 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 2, 6]
def baseStart_2512363 : Nat := 118140960795 + 2512363 * 2 ^ 59
def prefixEnd_2512363 : Nat := 4983230072969 + 3 ^ 40 * 2512363 * 2
def baseEnd_2512363 : Nat := 860033198381239401272239

theorem tailTrace_2512363 : CollatzResearch.WordTrace tailWord_2512363 prefixEnd_2512363 860033198381239401272239 := by
  unfold tailWord_2512363
  simp only [CollatzResearch.WordTrace]
  refine ⟨91633406597145403284909743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61088937731430268856606495 91633406597145403284909743)
  ·
    refine ⟨137450109895718104927364615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91633406597145403284909743 137450109895718104927364615)
    ·
      refine ⟨206175164843577157391046923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137450109895718104927364615 206175164843577157391046923)
      ·
        refine ⟨309262747265365736086570385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206175164843577157391046923 309262747265365736086570385)
        ·
          refine ⟨231947060449024302064927789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309262747265365736086570385 231947060449024302064927789)
          ·
            refine ⟨86980147668384113274347921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231947060449024302064927789 86980147668384113274347921)
            ·
              refine ⟨65235110751288084955760941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86980147668384113274347921 65235110751288084955760941)
              ·
                refine ⟨24463166531733031858410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65235110751288084955760941 24463166531733031858410353)
                ·
                  refine ⟨18347374898799773893807765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24463166531733031858410353 18347374898799773893807765)
                  ·
                    refine ⟨860033198381239401272239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18347374898799773893807765 860033198381239401272239)
                    ·
                      rfl

theorem cell22_2512363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_2512363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512363 prefixEnd_2512363 := by exact prefixLift 2512363
  have htrace : WordTrace (prefixWord ++ tailWord_2512363) baseStart_2512363 baseEnd_2512363 := by
    simpa [prefixWord, tailWord_2512363, baseEnd_2512363] using wordTrace_append hprefix tailTrace_2512363
  have hstable : (prefixWord ++ tailWord_2512363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512363).length < 2 ^ (prefixWord ++ tailWord_2512363).sum := by decide
  have hdescent : baseEnd_2512363 < baseStart_2512363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512390 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2512390 : Nat := 118140960795 + 2512390 * 2 ^ 59
def prefixEnd_2512390 : Nat := 4983230072969 + 3 ^ 40 * 2512390 * 2
def baseEnd_2512390 : Nat := 286680813677673443615719

theorem tailTrace_2512390 : CollatzResearch.WordTrace tailWord_2512390 prefixEnd_2512390 286680813677673443615719 := by
  unfold tailWord_2512390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863574730251487090504457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61089594245365057930761749 2863574730251487090504457)
  ·
    refine ⟨2147681047688615317878343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2863574730251487090504457 2147681047688615317878343)
    ·
      refine ⟨3221521571532922976817515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147681047688615317878343 3221521571532922976817515)
      ·
        refine ⟨4832282357299384465226273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221521571532922976817515 4832282357299384465226273)
        ·
          refine ⟨3624211767974538348919705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4832282357299384465226273 3624211767974538348919705)
          ·
            refine ⟨2718158825980903761689779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3624211767974538348919705 2718158825980903761689779)
            ·
              refine ⟨4077238238971355642534669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718158825980903761689779 4077238238971355642534669)
              ·
                refine ⟨1528964339614258365950501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4077238238971355642534669 1528964339614258365950501)
                ·
                  refine ⟨286680813677673443615719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1528964339614258365950501 286680813677673443615719)
                  ·
                    rfl

theorem cell22_2512390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2512390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512390 prefixEnd_2512390 := by exact prefixLift 2512390
  have htrace : WordTrace (prefixWord ++ tailWord_2512390) baseStart_2512390 baseEnd_2512390 := by
    simpa [prefixWord, tailWord_2512390, baseEnd_2512390] using wordTrace_append hprefix tailTrace_2512390
  have hstable : (prefixWord ++ tailWord_2512390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512390).length < 2 ^ (prefixWord ++ tailWord_2512390).sum := by decide
  have hdescent : baseEnd_2512390 < baseStart_2512390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512517 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_2512517 : Nat := 118140960795 + 2512517 * 2 ^ 59
def prefixEnd_2512517 : Nat := 4983230072969 + 3 ^ 40 * 2512517 * 2
def baseEnd_2512517 : Nat := 860085915728434332921767

theorem tailTrace_2512517 : CollatzResearch.WordTrace tailWord_2512517 prefixEnd_2512517 860085915728434332921767 := by
  unfold tailWord_2512517
  simp only [CollatzResearch.WordTrace]
  refine ⟨91639023438587487586015805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61092682292391658390677203 91639023438587487586015805)
  ·
    refine ⟨34364633789470307844755927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91639023438587487586015805 34364633789470307844755927)
    ·
      refine ⟨51546950684205461767133891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34364633789470307844755927 51546950684205461767133891)
      ·
        refine ⟨77320426026308192650700837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51546950684205461767133891 77320426026308192650700837)
        ·
          refine ⟨14497579879932786122006407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77320426026308192650700837 14497579879932786122006407)
          ·
            refine ⟨21746369819899179183009611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14497579879932786122006407 21746369819899179183009611)
            ·
              refine ⟨32619554729848768774514417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21746369819899179183009611 32619554729848768774514417)
              ·
                refine ⟨24464666047386576580885813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32619554729848768774514417 24464666047386576580885813)
                ·
                  refine ⟨2293562441942491554458045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24464666047386576580885813 2293562441942491554458045)
                  ·
                    refine ⟨860085915728434332921767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2293562441942491554458045 860085915728434332921767)
                    ·
                      rfl

theorem cell22_2512517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_2512517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512517 prefixEnd_2512517 := by exact prefixLift 2512517
  have htrace : WordTrace (prefixWord ++ tailWord_2512517) baseStart_2512517 baseEnd_2512517 := by
    simpa [prefixWord, tailWord_2512517, baseEnd_2512517] using wordTrace_append hprefix tailTrace_2512517
  have hstable : (prefixWord ++ tailWord_2512517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512517).length < 2 ^ (prefixWord ++ tailWord_2512517).sum := by decide
  have hdescent : baseEnd_2512517 < baseStart_2512517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512598 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2512598 : Nat := 118140960795 + 2512598 * 2 ^ 59
def prefixEnd_2512598 : Nat := 4983230072969 + 3 ^ 40 * 2512598 * 2
def baseEnd_2512598 : Nat := 286704547894592373882173

theorem tailTrace_2512598 : CollatzResearch.WordTrace tailWord_2512598 prefixEnd_2512598 286704547894592373882173 := by
  unfold tailWord_2512598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727623609455877401232153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61094651834196025613142965 5727623609455877401232153)
  ·
    refine ⟨4295717707091908050924115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5727623609455877401232153 4295717707091908050924115)
    ·
      refine ⟨6443576560637862076386173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295717707091908050924115 6443576560637862076386173)
      ·
        refine ⟨2416341210239198278644815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6443576560637862076386173 2416341210239198278644815)
        ·
          refine ⟨3624511815358797417967223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416341210239198278644815 3624511815358797417967223)
          ·
            refine ⟨5436767723038196126950835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624511815358797417967223 5436767723038196126950835)
            ·
              refine ⟨8155151584557294190426253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436767723038196126950835 8155151584557294190426253)
              ·
                refine ⟨3058181844208985321409845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8155151584557294190426253 3058181844208985321409845)
                ·
                  refine ⟨286704547894592373882173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3058181844208985321409845 286704547894592373882173)
                  ·
                    rfl

theorem cell22_2512598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2512598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512598 prefixEnd_2512598 := by exact prefixLift 2512598
  have htrace : WordTrace (prefixWord ++ tailWord_2512598) baseStart_2512598 baseEnd_2512598 := by
    simpa [prefixWord, tailWord_2512598, baseEnd_2512598] using wordTrace_append hprefix tailTrace_2512598
  have hstable : (prefixWord ++ tailWord_2512598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512598).length < 2 ^ (prefixWord ++ tailWord_2512598).sum := by decide
  have hdescent : baseEnd_2512598 < baseStart_2512598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512607 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 1, 5]
def baseStart_2512607 : Nat := 118140960795 + 2512607 * 2 ^ 59
def prefixEnd_2512607 : Nat := 4983230072969 + 3 ^ 40 * 2512607 * 2
def baseEnd_2512607 : Nat := 860116724567704098171491

theorem tailTrace_2512607 : CollatzResearch.WordTrace tailWord_2512607 prefixEnd_2512607 860116724567704098171491 := by
  unfold tailWord_2512607
  simp only [CollatzResearch.WordTrace]
  refine ⟨91642306008261432956792075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61094870672174288637861383 91642306008261432956792075)
  ·
    refine ⟨137463459012392149435188113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91642306008261432956792075 137463459012392149435188113)
    ·
      refine ⟨103097594259294112076391085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137463459012392149435188113 103097594259294112076391085)
      ·
        refine ⟨38661597847235292028646657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103097594259294112076391085 38661597847235292028646657)
        ·
          refine ⟨28996198385426469021484993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38661597847235292028646657 28996198385426469021484993)
          ·
            refine ⟨21747148789069851766113745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28996198385426469021484993 21747148789069851766113745)
            ·
              refine ⟨16310361591802388824585309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21747148789069851766113745 16310361591802388824585309)
              ·
                refine ⟨6116385596925895809219491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16310361591802388824585309 6116385596925895809219491)
                ·
                  refine ⟨9174578395388843713829237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6116385596925895809219491 9174578395388843713829237)
                  ·
                    refine ⟨860116724567704098171491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9174578395388843713829237 860116724567704098171491)
                    ·
                      rfl

theorem cell22_2512607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_2512607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512607 prefixEnd_2512607 := by exact prefixLift 2512607
  have htrace : WordTrace (prefixWord ++ tailWord_2512607) baseStart_2512607 baseEnd_2512607 := by
    simpa [prefixWord, tailWord_2512607, baseEnd_2512607] using wordTrace_append hprefix tailTrace_2512607
  have hstable : (prefixWord ++ tailWord_2512607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512607).length < 2 ^ (prefixWord ++ tailWord_2512607).sum := by decide
  have hdescent : baseEnd_2512607 < baseStart_2512607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512658 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2512658 : Nat := 118140960795 + 2512658 * 2 ^ 59
def prefixEnd_2512658 : Nat := 4983230072969 + 3 ^ 40 * 2512658 * 2
def baseEnd_2512658 : Nat := 860134182909956965146335

theorem tailTrace_2512658 : CollatzResearch.WordTrace tailWord_2512658 prefixEnd_2512658 860134182909956965146335 := by
  unfold tailWord_2512658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22911041532769167166724657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61096110754051112444599085 22911041532769167166724657)
  ·
    refine ⟨17183281149576875375043493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22911041532769167166724657 17183281149576875375043493)
    ·
      refine ⟨3221865215545664132820655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17183281149576875375043493 3221865215545664132820655)
      ·
        refine ⟨4832797823318496199230983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221865215545664132820655 4832797823318496199230983)
        ·
          refine ⟨7249196734977744298846475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832797823318496199230983 7249196734977744298846475)
          ·
            refine ⟨10873795102466616448269713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7249196734977744298846475 10873795102466616448269713)
            ·
              refine ⟨8155346326849962336202285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10873795102466616448269713 8155346326849962336202285)
              ·
                refine ⟨3058254872568735876075857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8155346326849962336202285 3058254872568735876075857)
                ·
                  refine ⟨2293691154426551907056893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058254872568735876075857 2293691154426551907056893)
                  ·
                    refine ⟨860134182909956965146335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2293691154426551907056893 860134182909956965146335)
                    ·
                      rfl

theorem cell22_2512658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2512658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512658 prefixEnd_2512658 := by exact prefixLift 2512658
  have htrace : WordTrace (prefixWord ++ tailWord_2512658) baseStart_2512658 baseEnd_2512658 := by
    simpa [prefixWord, tailWord_2512658, baseEnd_2512658] using wordTrace_append hprefix tailTrace_2512658
  have hstable : (prefixWord ++ tailWord_2512658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512658).length < 2 ^ (prefixWord ++ tailWord_2512658).sum := by decide
  have hdescent : baseEnd_2512658 < baseStart_2512658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512791 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 2, 4]
def baseStart_2512791 : Nat := 118140960795 + 2512791 * 2 ^ 59
def prefixEnd_2512791 : Nat := 4983230072969 + 3 ^ 40 * 2512791 * 2
def baseEnd_2512791 : Nat := 860179711527988951570927

theorem tailTrace_2512791 : CollatzResearch.WordTrace tailWord_2512791 prefixEnd_2512791 860179711527988951570927 := by
  unfold tailWord_2512791
  simp only [CollatzResearch.WordTrace]
  refine ⟨91649017039594832381490227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61099344693063221587660151 91649017039594832381490227)
  ·
    refine ⟨137473525559392248572235341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91649017039594832381490227 137473525559392248572235341)
    ·
      refine ⟨51552572084772093214588253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137473525559392248572235341 51552572084772093214588253)
      ·
        refine ⟨19332214531789534955470595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51552572084772093214588253 19332214531789534955470595)
        ·
          refine ⟨28998321797684302433205893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19332214531789534955470595 28998321797684302433205893)
          ·
            refine ⟨5437185337065806706226105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28998321797684302433205893 5437185337065806706226105)
            ·
              refine ⟨4077889002799355029669579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437185337065806706226105 4077889002799355029669579)
              ·
                refine ⟨6116833504199032544504369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077889002799355029669579 6116833504199032544504369)
                ·
                  refine ⟨4587625128149274408378277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116833504199032544504369 4587625128149274408378277)
                  ·
                    refine ⟨860179711527988951570927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4587625128149274408378277 860179711527988951570927)
                    ·
                      rfl

theorem cell22_2512791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_2512791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512791 prefixEnd_2512791 := by exact prefixLift 2512791
  have htrace : WordTrace (prefixWord ++ tailWord_2512791) baseStart_2512791 baseEnd_2512791 := by
    simpa [prefixWord, tailWord_2512791, baseEnd_2512791] using wordTrace_append hprefix tailTrace_2512791
  have hstable : (prefixWord ++ tailWord_2512791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512791).length < 2 ^ (prefixWord ++ tailWord_2512791).sum := by decide
  have hdescent : baseEnd_2512791 < baseStart_2512791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512930 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_2512930 : Nat := 118140960795 + 2512930 * 2 ^ 59
def prefixEnd_2512930 : Nat := 4983230072969 + 3 ^ 40 * 2512930 * 2
def baseEnd_2512930 : Nat := 286742431356212974115167

theorem tailTrace_2512930 : CollatzResearch.WordTrace tailWord_2512930 prefixEnd_2512930 286742431356212974115167 := by
  unfold tailWord_2512930
  simp only [CollatzResearch.WordTrace]
  refine ⟨22913521696522814780200061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61102724524060839413866829 22913521696522814780200061)
  ·
    refine ⟨8592570636196055542575023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22913521696522814780200061 8592570636196055542575023)
    ·
      refine ⟨12888855954294083313862535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8592570636196055542575023 12888855954294083313862535)
      ·
        refine ⟨19333283931441124970793803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12888855954294083313862535 19333283931441124970793803)
        ·
          refine ⟨28999925897161687456190705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19333283931441124970793803 28999925897161687456190705)
          ·
            refine ⟨21749944422871265592143029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28999925897161687456190705 21749944422871265592143029)
            ·
              refine ⟨2039057289644181149263409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21749944422871265592143029 2039057289644181149263409)
              ·
                refine ⟨1529292967233135861947557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2039057289644181149263409 1529292967233135861947557)
                ·
                  refine ⟨286742431356212974115167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529292967233135861947557 286742431356212974115167)
                  ·
                    rfl

theorem cell22_2512930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_2512930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512930 prefixEnd_2512930 := by exact prefixLift 2512930
  have htrace : WordTrace (prefixWord ++ tailWord_2512930) baseStart_2512930 baseEnd_2512930 := by
    simpa [prefixWord, tailWord_2512930, baseEnd_2512930] using wordTrace_append hprefix tailTrace_2512930
  have hstable : (prefixWord ++ tailWord_2512930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512930).length < 2 ^ (prefixWord ++ tailWord_2512930).sum := by decide
  have hdescent : baseEnd_2512930 < baseStart_2512930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512939 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 7]
def baseStart_2512939 : Nat := 118140960795 + 2512939 * 2 ^ 59
def prefixEnd_2512939 : Nat := 4983230072969 + 3 ^ 40 * 2512939 * 2
def baseEnd_2512939 : Nat := 860230374952565898870473

theorem tailTrace_2512939 : CollatzResearch.WordTrace tailWord_2512939 prefixEnd_2512939 860230374952565898870473 := by
  unfold tailWord_2512939
  simp only [CollatzResearch.WordTrace]
  refine ⟨91654415043058653657877871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61102943362039102438585247 91654415043058653657877871)
  ·
    refine ⟨137481622564587980486816807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91654415043058653657877871 137481622564587980486816807)
    ·
      refine ⟨206222433846881970730225211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137481622564587980486816807 206222433846881970730225211)
      ·
        refine ⟨309333650770322956095337817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206222433846881970730225211 309333650770322956095337817)
        ·
          refine ⟨232000238077742217071503363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309333650770322956095337817 232000238077742217071503363)
          ·
            refine ⟨348000357116613325607255045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232000238077742217071503363 348000357116613325607255045)
            ·
              refine ⟨65250066959364998551360321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 348000357116613325607255045 65250066959364998551360321)
              ·
                refine ⟨48937550219523748913520241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65250066959364998551360321 48937550219523748913520241)
                ·
                  refine ⟨36703162664642811685140181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48937550219523748913520241 36703162664642811685140181)
                  ·
                    refine ⟨860230374952565898870473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36703162664642811685140181 860230374952565898870473)
                    ·
                      rfl

theorem cell22_2512939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_2512939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512939 prefixEnd_2512939 := by exact prefixLift 2512939
  have htrace : WordTrace (prefixWord ++ tailWord_2512939) baseStart_2512939 baseEnd_2512939 := by
    simpa [prefixWord, tailWord_2512939, baseEnd_2512939] using wordTrace_append hprefix tailTrace_2512939
  have hstable : (prefixWord ++ tailWord_2512939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512939).length < 2 ^ (prefixWord ++ tailWord_2512939).sum := by decide
  have hdescent : baseEnd_2512939 < baseStart_2512939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512945 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 2, 3]
def baseStart_2512945 : Nat := 118140960795 + 2512945 * 2 ^ 59
def prefixEnd_2512945 : Nat := 4983230072969 + 3 ^ 40 * 2512945 * 2
def baseEnd_2512945 : Nat := 860232428875183883220455

theorem tailTrace_2512945 : CollatzResearch.WordTrace tailWord_2512945 prefixEnd_2512945 860232428875183883220455 := by
  unfold tailWord_2512945
  simp only [CollatzResearch.WordTrace]
  refine ⟨91654633881036916682596289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61103089254024611121730859 91654633881036916682596289)
  ·
    refine ⟨68740975410777687511947217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91654633881036916682596289 68740975410777687511947217)
    ·
      refine ⟨51555731558083265633960413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68740975410777687511947217 51555731558083265633960413)
      ·
        refine ⟨19333399334281224612735155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51555731558083265633960413 19333399334281224612735155)
        ·
          refine ⟨29000099001421836919102733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19333399334281224612735155 29000099001421836919102733)
          ·
            refine ⟨10875037125533188844663525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29000099001421836919102733 10875037125533188844663525)
            ·
              refine ⟨2039069461037472908374411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10875037125533188844663525 2039069461037472908374411)
              ·
                refine ⟨3058604191556209362561617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039069461037472908374411 3058604191556209362561617)
                ·
                  refine ⟨2293953143667157021921213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058604191556209362561617 2293953143667157021921213)
                  ·
                    refine ⟨860232428875183883220455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2293953143667157021921213 860232428875183883220455)
                    ·
                      rfl

theorem cell22_2512945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_2512945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2512945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2512945 prefixEnd_2512945 := by exact prefixLift 2512945
  have htrace : WordTrace (prefixWord ++ tailWord_2512945) baseStart_2512945 baseEnd_2512945 := by
    simpa [prefixWord, tailWord_2512945, baseEnd_2512945] using wordTrace_append hprefix tailTrace_2512945
  have hstable : (prefixWord ++ tailWord_2512945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512945).length < 2 ^ (prefixWord ++ tailWord_2512945).sum := by decide
  have hdescent : baseEnd_2512945 < baseStart_2512945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513001 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_2513001 : Nat := 118140960795 + 2513001 * 2 ^ 59
def prefixEnd_2513001 : Nat := 4983230072969 + 3 ^ 40 * 2513001 * 2
def baseEnd_2513001 : Nat := 860251598819618403820283

theorem tailTrace_2513001 : CollatzResearch.WordTrace tailWord_2513001 prefixEnd_2513001 860251598819618403820283 := by
  unfold tailWord_2513001
  simp only [CollatzResearch.WordTrace]
  refine ⟨91656676368834038246634857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61104450912556025497756571 91656676368834038246634857)
  ·
    refine ⟨68742507276625528684976143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91656676368834038246634857 68742507276625528684976143)
    ·
      refine ⟨103113760914938293027464215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68742507276625528684976143 103113760914938293027464215)
      ·
        refine ⟨154670641372407439541196323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103113760914938293027464215 154670641372407439541196323)
        ·
          refine ⟨232005962058611159311794485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154670641372407439541196323 232005962058611159311794485)
          ·
            refine ⟨21750558942994796185480733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232005962058611159311794485 21750558942994796185480733)
            ·
              refine ⟨8156459603623048569555275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21750558942994796185480733 8156459603623048569555275)
              ·
                refine ⟨12234689405434572854332913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8156459603623048569555275 12234689405434572854332913)
                ·
                  refine ⟨9176017054075929640749685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12234689405434572854332913 9176017054075929640749685)
                  ·
                    refine ⟨860251598819618403820283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9176017054075929640749685 860251598819618403820283)
                    ·
                      rfl

theorem cell22_2513001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_2513001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513001 prefixEnd_2513001 := by exact prefixLift 2513001
  have htrace : WordTrace (prefixWord ++ tailWord_2513001) baseStart_2513001 baseEnd_2513001 := by
    simpa [prefixWord, tailWord_2513001, baseEnd_2513001] using wordTrace_append hprefix tailTrace_2513001
  have hstable : (prefixWord ++ tailWord_2513001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513001).length < 2 ^ (prefixWord ++ tailWord_2513001).sum := by decide
  have hdescent : baseEnd_2513001 < baseStart_2513001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513033 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_2513033 : Nat := 118140960795 + 2513033 * 2 ^ 59
def prefixEnd_2513033 : Nat := 4983230072969 + 3 ^ 40 * 2513033 * 2
def baseEnd_2513033 : Nat := 860262553073580987020185

theorem tailTrace_2513033 : CollatzResearch.WordTrace tailWord_2513033 prefixEnd_2513033 860262553073580987020185 := by
  unfold tailWord_2513033
  simp only [CollatzResearch.WordTrace]
  refine ⟨91657843504718107711799753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61105229003145405141199835 91657843504718107711799753)
  ·
    refine ⟨68743382628538580783849815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91657843504718107711799753 68743382628538580783849815)
    ·
      refine ⟨103115073942807871175774723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68743382628538580783849815 103115073942807871175774723)
      ·
        refine ⟨154672610914211806763662085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103115073942807871175774723 154672610914211806763662085)
        ·
          refine ⟨29001114546414713768186641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154672610914211806763662085 29001114546414713768186641)
          ·
            refine ⟨21750835909811035326139981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29001114546414713768186641 21750835909811035326139981)
            ·
              refine ⟨8156563466179138247302493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21750835909811035326139981 8156563466179138247302493)
              ·
                refine ⟨3058711299817176842738435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8156563466179138247302493 3058711299817176842738435)
                ·
                  refine ⟨4588066949725765264107653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058711299817176842738435 4588066949725765264107653)
                  ·
                    refine ⟨860262553073580987020185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4588066949725765264107653 860262553073580987020185)
                    ·
                      rfl

theorem cell22_2513033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_2513033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513033 prefixEnd_2513033 := by exact prefixLift 2513033
  have htrace : WordTrace (prefixWord ++ tailWord_2513033) baseStart_2513033 baseEnd_2513033 := by
    simpa [prefixWord, tailWord_2513033, baseEnd_2513033] using wordTrace_append hprefix tailTrace_2513033
  have hstable : (prefixWord ++ tailWord_2513033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513033).length < 2 ^ (prefixWord ++ tailWord_2513033).sum := by decide
  have hdescent : baseEnd_2513033 < baseStart_2513033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513061 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_2513061 : Nat := 118140960795 + 2513061 * 2 ^ 59
def prefixEnd_2513061 : Nat := 4983230072969 + 3 ^ 40 * 2513061 * 2
def baseEnd_2513061 : Nat := 860272138045798247320099

theorem tailTrace_2513061 : CollatzResearch.WordTrace tailWord_2513061 prefixEnd_2513061 860272138045798247320099 := by
  unfold tailWord_2513061
  simp only [CollatzResearch.WordTrace]
  refine ⟨91658864748616668493819037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61105909832411112329212691 91658864748616668493819037)
  ·
    refine ⟨34372074280731250685182139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91658864748616668493819037 34372074280731250685182139)
    ·
      refine ⟨51558111421096876027773209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34372074280731250685182139 51558111421096876027773209)
      ·
        refine ⟨38668583565822657020829907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51558111421096876027773209 38668583565822657020829907)
        ·
          refine ⟨58002875348733985531244861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38668583565822657020829907 58002875348733985531244861)
          ·
            refine ⟨21751078255775244574216823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58002875348733985531244861 21751078255775244574216823)
            ·
              refine ⟨32626617383662866861325235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21751078255775244574216823 32626617383662866861325235)
              ·
                refine ⟨48939926075494300291987853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32626617383662866861325235 48939926075494300291987853)
                ·
                  refine ⟨18352472278310362609495445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48939926075494300291987853 18352472278310362609495445)
                  ·
                    refine ⟨860272138045798247320099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18352472278310362609495445 860272138045798247320099)
                    ·
                      rfl

theorem cell22_2513061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_2513061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513061 prefixEnd_2513061 := by exact prefixLift 2513061
  have htrace : WordTrace (prefixWord ++ tailWord_2513061) baseStart_2513061 baseEnd_2513061 := by
    simpa [prefixWord, tailWord_2513061, baseEnd_2513061] using wordTrace_append hprefix tailTrace_2513061
  have hstable : (prefixWord ++ tailWord_2513061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513061).length < 2 ^ (prefixWord ++ tailWord_2513061).sum := by decide
  have hdescent : baseEnd_2513061 < baseStart_2513061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513110 : List Nat := [5, 2, 1, 2, 1, 1, 1, 9]
def baseStart_2513110 : Nat := 118140960795 + 2513110 * 2 ^ 59
def prefixEnd_2513110 : Nat := 4983230072969 + 3 ^ 40 * 2513110 * 2
def baseEnd_2513110 : Nat := 95587656860797605871661

theorem tailTrace_2513110 : CollatzResearch.WordTrace tailWord_2513110 prefixEnd_2513110 95587656860797605871661 := by
  unfold tailWord_2513110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728790745339946866397049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61107101283626099908235189 5728790745339946866397049)
  ·
    refine ⟨4296593059004960149797787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5728790745339946866397049 4296593059004960149797787)
    ·
      refine ⟨6444889588507440224696681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4296593059004960149797787 6444889588507440224696681)
      ·
        refine ⟨4833667191380580168522511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6444889588507440224696681 4833667191380580168522511)
        ·
          refine ⟨7250500787070870252783767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833667191380580168522511 7250500787070870252783767)
          ·
            refine ⟨10875751180606305379175651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7250500787070870252783767 10875751180606305379175651)
            ·
              refine ⟨16313626770909458068763477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10875751180606305379175651 16313626770909458068763477)
              ·
                refine ⟨95587656860797605871661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16313626770909458068763477 95587656860797605871661)
                ·
                  rfl

theorem cell22_2513110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_2513110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513110 prefixEnd_2513110 := by exact prefixLift 2513110
  have htrace : WordTrace (prefixWord ++ tailWord_2513110) baseStart_2513110 baseEnd_2513110 := by
    simpa [prefixWord, tailWord_2513110, baseEnd_2513110] using wordTrace_append hprefix tailTrace_2513110
  have hstable : (prefixWord ++ tailWord_2513110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513110).length < 2 ^ (prefixWord ++ tailWord_2513110).sum := by decide
  have hdescent : baseEnd_2513110 < baseStart_2513110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513153 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2513153 : Nat := 118140960795 + 2513153 * 2 ^ 59
def prefixEnd_2513153 : Nat := 4983230072969 + 3 ^ 40 * 2513153 * 2
def baseEnd_2513153 : Nat := 860303631525940674019817

theorem tailTrace_2513153 : CollatzResearch.WordTrace tailWord_2513153 prefixEnd_2513153 860303631525940674019817 := by
  unfold tailWord_2513153
  simp only [CollatzResearch.WordTrace]
  refine ⟨91662220264283368206168113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61108146842855578804112075 91662220264283368206168113)
  ·
    refine ⟨68746665198212526154626085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91662220264283368206168113 68746665198212526154626085)
    ·
      refine ⟨12889999724664848653992391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68746665198212526154626085 12889999724664848653992391)
      ·
        refine ⟨19334999586997272980988587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12889999724664848653992391 19334999586997272980988587)
        ·
          refine ⟨29002499380495909471482881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19334999586997272980988587 29002499380495909471482881)
          ·
            refine ⟨21751874535371932103612161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29002499380495909471482881 21751874535371932103612161)
            ·
              refine ⟨16313905901528949077709121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21751874535371932103612161 16313905901528949077709121)
              ·
                refine ⟨12235429426146711808281841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16313905901528949077709121 12235429426146711808281841)
                ·
                  refine ⟨9176572069610033856211381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12235429426146711808281841 9176572069610033856211381)
                  ·
                    refine ⟨860303631525940674019817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9176572069610033856211381 860303631525940674019817)
                    ·
                      rfl

theorem cell22_2513153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2513153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513153 prefixEnd_2513153 := by exact prefixLift 2513153
  have htrace : WordTrace (prefixWord ++ tailWord_2513153) baseStart_2513153 baseEnd_2513153 := by
    simpa [prefixWord, tailWord_2513153, baseEnd_2513153] using wordTrace_append hprefix tailTrace_2513153
  have hstable : (prefixWord ++ tailWord_2513153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513153).length < 2 ^ (prefixWord ++ tailWord_2513153).sum := by decide
  have hdescent : baseEnd_2513153 < baseStart_2513153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513183 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 8]
def baseStart_2513183 : Nat := 118140960795 + 2513183 * 2 ^ 59
def prefixEnd_2513183 : Nat := 4983230072969 + 3 ^ 40 * 2513183 * 2
def baseEnd_2513183 : Nat := 286771300379676865256575

theorem tailTrace_2513183 : CollatzResearch.WordTrace tailWord_2513183 prefixEnd_2513183 286771300379676865256575 := by
  unfold tailWord_2513183
  simp only [CollatzResearch.WordTrace]
  refine ⟨91663314454174683329760203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61108876302783122219840135 91663314454174683329760203)
  ·
    refine ⟨137494971681262024994640305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91663314454174683329760203 137494971681262024994640305)
    ·
      refine ⟨103121228760946518745980229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137494971681262024994640305 103121228760946518745980229)
      ·
        refine ⟨19335230392677472264871293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103121228760946518745980229 19335230392677472264871293)
        ·
          refine ⟨7250711397254052099326735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19335230392677472264871293 7250711397254052099326735)
          ·
            refine ⟨10876067095881078148990103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7250711397254052099326735 10876067095881078148990103)
            ·
              refine ⟨16314100643821617223485155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10876067095881078148990103 16314100643821617223485155)
              ·
                refine ⟨24471150965732425835227733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16314100643821617223485155 24471150965732425835227733)
                ·
                  refine ⟨286771300379676865256575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24471150965732425835227733 286771300379676865256575)
                  ·
                    rfl

theorem cell22_2513183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 8].length) (baseStart_2513183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513183 prefixEnd_2513183 := by exact prefixLift 2513183
  have htrace : WordTrace (prefixWord ++ tailWord_2513183) baseStart_2513183 baseEnd_2513183 := by
    simpa [prefixWord, tailWord_2513183, baseEnd_2513183] using wordTrace_append hprefix tailTrace_2513183
  have hstable : (prefixWord ++ tailWord_2513183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513183).length < 2 ^ (prefixWord ++ tailWord_2513183).sum := by decide
  have hdescent : baseEnd_2513183 < baseStart_2513183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513202 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_2513202 : Nat := 118140960795 + 2513202 * 2 ^ 59
def prefixEnd_2513202 : Nat := 4983230072969 + 3 ^ 40 * 2513202 * 2
def baseEnd_2513202 : Nat := 860320405227320879544667

theorem tailTrace_2513202 : CollatzResearch.WordTrace tailWord_2513202 prefixEnd_2513202 860320405227320879544667 := by
  unfold tailWord_2513202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22916001860276462393675465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61109338294070566383134573 22916001860276462393675465)
  ·
    refine ⟨17187001395207346795256599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22916001860276462393675465 17187001395207346795256599)
    ·
      refine ⟨25780502092811020192884899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17187001395207346795256599 25780502092811020192884899)
      ·
        refine ⟨38670753139216530289327349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25780502092811020192884899 38670753139216530289327349)
        ·
          refine ⟨3625383106801549714624439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38670753139216530289327349 3625383106801549714624439)
          ·
            refine ⟨5438074660202324571936659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625383106801549714624439 5438074660202324571936659)
            ·
              refine ⟨8157111990303486857904989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438074660202324571936659 8157111990303486857904989)
              ·
                refine ⟨3058916996363807571714371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8157111990303486857904989 3058916996363807571714371)
                ·
                  refine ⟨4588375494545711357571557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058916996363807571714371 4588375494545711357571557)
                  ·
                    refine ⟨860320405227320879544667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4588375494545711357571557 860320405227320879544667)
                    ·
                      rfl

theorem cell22_2513202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_2513202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513202 prefixEnd_2513202 := by exact prefixLift 2513202
  have htrace : WordTrace (prefixWord ++ tailWord_2513202) baseStart_2513202 baseEnd_2513202 := by
    simpa [prefixWord, tailWord_2513202, baseEnd_2513202] using wordTrace_append hprefix tailTrace_2513202
  have hstable : (prefixWord ++ tailWord_2513202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513202).length < 2 ^ (prefixWord ++ tailWord_2513202).sum := by decide
  have hdescent : baseEnd_2513202 < baseStart_2513202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513215 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 4, 3]
def baseStart_2513215 : Nat := 118140960795 + 2513215 * 2 ^ 59
def prefixEnd_2513215 : Nat := 4983230072969 + 3 ^ 40 * 2513215 * 2
def baseEnd_2513215 : Nat := 860324855392993178969627

theorem tailTrace_2513215 : CollatzResearch.WordTrace tailWord_2513215 prefixEnd_2513215 860324855392993178969627 := by
  unfold tailWord_2513215
  simp only [CollatzResearch.WordTrace]
  refine ⟨91664481590058752794925099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61109654393372501863283399 91664481590058752794925099)
  ·
    refine ⟨137496722385088129192387649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91664481590058752794925099 137496722385088129192387649)
    ·
      refine ⟨103122541788816096894290737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137496722385088129192387649 103122541788816096894290737)
      ·
        refine ⟨77341906341612072670718053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103122541788816096894290737 77341906341612072670718053)
        ·
          refine ⟨14501607439052263625759635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77341906341612072670718053 14501607439052263625759635)
          ·
            refine ⟨21752411158578395438639453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14501607439052263625759635 21752411158578395438639453)
            ·
              refine ⟨8157154184466898289489795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21752411158578395438639453 8157154184466898289489795)
              ·
                refine ⟨12235731276700347434234693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8157154184466898289489795 12235731276700347434234693)
                ·
                  refine ⟨2294199614381315143919005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12235731276700347434234693 2294199614381315143919005)
                  ·
                    refine ⟨860324855392993178969627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294199614381315143919005 860324855392993178969627)
                    ·
                      rfl

theorem cell22_2513215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_2513215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513215 prefixEnd_2513215 := by exact prefixLift 2513215
  have htrace : WordTrace (prefixWord ++ tailWord_2513215) baseStart_2513215 baseEnd_2513215 := by
    simpa [prefixWord, tailWord_2513215, baseEnd_2513215] using wordTrace_append hprefix tailTrace_2513215
  have hstable : (prefixWord ++ tailWord_2513215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513215).length < 2 ^ (prefixWord ++ tailWord_2513215).sum := by decide
  have hdescent : baseEnd_2513215 < baseStart_2513215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513217 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 6]
def baseStart_2513217 : Nat := 118140960795 + 2513217 * 2 ^ 59
def prefixEnd_2513217 : Nat := 4983230072969 + 3 ^ 40 * 2513217 * 2
def baseEnd_2513217 : Nat := 286775180011288613473207

theorem tailTrace_2513217 : CollatzResearch.WordTrace tailWord_2513217 prefixEnd_2513217 286775180011288613473207 := by
  unfold tailWord_2513217
  simp only [CollatzResearch.WordTrace]
  refine ⟨91664554536051507136497905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61109703024034338090998603 91664554536051507136497905)
  ·
    refine ⟨68748415902038630352373429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91664554536051507136497905 68748415902038630352373429)
    ·
      refine ⟨6445163990816121595535009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68748415902038630352373429 6445163990816121595535009)
      ·
        refine ⟨4833872993112091196651257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6445163990816121595535009 4833872993112091196651257)
        ·
          refine ⟨3625404744834068397488443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4833872993112091196651257 3625404744834068397488443)
          ·
            refine ⟨5438107117251102596232665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625404744834068397488443 5438107117251102596232665)
            ·
              refine ⟨4078580337938326947174499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5438107117251102596232665 4078580337938326947174499)
              ·
                refine ⟨6117870506907490420761749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4078580337938326947174499 6117870506907490420761749)
                ·
                  refine ⟨286775180011288613473207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6117870506907490420761749 286775180011288613473207)
                  ·
                    rfl

theorem cell22_2513217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_2513217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513217 prefixEnd_2513217 := by exact prefixLift 2513217
  have htrace : WordTrace (prefixWord ++ tailWord_2513217) baseStart_2513217 baseEnd_2513217 := by
    simpa [prefixWord, tailWord_2513217, baseEnd_2513217] using wordTrace_append hprefix tailTrace_2513217
  have hstable : (prefixWord ++ tailWord_2513217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513217).length < 2 ^ (prefixWord ++ tailWord_2513217).sum := by decide
  have hdescent : baseEnd_2513217 < baseStart_2513217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513228 : List Nat := [2, 2, 1, 3, 2, 1, 2, 9]
def baseStart_2513228 : Nat := 118140960795 + 2513228 * 2 ^ 59
def prefixEnd_2513228 : Nat := 4983230072969 + 3 ^ 40 * 2513228 * 2
def baseEnd_2513228 : Nat := 95592145062073942043843

theorem tailTrace_2513228 : CollatzResearch.WordTrace tailWord_2513228 prefixEnd_2513228 95592145062073942043843 := by
  unfold tailWord_2513228
  simp only [CollatzResearch.WordTrace]
  refine ⟨45832477869505828007574169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61109970492674437343432225 45832477869505828007574169)
  ·
    refine ⟨34374358402129371005680627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45832477869505828007574169 34374358402129371005680627)
    ·
      refine ⟨51561537603194056508520941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34374358402129371005680627 51561537603194056508520941)
      ·
        refine ⟨19335576601197771190695353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51561537603194056508520941 19335576601197771190695353)
        ·
          refine ⟨14501682450898328393021515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19335576601197771190695353 14501682450898328393021515)
          ·
            refine ⟨21752523676347492589532273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14501682450898328393021515 21752523676347492589532273)
            ·
              refine ⟨16314392757260619442149205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21752523676347492589532273 16314392757260619442149205)
              ·
                refine ⟨95592145062073942043843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16314392757260619442149205 95592145062073942043843)
                ·
                  rfl

theorem cell22_2513228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_2513228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513228 prefixEnd_2513228 := by exact prefixLift 2513228
  have htrace : WordTrace (prefixWord ++ tailWord_2513228) baseStart_2513228 baseEnd_2513228 := by
    simpa [prefixWord, tailWord_2513228, baseEnd_2513228] using wordTrace_append hprefix tailTrace_2513228
  have hstable : (prefixWord ++ tailWord_2513228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513228).length < 2 ^ (prefixWord ++ tailWord_2513228).sum := by decide
  have hdescent : baseEnd_2513228 < baseStart_2513228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513277 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_2513277 : Nat := 118140960795 + 2513277 * 2 ^ 59
def prefixEnd_2513277 : Nat := 4983230072969 + 3 ^ 40 * 2513277 * 2
def baseEnd_2513277 : Nat := 860346079260045683919437

theorem tailTrace_2513277 : CollatzResearch.WordTrace tailWord_2513277 prefixEnd_2513277 860346079260045683919437 := by
  unfold tailWord_2513277
  simp only [CollatzResearch.WordTrace]
  refine ⟨91666742915834137383682085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61111161943889424922454723 91666742915834137383682085)
  ·
    refine ⟨17187514296718900759440391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91666742915834137383682085 17187514296718900759440391)
    ·
      refine ⟨25781271445078351139160587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17187514296718900759440391 25781271445078351139160587)
      ·
        refine ⟨38671907167617526708740881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25781271445078351139160587 38671907167617526708740881)
        ·
          refine ⟨29003930375713145031555661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38671907167617526708740881 29003930375713145031555661)
          ·
            refine ⟨10876473890892429386833373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29003930375713145031555661 10876473890892429386833373)
            ·
              refine ⟨4078677709084661020062515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10876473890892429386833373 4078677709084661020062515)
              ·
                refine ⟨6118016563626991530093773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4078677709084661020062515 6118016563626991530093773)
                ·
                  refine ⟨2294256211360121823785165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6118016563626991530093773 2294256211360121823785165)
                  ·
                    refine ⟨860346079260045683919437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294256211360121823785165 860346079260045683919437)
                    ·
                      rfl

theorem cell22_2513277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_2513277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513277 prefixEnd_2513277 := by exact prefixLift 2513277
  have htrace : WordTrace (prefixWord ++ tailWord_2513277) baseStart_2513277 baseEnd_2513277 := by
    simpa [prefixWord, tailWord_2513277, baseEnd_2513277] using wordTrace_append hprefix tailTrace_2513277
  have hstable : (prefixWord ++ tailWord_2513277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513277).length < 2 ^ (prefixWord ++ tailWord_2513277).sum := by decide
  have hdescent : baseEnd_2513277 < baseStart_2513277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513384 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_2513384 : Nat := 118140960795 + 2513384 * 2 ^ 59
def prefixEnd_2513384 : Nat := 4983230072969 + 3 ^ 40 * 2513384 * 2
def baseEnd_2513384 : Nat := 860382707546733071494109

theorem tailTrace_2513384 : CollatzResearch.WordTrace tailWord_2513384 prefixEnd_2513384 860382707546733071494109 := by
  unfold tailWord_2513384
  simp only [CollatzResearch.WordTrace]
  refine ⟨45835322763223247328913603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61113763684297663105218137 45835322763223247328913603)
  ·
    refine ⟨68752984144834870993370405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45835322763223247328913603 68752984144834870993370405)
    ·
      refine ⟨12891184527156538311256951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68752984144834870993370405 12891184527156538311256951)
      ·
        refine ⟨19336776790734807466885427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12891184527156538311256951 19336776790734807466885427)
        ·
          refine ⟨29005165186102211200328141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19336776790734807466885427 29005165186102211200328141)
          ·
            refine ⟨10876936944788329200123053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29005165186102211200328141 10876936944788329200123053)
            ·
              refine ⟨4078851354295623450046145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10876936944788329200123053 4078851354295623450046145)
              ·
                refine ⟨3059138515721717587534609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4078851354295623450046145 3059138515721717587534609)
                ·
                  refine ⟨2294353886791288190650957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059138515721717587534609 2294353886791288190650957)
                  ·
                    refine ⟨860382707546733071494109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294353886791288190650957 860382707546733071494109)
                    ·
                      rfl

theorem cell22_2513384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_2513384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513384 prefixEnd_2513384 := by exact prefixLift 2513384
  have htrace : WordTrace (prefixWord ++ tailWord_2513384) baseStart_2513384 baseEnd_2513384 := by
    simpa [prefixWord, tailWord_2513384, baseEnd_2513384] using wordTrace_append hprefix tailTrace_2513384
  have hstable : (prefixWord ++ tailWord_2513384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513384).length < 2 ^ (prefixWord ++ tailWord_2513384).sum := by decide
  have hdescent : baseEnd_2513384 < baseStart_2513384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513442 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_2513442 : Nat := 118140960795 + 2513442 * 2 ^ 59
def prefixEnd_2513442 : Nat := 4983230072969 + 3 ^ 40 * 2513442 * 2
def baseEnd_2513442 : Nat := 286800854044013417847977

theorem tailTrace_2513442 : CollatzResearch.WordTrace tailWord_2513442 prefixEnd_2513442 286800854044013417847977 := by
  unfold tailWord_2513442
  simp only [CollatzResearch.WordTrace]
  refine ⟨22918190240059092640859645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61115173973490913708959053 22918190240059092640859645)
  ·
    refine ⟨8594321340022159740322367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22918190240059092640859645 8594321340022159740322367)
    ·
      refine ⟨12891482010033239610483551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8594321340022159740322367 12891482010033239610483551)
      ·
        refine ⟨19337223015049859415725327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12891482010033239610483551 19337223015049859415725327)
        ·
          refine ⟨29005834522574789123587991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19337223015049859415725327 29005834522574789123587991)
          ·
            refine ⟨43508751783862183685381987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29005834522574789123587991 43508751783862183685381987)
            ·
              refine ⟨65263127675793275528072981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43508751783862183685381987 65263127675793275528072981)
              ·
                refine ⟨3059209109802809790378421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65263127675793275528072981 3059209109802809790378421)
                ·
                  refine ⟨286800854044013417847977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3059209109802809790378421 286800854044013417847977)
                  ·
                    rfl

theorem cell22_2513442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_2513442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513442 prefixEnd_2513442 := by exact prefixLift 2513442
  have htrace : WordTrace (prefixWord ++ tailWord_2513442) baseStart_2513442 baseEnd_2513442 := by
    simpa [prefixWord, tailWord_2513442, baseEnd_2513442] using wordTrace_append hprefix tailTrace_2513442
  have hstable : (prefixWord ++ tailWord_2513442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513442).length < 2 ^ (prefixWord ++ tailWord_2513442).sum := by decide
  have hdescent : baseEnd_2513442 < baseStart_2513442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513515 : List Nat := [1, 1, 1, 1, 2, 2, 1, 13]
def baseStart_2513515 : Nat := 118140960795 + 2513515 * 2 ^ 59
def prefixEnd_2513515 : Nat := 4983230072969 + 3 ^ 40 * 2513515 * 2
def baseEnd_2513515 : Nat := 95603061280432488496523

theorem tailTrace_2513515 : CollatzResearch.WordTrace tailWord_2513515 prefixEnd_2513515 95603061280432488496523 := by
  unfold tailWord_2513515
  simp only [CollatzResearch.WordTrace]
  refine ⟨91675423488971904030845999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61116948992647936020563999 91675423488971904030845999)
  ·
    refine ⟨137513135233457856046268999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91675423488971904030845999 137513135233457856046268999)
    ·
      refine ⟨206269702850186784069403499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137513135233457856046268999 206269702850186784069403499)
      ·
        refine ⟨309404554275280176104105249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206269702850186784069403499 309404554275280176104105249)
        ·
          refine ⟨232053415706460132078078937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309404554275280176104105249 232053415706460132078078937)
          ·
            refine ⟨174040061779845099058559203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232053415706460132078078937 174040061779845099058559203)
            ·
              refine ⟨261060092669767648587838805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174040061779845099058559203 261060092669767648587838805)
              ·
                refine ⟨95603061280432488496523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 261060092669767648587838805 95603061280432488496523)
                ·
                  rfl

theorem cell22_2513515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 13].length) (baseStart_2513515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513515 prefixEnd_2513515 := by exact prefixLift 2513515
  have htrace : WordTrace (prefixWord ++ tailWord_2513515) baseStart_2513515 baseEnd_2513515 := by
    simpa [prefixWord, tailWord_2513515, baseEnd_2513515] using wordTrace_append hprefix tailTrace_2513515
  have hstable : (prefixWord ++ tailWord_2513515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513515).length < 2 ^ (prefixWord ++ tailWord_2513515).sum := by decide
  have hdescent : baseEnd_2513515 < baseStart_2513515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513519 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 2, 3]
def baseStart_2513519 : Nat := 118140960795 + 2513519 * 2 ^ 59
def prefixEnd_2513519 : Nat := 4983230072969 + 3 ^ 40 * 2513519 * 2
def baseEnd_2513519 : Nat := 860428920805637719368695

theorem tailTrace_2513519 : CollatzResearch.WordTrace tailWord_2513519 prefixEnd_2513519 860428920805637719368695 := by
  unfold tailWord_2513519
  simp only [CollatzResearch.WordTrace]
  refine ⟨91675569380957412713991611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61117046253971608475994407 91675569380957412713991611)
  ·
    refine ⟨137513354071436119070987417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91675569380957412713991611 137513354071436119070987417)
    ·
      refine ⟨103135015553577089303240563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137513354071436119070987417 103135015553577089303240563)
      ·
        refine ⟨154702523330365633954860845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103135015553577089303240563 154702523330365633954860845)
        ·
          refine ⟨58013446248887112733072817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154702523330365633954860845 58013446248887112733072817)
          ·
            refine ⟨43510084686665334549804613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58013446248887112733072817 43510084686665334549804613)
            ·
              refine ⟨8158140878749750228088365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43510084686665334549804613 8158140878749750228088365)
              ·
                refine ⟨3059302829531156335533137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8158140878749750228088365 3059302829531156335533137)
                ·
                  refine ⟨2294477122148367251649853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059302829531156335533137 2294477122148367251649853)
                  ·
                    refine ⟨860428920805637719368695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294477122148367251649853 860428920805637719368695)
                    ·
                      rfl

theorem cell22_2513519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_2513519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513519 prefixEnd_2513519 := by exact prefixLift 2513519
  have htrace : WordTrace (prefixWord ++ tailWord_2513519) baseStart_2513519 baseEnd_2513519 := by
    simpa [prefixWord, tailWord_2513519, baseEnd_2513519] using wordTrace_append hprefix tailTrace_2513519
  have hstable : (prefixWord ++ tailWord_2513519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513519).length < 2 ^ (prefixWord ++ tailWord_2513519).sum := by decide
  have hdescent : baseEnd_2513519 < baseStart_2513519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513581 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2513581 : Nat := 118140960795 + 2513581 * 2 ^ 59
def prefixEnd_2513581 : Nat := 4983230072969 + 3 ^ 40 * 2513581 * 2
def baseEnd_2513581 : Nat := 860450144672690224318505

theorem tailTrace_2513581 : CollatzResearch.WordTrace tailWord_2513581 prefixEnd_2513581 860450144672690224318505 := by
  unfold tailWord_2513581
  simp only [CollatzResearch.WordTrace]
  refine ⟨91677830706732797302748597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61118553804488531535165731 91677830706732797302748597)
  ·
    refine ⟨8594796628756199747132681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91677830706732797302748597 8594796628756199747132681)
    ·
      refine ⟨6446097471567149810349511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8594796628756199747132681 6446097471567149810349511)
      ·
        refine ⟨9669146207350724715524267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6446097471567149810349511 9669146207350724715524267)
        ·
          refine ⟨14503719311026087073286401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9669146207350724715524267 14503719311026087073286401)
          ·
            refine ⟨10877789483269565304964801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14503719311026087073286401 10877789483269565304964801)
            ·
              refine ⟨8158342112452173978723601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10877789483269565304964801 8158342112452173978723601)
              ·
                refine ⟨6118756584339130484042701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8158342112452173978723601 6118756584339130484042701)
                ·
                  refine ⟨2294533719127173931516013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6118756584339130484042701 2294533719127173931516013)
                  ·
                    refine ⟨860450144672690224318505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294533719127173931516013 860450144672690224318505)
                    ·
                      rfl

theorem cell22_2513581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2513581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513581 prefixEnd_2513581 := by exact prefixLift 2513581
  have htrace : WordTrace (prefixWord ++ tailWord_2513581) baseStart_2513581 baseEnd_2513581 := by
    simpa [prefixWord, tailWord_2513581, baseEnd_2513581] using wordTrace_append hprefix tailTrace_2513581
  have hstable : (prefixWord ++ tailWord_2513581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513581).length < 2 ^ (prefixWord ++ tailWord_2513581).sum := by decide
  have hdescent : baseEnd_2513581 < baseStart_2513581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513628 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 5]
def baseStart_2513628 : Nat := 118140960795 + 2513628 * 2 ^ 59
def prefixEnd_2513628 : Nat := 4983230072969 + 3 ^ 40 * 2513628 * 2
def baseEnd_2513628 : Nat := 286822077911065922797787

theorem tailTrace_2513628 : CollatzResearch.WordTrace tailWord_2513628 prefixEnd_2513628 286822077911065922797787 := by
  unfold tailWord_2513628
  simp only [CollatzResearch.WordTrace]
  refine ⟨45839772468781262164854769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61119696625041682886473025 45839772468781262164854769)
  ·
    refine ⟨34379829351585946623641077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45839772468781262164854769 34379829351585946623641077)
    ·
      refine ⟨3223109001711182495966351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34379829351585946623641077 3223109001711182495966351)
      ·
        refine ⟨4834663502566773743949527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223109001711182495966351 4834663502566773743949527)
        ·
          refine ⟨7251995253850160615924291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4834663502566773743949527 7251995253850160615924291)
          ·
            refine ⟨10877992880775240923886437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7251995253850160615924291 10877992880775240923886437)
            ·
              refine ⟨2039623665145357673228707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10877992880775240923886437 2039623665145357673228707)
              ·
                refine ⟨3059435497718036509843061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039623665145357673228707 3059435497718036509843061)
                ·
                  refine ⟨286822077911065922797787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3059435497718036509843061 286822077911065922797787)
                  ·
                    rfl

theorem cell22_2513628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_2513628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513628 prefixEnd_2513628 := by exact prefixLift 2513628
  have htrace : WordTrace (prefixWord ++ tailWord_2513628) baseStart_2513628 baseEnd_2513628 := by
    simpa [prefixWord, tailWord_2513628, baseEnd_2513628] using wordTrace_append hprefix tailTrace_2513628
  have hstable : (prefixWord ++ tailWord_2513628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513628).length < 2 ^ (prefixWord ++ tailWord_2513628).sum := by decide
  have hdescent : baseEnd_2513628 < baseStart_2513628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513709 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2513709 : Nat := 118140960795 + 2513709 * 2 ^ 59
def prefixEnd_2513709 : Nat := 4983230072969 + 3 ^ 40 * 2513709 * 2
def baseEnd_2513709 : Nat := 860493961688540557118113

theorem tailTrace_2513709 : CollatzResearch.WordTrace tailWord_2513709 prefixEnd_2513709 860493961688540557118113 := by
  unfold tailWord_2513709
  simp only [CollatzResearch.WordTrace]
  refine ⟨91682499250269075163408181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61121666166846050108938787 91682499250269075163408181)
  ·
    refine ⟨8595234304712725796569517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91682499250269075163408181 8595234304712725796569517)
    ·
      refine ⟨3223212864267272173713569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8595234304712725796569517 3223212864267272173713569)
      ·
        refine ⟨2417409648200454130285177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3223212864267272173713569 2417409648200454130285177)
        ·
          refine ⟨1813057236150340597713883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417409648200454130285177 1813057236150340597713883)
          ·
            refine ⟨2719585854225510896570825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813057236150340597713883 2719585854225510896570825)
            ·
              refine ⟨2039689390669133172428119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2719585854225510896570825 2039689390669133172428119)
              ·
                refine ⟨3059534086003699758642179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039689390669133172428119 3059534086003699758642179)
                ·
                  refine ⟨4589301129005549637963269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059534086003699758642179 4589301129005549637963269)
                  ·
                    refine ⟨860493961688540557118113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4589301129005549637963269 860493961688540557118113)
                    ·
                      rfl

theorem cell22_2513709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2513709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513709 prefixEnd_2513709 := by exact prefixLift 2513709
  have htrace : WordTrace (prefixWord ++ tailWord_2513709) baseStart_2513709 baseEnd_2513709 := by
    simpa [prefixWord, tailWord_2513709, baseEnd_2513709] using wordTrace_append hprefix tailTrace_2513709
  have hstable : (prefixWord ++ tailWord_2513709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513709).length < 2 ^ (prefixWord ++ tailWord_2513709).sum := by decide
  have hdescent : baseEnd_2513709 < baseStart_2513709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513744 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_2513744 : Nat := 118140960795 + 2513744 * 2 ^ 59
def prefixEnd_2513744 : Nat := 4983230072969 + 3 ^ 40 * 2513744 * 2
def baseEnd_2513744 : Nat := 860505942903812132493005

theorem tailTrace_2513744 : CollatzResearch.WordTrace tailWord_2513744 prefixEnd_2513744 860505942903812132493005 := by
  unfold tailWord_2513744
  simp only [CollatzResearch.WordTrace]
  refine ⟨45841887902571138070466143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61122517203428184093954857 45841887902571138070466143)
  ·
    refine ⟨68762831853856707105699215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45841887902571138070466143 68762831853856707105699215)
    ·
      refine ⟨103144247780785060658548823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68762831853856707105699215 103144247780785060658548823)
      ·
        refine ⟨154716371671177590987823235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103144247780785060658548823 154716371671177590987823235)
        ·
          refine ⟨232074557506766386481734853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154716371671177590987823235 232074557506766386481734853)
          ·
            refine ⟨43513979532518697465325285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232074557506766386481734853 43513979532518697465325285)
            ·
              refine ⟨8158871162347255774748491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43513979532518697465325285 8158871162347255774748491)
              ·
                refine ⟨12238306743520883662122737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158871162347255774748491 12238306743520883662122737)
                ·
                  refine ⟨9178730057640662746592053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12238306743520883662122737 9178730057640662746592053)
                  ·
                    refine ⟨860505942903812132493005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9178730057640662746592053 860505942903812132493005)
                    ·
                      rfl

theorem cell22_2513744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_2513744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513744 prefixEnd_2513744 := by exact prefixLift 2513744
  have htrace : WordTrace (prefixWord ++ tailWord_2513744) baseStart_2513744 baseEnd_2513744 := by
    simpa [prefixWord, tailWord_2513744, baseEnd_2513744] using wordTrace_append hprefix tailTrace_2513744
  have hstable : (prefixWord ++ tailWord_2513744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513744).length < 2 ^ (prefixWord ++ tailWord_2513744).sum := by decide
  have hdescent : baseEnd_2513744 < baseStart_2513744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513776 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_2513776 : Nat := 118140960795 + 2513776 * 2 ^ 59
def prefixEnd_2513776 : Nat := 4983230072969 + 3 ^ 40 * 2513776 * 2
def baseEnd_2513776 : Nat := 860516897157774715692907

theorem tailTrace_2513776 : CollatzResearch.WordTrace tailWord_2513776 prefixEnd_2513776 860516897157774715692907 := by
  unfold tailWord_2513776
  simp only [CollatzResearch.WordTrace]
  refine ⟨45842471470513172803048591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61123295294017563737398121 45842471470513172803048591)
  ·
    refine ⟨68763707205769759204572887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45842471470513172803048591 68763707205769759204572887)
    ·
      refine ⟨103145560808654638806859331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68763707205769759204572887 103145560808654638806859331)
      ·
        refine ⟨154718341212981958210288997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103145560808654638806859331 154718341212981958210288997)
        ·
          refine ⟨29009688977434117164429187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154718341212981958210288997 29009688977434117164429187)
          ·
            refine ⟨43514533466151175746643781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29009688977434117164429187 43514533466151175746643781)
            ·
              refine ⟨8158975024903345452495709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43514533466151175746643781 8158975024903345452495709)
              ·
                refine ⟨3059615634338754544685891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8158975024903345452495709 3059615634338754544685891)
                ·
                  refine ⟨4589423451508131817028837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059615634338754544685891 4589423451508131817028837)
                  ·
                    refine ⟨860516897157774715692907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4589423451508131817028837 860516897157774715692907)
                    ·
                      rfl

theorem cell22_2513776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_2513776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513776 prefixEnd_2513776 := by exact prefixLift 2513776
  have htrace : WordTrace (prefixWord ++ tailWord_2513776) baseStart_2513776 baseEnd_2513776 := by
    simpa [prefixWord, tailWord_2513776, baseEnd_2513776] using wordTrace_append hprefix tailTrace_2513776
  have hstable : (prefixWord ++ tailWord_2513776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513776).length < 2 ^ (prefixWord ++ tailWord_2513776).sum := by decide
  have hdescent : baseEnd_2513776 < baseStart_2513776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513791 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 4]
def baseStart_2513791 : Nat := 118140960795 + 2513791 * 2 ^ 59
def prefixEnd_2513791 : Nat := 4983230072969 + 3 ^ 40 * 2513791 * 2
def baseEnd_2513791 : Nat := 286840677321439892189287

theorem tailTrace_2513791 : CollatzResearch.WordTrace tailWord_2513791 prefixEnd_2513791 286840677321439892189287 := by
  unfold tailWord_2513791
  simp only [CollatzResearch.WordTrace]
  refine ⟨91685490035972003167893227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61123660023981335445262151 91685490035972003167893227)
  ·
    refine ⟨137528235053958004751839841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91685490035972003167893227 137528235053958004751839841)
    ·
      refine ⟨103146176290468503563879881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137528235053958004751839841 103146176290468503563879881)
      ·
        refine ⟨77359632217851377672909911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103146176290468503563879881 77359632217851377672909911)
        ·
          refine ⟨116039448326777066509364867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77359632217851377672909911 116039448326777066509364867)
          ·
            refine ⟨174059172490165599764047301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116039448326777066509364867 174059172490165599764047301)
            ·
              refine ⟨32636094841906049955758869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174059172490165599764047301 32636094841906049955758869)
              ·
                refine ⟨1529816945714346091676197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32636094841906049955758869 1529816945714346091676197)
                ·
                  refine ⟨286840677321439892189287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529816945714346091676197 286840677321439892189287)
                  ·
                    rfl

theorem cell22_2513791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 4].length) (baseStart_2513791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513791 prefixEnd_2513791 := by exact prefixLift 2513791
  have htrace : WordTrace (prefixWord ++ tailWord_2513791) baseStart_2513791 baseEnd_2513791 := by
    simpa [prefixWord, tailWord_2513791, baseEnd_2513791] using wordTrace_append hprefix tailTrace_2513791
  have hstable : (prefixWord ++ tailWord_2513791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513791).length < 2 ^ (prefixWord ++ tailWord_2513791).sum := by decide
  have hdescent : baseEnd_2513791 < baseStart_2513791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513804 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_2513804 : Nat := 118140960795 + 2513804 * 2 ^ 59
def prefixEnd_2513804 : Nat := 4983230072969 + 3 ^ 40 * 2513804 * 2
def baseEnd_2513804 : Nat := 860526482129991975992821

theorem tailTrace_2513804 : CollatzResearch.WordTrace tailWord_2513804 prefixEnd_2513804 860526482129991975992821 := by
  unfold tailWord_2513804
  simp only [CollatzResearch.WordTrace]
  refine ⟨45842982092462453194058233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61123976123283270925410977 45842982092462453194058233)
  ·
    refine ⟨34382236569346839895543675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45842982092462453194058233 34382236569346839895543675)
    ·
      refine ⟨51573354854020259843315513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34382236569346839895543675 51573354854020259843315513)
      ·
        refine ⟨38680016140515194882486635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51573354854020259843315513 38680016140515194882486635)
        ·
          refine ⟨58020024210772792323729953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38680016140515194882486635 58020024210772792323729953)
          ·
            refine ⟨43515018158079594242797465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58020024210772792323729953 43515018158079594242797465)
            ·
              refine ⟨32636263618559695682098099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43515018158079594242797465 32636263618559695682098099)
              ·
                refine ⟨48954395427839543523147149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32636263618559695682098099 48954395427839543523147149)
                ·
                  refine ⟨18357898285439828821180181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48954395427839543523147149 18357898285439828821180181)
                  ·
                    refine ⟨860526482129991975992821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18357898285439828821180181 860526482129991975992821)
                    ·
                      rfl

theorem cell22_2513804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_2513804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513804 prefixEnd_2513804 := by exact prefixLift 2513804
  have htrace : WordTrace (prefixWord ++ tailWord_2513804) baseStart_2513804 baseEnd_2513804 := by
    simpa [prefixWord, tailWord_2513804, baseEnd_2513804] using wordTrace_append hprefix tailTrace_2513804
  have hstable : (prefixWord ++ tailWord_2513804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513804).length < 2 ^ (prefixWord ++ tailWord_2513804).sum := by decide
  have hdescent : baseEnd_2513804 < baseStart_2513804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513853 : List Nat := [1, 4, 1, 2, 4, 2, 1, 7]
def baseStart_2513853 : Nat := 118140960795 + 2513853 * 2 ^ 59
def prefixEnd_2513853 : Nat := 4983230072969 + 3 ^ 40 * 2513853 * 2
def baseEnd_2513853 : Nat := 95615917314596909057519

theorem tailTrace_2513853 : CollatzResearch.WordTrace tailWord_2513853 prefixEnd_2513853 95615917314596909057519 := by
  unfold tailWord_2513853
  simp only [CollatzResearch.WordTrace]
  refine ⟨91687751361747387756650213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61125167574498258504433475 91687751361747387756650213)
  ·
    refine ⟨17191453380327635204371915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91687751361747387756650213 17191453380327635204371915)
    ·
      refine ⟨25787180070491452806557873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17191453380327635204371915 25787180070491452806557873)
      ·
        refine ⟨19340385052868589604918405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25787180070491452806557873 19340385052868589604918405)
        ·
          refine ⟨3626322197412860550922201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19340385052868589604918405 3626322197412860550922201)
          ·
            refine ⟨2719741648059645413191651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3626322197412860550922201 2719741648059645413191651)
            ·
              refine ⟨4079612472089468119787477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719741648059645413191651 4079612472089468119787477)
              ·
                refine ⟨95615917314596909057519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4079612472089468119787477 95615917314596909057519)
                ·
                  rfl

theorem cell22_2513853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 7].length) (baseStart_2513853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513853 prefixEnd_2513853 := by exact prefixLift 2513853
  have htrace : WordTrace (prefixWord ++ tailWord_2513853) baseStart_2513853 baseEnd_2513853 := by
    simpa [prefixWord, tailWord_2513853, baseEnd_2513853] using wordTrace_append hprefix tailTrace_2513853
  have hstable : (prefixWord ++ tailWord_2513853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513853).length < 2 ^ (prefixWord ++ tailWord_2513853).sum := by decide
  have hdescent : baseEnd_2513853 < baseStart_2513853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513868 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_2513868 : Nat := 118140960795 + 2513868 * 2 ^ 59
def prefixEnd_2513868 : Nat := 4983230072969 + 3 ^ 40 * 2513868 * 2
def baseEnd_2513868 : Nat := 860548390637917142392625

theorem tailTrace_2513868 : CollatzResearch.WordTrace tailWord_2513868 prefixEnd_2513868 860548390637917142392625 := by
  unfold tailWord_2513868
  simp only [CollatzResearch.WordTrace]
  refine ⟨45844149228346522659223129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61125532304462030212297505 45844149228346522659223129)
  ·
    refine ⟨34383111921259891994417347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45844149228346522659223129 34383111921259891994417347)
    ·
      refine ⟨51574667881889837991626021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34383111921259891994417347 51574667881889837991626021)
      ·
        refine ⟨9670250227854344623429879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51574667881889837991626021 9670250227854344623429879)
        ·
          refine ⟨14505375341781516935144819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9670250227854344623429879 14505375341781516935144819)
          ·
            refine ⟨21758063012672275402717229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14505375341781516935144819 21758063012672275402717229)
            ·
              refine ⟨8159273629752103276018961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21758063012672275402717229 8159273629752103276018961)
              ·
                refine ⟨6119455222314077457014221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8159273629752103276018961 6119455222314077457014221)
                ·
                  refine ⟨2294795708367779046380333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6119455222314077457014221 2294795708367779046380333)
                  ·
                    refine ⟨860548390637917142392625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294795708367779046380333 860548390637917142392625)
                    ·
                      rfl

theorem cell22_2513868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_2513868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513868 prefixEnd_2513868 := by exact prefixLift 2513868
  have htrace : WordTrace (prefixWord ++ tailWord_2513868) baseStart_2513868 baseEnd_2513868 := by
    simpa [prefixWord, tailWord_2513868, baseEnd_2513868] using wordTrace_append hprefix tailTrace_2513868
  have hstable : (prefixWord ++ tailWord_2513868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513868).length < 2 ^ (prefixWord ++ tailWord_2513868).sum := by decide
  have hdescent : baseEnd_2513868 < baseStart_2513868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513896 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2513896 : Nat := 118140960795 + 2513896 * 2 ^ 59
def prefixEnd_2513896 : Nat := 4983230072969 + 3 ^ 40 * 2513896 * 2
def baseEnd_2513896 : Nat := 860557975610134402692539

theorem tailTrace_2513896 : CollatzResearch.WordTrace tailWord_2513896 prefixEnd_2513896 860557975610134402692539 := by
  unfold tailWord_2513896
  simp only [CollatzResearch.WordTrace]
  refine ⟨45844659850295803050232771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61126213133727737400310361 45844659850295803050232771)
  ·
    refine ⟨68766989775443704575349157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45844659850295803050232771 68766989775443704575349157)
    ·
      refine ⟨12893810582895694607877967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68766989775443704575349157 12893810582895694607877967)
      ·
        refine ⟨19340715874343541911816951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12893810582895694607877967 19340715874343541911816951)
        ·
          refine ⟨29011073811515312867725427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19340715874343541911816951 29011073811515312867725427)
          ·
            refine ⟨43516610717272969301588141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29011073811515312867725427 43516610717272969301588141)
            ·
              refine ⟨16318729018977363488095553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43516610717272969301588141 16318729018977363488095553)
              ·
                refine ⟨12239046764233022616071665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16318729018977363488095553 12239046764233022616071665)
                ·
                  refine ⟨9179285073174766962053749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12239046764233022616071665 9179285073174766962053749)
                  ·
                    refine ⟨860557975610134402692539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9179285073174766962053749 860557975610134402692539)
                    ·
                      rfl

theorem cell22_2513896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2513896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513896 prefixEnd_2513896 := by exact prefixLift 2513896
  have htrace : WordTrace (prefixWord ++ tailWord_2513896) baseStart_2513896 baseEnd_2513896 := by
    simpa [prefixWord, tailWord_2513896, baseEnd_2513896] using wordTrace_append hprefix tailTrace_2513896
  have hstable : (prefixWord ++ tailWord_2513896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513896).length < 2 ^ (prefixWord ++ tailWord_2513896).sum := by decide
  have hdescent : baseEnd_2513896 < baseStart_2513896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513898 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_2513898 : Nat := 118140960795 + 2513898 * 2 ^ 59
def prefixEnd_2513898 : Nat := 4983230072969 + 3 ^ 40 * 2513898 * 2
def baseEnd_2513898 : Nat := 286852886750335688047511

theorem tailTrace_2513898 : CollatzResearch.WordTrace tailWord_2513898 prefixEnd_2513898 286852886750335688047511 := by
  unfold tailWord_2513898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22922348161646090110509587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61126261764389573628025565 22922348161646090110509587)
  ·
    refine ⟨34383522242469135165764381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22922348161646090110509587 34383522242469135165764381)
    ·
      refine ⟨12893820840925925687161643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34383522242469135165764381 12893820840925925687161643)
      ·
        refine ⟨19340731261388888530742465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12893820840925925687161643 19340731261388888530742465)
        ·
          refine ⟨14505548446041666398056849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19340731261388888530742465 14505548446041666398056849)
          ·
            refine ⟨10879161334531249798542637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14505548446041666398056849 10879161334531249798542637)
            ·
              refine ⟨4079685500449218674453489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10879161334531249798542637 4079685500449218674453489)
              ·
                refine ⟨3059764125336914005840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4079685500449218674453489 3059764125336914005840117)
                ·
                  refine ⟨286852886750335688047511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3059764125336914005840117 286852886750335688047511)
                  ·
                    rfl

theorem cell22_2513898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_2513898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513898 prefixEnd_2513898 := by exact prefixLift 2513898
  have htrace : WordTrace (prefixWord ++ tailWord_2513898) baseStart_2513898 baseEnd_2513898 := by
    simpa [prefixWord, tailWord_2513898, baseEnd_2513898] using wordTrace_append hprefix tailTrace_2513898
  have hstable : (prefixWord ++ tailWord_2513898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513898).length < 2 ^ (prefixWord ++ tailWord_2513898).sum := by decide
  have hdescent : baseEnd_2513898 < baseStart_2513898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513908 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2513908 : Nat := 118140960795 + 2513908 * 2 ^ 59
def prefixEnd_2513908 : Nat := 4983230072969 + 3 ^ 40 * 2513908 * 2
def baseEnd_2513908 : Nat := 860562083455370371392503

theorem tailTrace_2513908 : CollatzResearch.WordTrace tailWord_2513908 prefixEnd_2513908 860562083455370371392503 := by
  unfold tailWord_2513908
  simp only [CollatzResearch.WordTrace]
  refine ⟨45844878688274066074951189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61126504917698754766601585 45844878688274066074951189)
  ·
    refine ⟨2148978688512846847263337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45844878688274066074951189 2148978688512846847263337)
    ·
      refine ⟨1611734016384635135447503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148978688512846847263337 1611734016384635135447503)
      ·
        refine ⟨2417601024576952703171255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611734016384635135447503 2417601024576952703171255)
        ·
          refine ⟨3626401536865429054756883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417601024576952703171255 3626401536865429054756883)
          ·
            refine ⟨5439602305298143582135325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3626401536865429054756883 5439602305298143582135325)
            ·
              refine ⟨2039850864486803843300747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5439602305298143582135325 2039850864486803843300747)
              ·
                refine ⟨3059776296730205764951121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039850864486803843300747 3059776296730205764951121)
                ·
                  refine ⟨2294832222547654323713341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059776296730205764951121 2294832222547654323713341)
                  ·
                    refine ⟨860562083455370371392503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294832222547654323713341 860562083455370371392503)
                    ·
                      rfl

theorem cell22_2513908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2513908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513908 prefixEnd_2513908 := by exact prefixLift 2513908
  have htrace : WordTrace (prefixWord ++ tailWord_2513908) baseStart_2513908 baseEnd_2513908 := by
    simpa [prefixWord, tailWord_2513908, baseEnd_2513908] using wordTrace_append hprefix tailTrace_2513908
  have hstable : (prefixWord ++ tailWord_2513908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513908).length < 2 ^ (prefixWord ++ tailWord_2513908).sum := by decide
  have hdescent : baseEnd_2513908 < baseStart_2513908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513928 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_2513928 : Nat := 118140960795 + 2513928 * 2 ^ 59
def prefixEnd_2513928 : Nat := 4983230072969 + 3 ^ 40 * 2513928 * 2
def baseEnd_2513928 : Nat := 860568929864096985892441

theorem tailTrace_2513928 : CollatzResearch.WordTrace tailWord_2513928 prefixEnd_2513928 860568929864096985892441 := by
  unfold tailWord_2513928
  simp only [CollatzResearch.WordTrace]
  refine ⟨45845243418237837782815219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61126991224317117043753625 45845243418237837782815219)
  ·
    refine ⟨68767865127356756674222829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45845243418237837782815219 68767865127356756674222829)
    ·
      refine ⟨25787949422758783752833561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68767865127356756674222829 25787949422758783752833561)
      ·
        refine ⟨19340962067069087814625171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25787949422758783752833561 19340962067069087814625171)
        ·
          refine ⟨29011443100603631721937757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19340962067069087814625171 29011443100603631721937757)
          ·
            refine ⟨10879291162726361895726659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29011443100603631721937757 10879291162726361895726659)
            ·
              refine ⟨16318936744089542843589989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10879291162726361895726659 16318936744089542843589989)
              ·
                refine ⟨3059800639516789283173123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16318936744089542843589989 3059800639516789283173123)
                ·
                  refine ⟨4589700959275183924759685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059800639516789283173123 4589700959275183924759685)
                  ·
                    refine ⟨860568929864096985892441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4589700959275183924759685 860568929864096985892441)
                    ·
                      rfl

theorem cell22_2513928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_2513928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2513928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2513928 prefixEnd_2513928 := by exact prefixLift 2513928
  have htrace : WordTrace (prefixWord ++ tailWord_2513928) baseStart_2513928 baseEnd_2513928 := by
    simpa [prefixWord, tailWord_2513928, baseEnd_2513928] using wordTrace_append hprefix tailTrace_2513928
  have hstable : (prefixWord ++ tailWord_2513928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513928).length < 2 ^ (prefixWord ++ tailWord_2513928).sum := by decide
  have hdescent : baseEnd_2513928 < baseStart_2513928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514097 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_2514097 : Nat := 118140960795 + 2514097 * 2 ^ 59
def prefixEnd_2514097 : Nat := 4983230072969 + 3 ^ 40 * 2514097 * 2
def baseEnd_2514097 : Nat := 860626782017836878416923

theorem tailTrace_2514097 : CollatzResearch.WordTrace tailWord_2514097 prefixEnd_2514097 860626782017836878416923 := by
  unfold tailWord_2514097
  simp only [CollatzResearch.WordTrace]
  refine ⟨91696650772863417428532545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61131100515242278285688363 91696650772863417428532545)
  ·
    refine ⟨68772488079647563071399409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91696650772863417428532545 68772488079647563071399409)
    ·
      refine ⟨51579366059735672303549557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68772488079647563071399409 51579366059735672303549557)
      ·
        refine ⟨4835565568100219278457771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51579366059735672303549557 4835565568100219278457771)
        ·
          refine ⟨7253348352150328917686657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835565568100219278457771 7253348352150328917686657)
          ·
            refine ⟨5440011264112746688264993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7253348352150328917686657 5440011264112746688264993)
            ·
              refine ⟨4080008448084560016198745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5440011264112746688264993 4080008448084560016198745)
              ·
                refine ⟨3060006336063420012149059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4080008448084560016198745 3060006336063420012149059)
                ·
                  refine ⟨4590009504095130018223589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060006336063420012149059 4590009504095130018223589)
                  ·
                    refine ⟨860626782017836878416923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4590009504095130018223589 860626782017836878416923)
                    ·
                      rfl

theorem cell22_2514097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_2514097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514097 prefixEnd_2514097 := by exact prefixLift 2514097
  have htrace : WordTrace (prefixWord ++ tailWord_2514097) baseStart_2514097 baseEnd_2514097 := by
    simpa [prefixWord, tailWord_2514097, baseEnd_2514097] using wordTrace_append hprefix tailTrace_2514097
  have hstable : (prefixWord ++ tailWord_2514097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514097).length < 2 ^ (prefixWord ++ tailWord_2514097).sum := by decide
  have hdescent : baseEnd_2514097 < baseStart_2514097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514144 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 2, 3]
def baseStart_2514144 : Nat := 118140960795 + 2514144 * 2 ^ 59
def prefixEnd_2514144 : Nat := 4983230072969 + 3 ^ 40 * 2514144 * 2
def baseEnd_2514144 : Nat := 860642871078344422491779

theorem tailTrace_2514144 : CollatzResearch.WordTrace tailWord_2514144 prefixEnd_2514144 860642871078344422491779 := by
  unfold tailWord_2514144
  simp only [CollatzResearch.WordTrace]
  refine ⟨45849182501846572227746743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61132243335795429636995657 45849182501846572227746743)
  ·
    refine ⟨68773773752769858341620115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45849182501846572227746743 68773773752769858341620115)
    ·
      refine ⟨103160660629154787512430173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68773773752769858341620115 103160660629154787512430173)
      ·
        refine ⟨38685247735933045317161315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103160660629154787512430173 38685247735933045317161315)
        ·
          refine ⟨58027871603899567975741973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38685247735933045317161315 58027871603899567975741973)
          ·
            refine ⟨2720056481432792248862905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58027871603899567975741973 2720056481432792248862905)
            ·
              refine ⟨2040042361074594186647179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720056481432792248862905 2040042361074594186647179)
              ·
                refine ⟨3060063541611891279970769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040042361074594186647179 3060063541611891279970769)
                ·
                  refine ⟨2295047656208918459978077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060063541611891279970769 2295047656208918459978077)
                  ·
                    refine ⟨860642871078344422491779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295047656208918459978077 860642871078344422491779)
                    ·
                      rfl

theorem cell22_2514144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_2514144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514144 prefixEnd_2514144 := by exact prefixLift 2514144
  have htrace : WordTrace (prefixWord ++ tailWord_2514144) baseStart_2514144 baseEnd_2514144 := by
    simpa [prefixWord, tailWord_2514144, baseEnd_2514144] using wordTrace_append hprefix tailTrace_2514144
  have hstable : (prefixWord ++ tailWord_2514144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514144).length < 2 ^ (prefixWord ++ tailWord_2514144).sum := by decide
  have hdescent : baseEnd_2514144 < baseStart_2514144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514185 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 5]
def baseStart_2514185 : Nat := 118140960795 + 2514185 * 2 ^ 59
def prefixEnd_2514185 : Nat := 4983230072969 + 3 ^ 40 * 2514185 * 2
def baseEnd_2514185 : Nat := 286885635405411327405551

theorem tailTrace_2514185 : CollatzResearch.WordTrace tailWord_2514185 prefixEnd_2514185 286885635405411327405551 := by
  unfold tailWord_2514185
  simp only [CollatzResearch.WordTrace]
  refine ⟨91699860396544608457736009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61133240264363072305157339 91699860396544608457736009)
  ·
    refine ⟨68774895297408456343302007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91699860396544608457736009 68774895297408456343302007)
    ·
      refine ⟨103162342946112684514953011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68774895297408456343302007 103162342946112684514953011)
      ·
        refine ⟨154743514419169026772429517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103162342946112684514953011 154743514419169026772429517)
        ·
          refine ⟨58028817907188385039661069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154743514419169026772429517 58028817907188385039661069)
          ·
            refine ⟨21760806715195644389872901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58028817907188385039661069 21760806715195644389872901)
            ·
              refine ⟨4080151259099183323101169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21760806715195644389872901 4080151259099183323101169)
              ·
                refine ⟨3060113444324387492325877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4080151259099183323101169 3060113444324387492325877)
                ·
                  refine ⟨286885635405411327405551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3060113444324387492325877 286885635405411327405551)
                  ·
                    rfl

theorem cell22_2514185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_2514185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514185 prefixEnd_2514185 := by exact prefixLift 2514185
  have htrace : WordTrace (prefixWord ++ tailWord_2514185) baseStart_2514185 baseEnd_2514185 := by
    simpa [prefixWord, tailWord_2514185, baseEnd_2514185] using wordTrace_append hprefix tailTrace_2514185
  have hstable : (prefixWord ++ tailWord_2514185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514185).length < 2 ^ (prefixWord ++ tailWord_2514185).sum := by decide
  have hdescent : baseEnd_2514185 < baseStart_2514185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514200 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_2514200 : Nat := 118140960795 + 2514200 * 2 ^ 59
def prefixEnd_2514200 : Nat := 4983230072969 + 3 ^ 40 * 2514200 * 2
def baseEnd_2514200 : Nat := 860662041022778943091607

theorem tailTrace_2514200 : CollatzResearch.WordTrace tailWord_2514200 prefixEnd_2514200 860662041022778943091607 := by
  unfold tailWord_2514200
  simp only [CollatzResearch.WordTrace]
  refine ⟨45850203745745133009766027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61133604994326844013021369 45850203745745133009766027)
  ·
    refine ⟨68775305618617699514649041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45850203745745133009766027 68775305618617699514649041)
    ·
      refine ⟨51581479213963274635986781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68775305618617699514649041 51581479213963274635986781)
      ·
        refine ⟨19343054705236227988495043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51581479213963274635986781 19343054705236227988495043)
        ·
          refine ⟨29014582057854341982742565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19343054705236227988495043 29014582057854341982742565)
          ·
            refine ⟨5440234135847689121764231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29014582057854341982742565 5440234135847689121764231)
            ·
              refine ⟨8160351203771533682646347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440234135847689121764231 8160351203771533682646347)
              ·
                refine ⟨12240526805657300523969521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8160351203771533682646347 12240526805657300523969521)
                ·
                  refine ⟨9180395104242975392977141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12240526805657300523969521 9180395104242975392977141)
                  ·
                    refine ⟨860662041022778943091607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9180395104242975392977141 860662041022778943091607)
                    ·
                      rfl

theorem cell22_2514200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_2514200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514200 prefixEnd_2514200 := by exact prefixLift 2514200
  have htrace : WordTrace (prefixWord ++ tailWord_2514200) baseStart_2514200 baseEnd_2514200 := by
    simpa [prefixWord, tailWord_2514200, baseEnd_2514200] using wordTrace_append hprefix tailTrace_2514200
  have hstable : (prefixWord ++ tailWord_2514200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514200).length < 2 ^ (prefixWord ++ tailWord_2514200).sum := by decide
  have hdescent : baseEnd_2514200 < baseStart_2514200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514206 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2514206 : Nat := 118140960795 + 2514206 * 2 ^ 59
def prefixEnd_2514206 : Nat := 4983230072969 + 3 ^ 40 * 2514206 * 2
def baseEnd_2514206 : Nat := 860664094945396927441589

theorem tailTrace_2514206 : CollatzResearch.WordTrace tailWord_2514206 prefixEnd_2514206 860664094945396927441589 := by
  unfold tailWord_2514206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462578291183566130531309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61133750886312352696166981 11462578291183566130531309)
  ·
    refine ⟨4298466859193837298949241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11462578291183566130531309 4298466859193837298949241)
    ·
      refine ⟨3223850144395377974211931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4298466859193837298949241 3223850144395377974211931)
      ·
        refine ⟨4835775216593066961317897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223850144395377974211931 4835775216593066961317897)
        ·
          refine ⟨3626831412444800220988423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4835775216593066961317897 3626831412444800220988423)
          ·
            refine ⟨5440247118667200331482635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3626831412444800220988423 5440247118667200331482635)
            ·
              refine ⟨8160370678000800497223953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440247118667200331482635 8160370678000800497223953)
              ·
                refine ⟨6120278008500600372917965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8160370678000800497223953 6120278008500600372917965)
                ·
                  refine ⟨2295104253187725139844237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6120278008500600372917965 2295104253187725139844237)
                  ·
                    refine ⟨860664094945396927441589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295104253187725139844237 860664094945396927441589)
                    ·
                      rfl

theorem cell22_2514206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2514206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514206 prefixEnd_2514206 := by exact prefixLift 2514206
  have htrace : WordTrace (prefixWord ++ tailWord_2514206) baseStart_2514206 baseEnd_2514206 := by
    simpa [prefixWord, tailWord_2514206, baseEnd_2514206] using wordTrace_append hprefix tailTrace_2514206
  have hstable : (prefixWord ++ tailWord_2514206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514206).length < 2 ^ (prefixWord ++ tailWord_2514206).sum := by decide
  have hdescent : baseEnd_2514206 < baseStart_2514206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514247 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 4]
def baseStart_2514247 : Nat := 118140960795 + 2514247 * 2 ^ 59
def prefixEnd_2514247 : Nat := 4983230072969 + 3 ^ 40 * 2514247 * 2
def baseEnd_2514247 : Nat := 286892710027762162388821

theorem tailTrace_2514247 : CollatzResearch.WordTrace tailWord_2514247 prefixEnd_2514247 286892710027762162388821 := by
  unfold tailWord_2514247
  simp only [CollatzResearch.WordTrace]
  refine ⟨91702121722319993046492995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61134747814879995364328663 91702121722319993046492995)
  ·
    refine ⟨137553182583479989569739493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91702121722319993046492995 137553182583479989569739493)
    ·
      refine ⟨25791221734402498044326155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137553182583479989569739493 25791221734402498044326155)
      ·
        refine ⟨38686832601603747066489233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25791221734402498044326155 38686832601603747066489233)
        ·
          refine ⟨29015124451202810299866925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38686832601603747066489233 29015124451202810299866925)
          ·
            refine ⟨10880671669201053862450097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29015124451202810299866925 10880671669201053862450097)
            ·
              refine ⟨8160503751900790396837573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10880671669201053862450097 8160503751900790396837573)
              ·
                refine ⟨1530094453481398199407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8160503751900790396837573 1530094453481398199407045)
                ·
                  refine ⟨286892710027762162388821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530094453481398199407045 286892710027762162388821)
                  ·
                    rfl

theorem cell22_2514247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 4].length) (baseStart_2514247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514247 prefixEnd_2514247 := by exact prefixLift 2514247
  have htrace : WordTrace (prefixWord ++ tailWord_2514247) baseStart_2514247 baseEnd_2514247 := by
    simpa [prefixWord, tailWord_2514247, baseEnd_2514247] using wordTrace_append hprefix tailTrace_2514247
  have hstable : (prefixWord ++ tailWord_2514247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514247).length < 2 ^ (prefixWord ++ tailWord_2514247).sum := by decide
  have hdescent : baseEnd_2514247 < baseStart_2514247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514260 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2514260 : Nat := 118140960795 + 2514260 * 2 ^ 59
def prefixEnd_2514260 : Nat := 4983230072969 + 3 ^ 40 * 2514260 * 2
def baseEnd_2514260 : Nat := 860682580248958786591423

theorem tailTrace_2514260 : CollatzResearch.WordTrace tailWord_2514260 prefixEnd_2514260 860682580248958786591423 := by
  unfold tailWord_2514260
  simp only [CollatzResearch.WordTrace]
  refine ⟨45851297935636448133358117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61135063914181930844477489 45851297935636448133358117)
  ·
    refine ⟨8597118362931834025004647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45851297935636448133358117 8597118362931834025004647)
    ·
      refine ⟨12895677544397751037506971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597118362931834025004647 12895677544397751037506971)
      ·
        refine ⟨19343516316596626556260457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12895677544397751037506971 19343516316596626556260457)
        ·
          refine ⟨14507637237447469917195343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19343516316596626556260457 14507637237447469917195343)
          ·
            refine ⟨21761455856171204875793015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14507637237447469917195343 21761455856171204875793015)
            ·
              refine ⟨32642183784256807313689523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21761455856171204875793015 32642183784256807313689523)
              ·
                refine ⟨48963275676385210970534285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32642183784256807313689523 48963275676385210970534285)
                ·
                  refine ⟨18361228378644454113950357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48963275676385210970534285 18361228378644454113950357)
                  ·
                    refine ⟨860682580248958786591423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18361228378644454113950357 860682580248958786591423)
                    ·
                      rfl

theorem cell22_2514260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2514260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514260 prefixEnd_2514260 := by exact prefixLift 2514260
  have htrace : WordTrace (prefixWord ++ tailWord_2514260) baseStart_2514260 baseEnd_2514260 := by
    simpa [prefixWord, tailWord_2514260, baseEnd_2514260] using wordTrace_append hprefix tailTrace_2514260
  have hstable : (prefixWord ++ tailWord_2514260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514260).length < 2 ^ (prefixWord ++ tailWord_2514260).sum := by decide
  have hdescent : baseEnd_2514260 < baseStart_2514260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514275 : List Nat := [1, 1, 1, 5, 2, 3, 1, 8]
def baseStart_2514275 : Nat := 118140960795 + 2514275 * 2 ^ 59
def prefixEnd_2514275 : Nat := 4983230072969 + 3 ^ 40 * 2514275 * 2
def baseEnd_2514275 : Nat := 95631968339500416385153

theorem tailTrace_2514275 : CollatzResearch.WordTrace tailWord_2514275 prefixEnd_2514275 95631968339500416385153 := by
  unfold tailWord_2514275
  simp only [CollatzResearch.WordTrace]
  refine ⟨91703142966218553828512279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61135428644145702552341519 91703142966218553828512279)
  ·
    refine ⟨137554714449327830742768419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91703142966218553828512279 137554714449327830742768419)
    ·
      refine ⟨206332071673991746114152629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137554714449327830742768419 206332071673991746114152629)
      ·
        refine ⟨19343631719436726198201809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206332071673991746114152629 19343631719436726198201809)
        ·
          refine ⟨14507723789577544648651357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19343631719436726198201809 14507723789577544648651357)
          ·
            refine ⟨5440396421091579243244259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14507723789577544648651357 5440396421091579243244259)
            ·
              refine ⟨8160594631637368864866389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440396421091579243244259 8160594631637368864866389)
              ·
                refine ⟨95631968339500416385153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8160594631637368864866389 95631968339500416385153)
                ·
                  rfl

theorem cell22_2514275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 8].length) (baseStart_2514275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514275 prefixEnd_2514275 := by exact prefixLift 2514275
  have htrace : WordTrace (prefixWord ++ tailWord_2514275) baseStart_2514275 baseEnd_2514275 := by
    simpa [prefixWord, tailWord_2514275, baseEnd_2514275] using wordTrace_append hprefix tailTrace_2514275
  have hstable : (prefixWord ++ tailWord_2514275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514275).length < 2 ^ (prefixWord ++ tailWord_2514275).sum := by decide
  have hdescent : baseEnd_2514275 < baseStart_2514275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514313 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 2, 3]
def baseStart_2514313 : Nat := 118140960795 + 2514313 * 2 ^ 59
def prefixEnd_2514313 : Nat := 4983230072969 + 3 ^ 40 * 2514313 * 2
def baseEnd_2514313 : Nat := 860700723232084315016261

theorem tailTrace_2514313 : CollatzResearch.WordTrace tailWord_2514313 prefixEnd_2514313 860700723232084315016261 := by
  unfold tailWord_2514313
  simp only [CollatzResearch.WordTrace]
  refine ⟨91704528940080886318395593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61136352626720590878930395 91704528940080886318395593)
  ·
    refine ⟨68778396705060664738796695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91704528940080886318395593 68778396705060664738796695)
    ·
      refine ⟨103167595057590997108195043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68778396705060664738796695 103167595057590997108195043)
      ·
        refine ⟨154751392586386495662292565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103167595057590997108195043 154751392586386495662292565)
        ·
          refine ⟨1813492881871716746042491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 154751392586386495662292565 1813492881871716746042491)
          ·
            refine ⟨2720239322807575119063737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813492881871716746042491 2720239322807575119063737)
            ·
              refine ⟨2040179492105681339297803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720239322807575119063737 2040179492105681339297803)
              ·
                refine ⟨3060269238158522008946705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040179492105681339297803 3060269238158522008946705)
                ·
                  refine ⟨2295201928618891506710029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060269238158522008946705 2295201928618891506710029)
                  ·
                    refine ⟨860700723232084315016261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295201928618891506710029 860700723232084315016261)
                    ·
                      rfl

theorem cell22_2514313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_2514313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514313 prefixEnd_2514313 := by exact prefixLift 2514313
  have htrace : WordTrace (prefixWord ++ tailWord_2514313) baseStart_2514313 baseEnd_2514313 := by
    simpa [prefixWord, tailWord_2514313, baseEnd_2514313] using wordTrace_append hprefix tailTrace_2514313
  have hstable : (prefixWord ++ tailWord_2514313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514313).length < 2 ^ (prefixWord ++ tailWord_2514313).sum := by decide
  have hdescent : baseEnd_2514313 < baseStart_2514313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514399 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 4]
def baseStart_2514399 : Nat := 118140960795 + 2514399 * 2 ^ 59
def prefixEnd_2514399 : Nat := 4983230072969 + 3 ^ 40 * 2514399 * 2
def baseEnd_2514399 : Nat := 286910054263202919121999

theorem tailTrace_2514399 : CollatzResearch.WordTrace tailWord_2514399 prefixEnd_2514399 286910054263202919121999 := by
  unfold tailWord_2514399
  simp only [CollatzResearch.WordTrace]
  refine ⟨91707665617769323006026251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61138443745179548670684167 91707665617769323006026251)
  ·
    refine ⟨137561498426653984509039377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91707665617769323006026251 137561498426653984509039377)
    ·
      refine ⟨103171123819990488381779533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137561498426653984509039377 103171123819990488381779533)
      ·
        refine ⟨38689171432496433143167325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103171123819990488381779533 38689171432496433143167325)
        ·
          refine ⟨14508439287186162428687747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38689171432496433143167325 14508439287186162428687747)
          ·
            refine ⟨21762658930779243643031621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14508439287186162428687747 21762658930779243643031621)
            ·
              refine ⟨4080498549521108183068429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21762658930779243643031621 4080498549521108183068429)
              ·
                refine ⟨1530186956070415568650661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4080498549521108183068429 1530186956070415568650661)
                ·
                  refine ⟨286910054263202919121999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530186956070415568650661 286910054263202919121999)
                  ·
                    rfl

theorem cell22_2514399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 4].length) (baseStart_2514399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514399 prefixEnd_2514399 := by exact prefixLift 2514399
  have htrace : WordTrace (prefixWord ++ tailWord_2514399) baseStart_2514399 baseEnd_2514399 := by
    simpa [prefixWord, tailWord_2514399, baseEnd_2514399] using wordTrace_append hprefix tailTrace_2514399
  have hstable : (prefixWord ++ tailWord_2514399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514399).length < 2 ^ (prefixWord ++ tailWord_2514399).sum := by decide
  have hdescent : baseEnd_2514399 < baseStart_2514399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514401 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 1, 4]
def baseStart_2514401 : Nat := 118140960795 + 2514401 * 2 ^ 59
def prefixEnd_2514401 : Nat := 4983230072969 + 3 ^ 40 * 2514401 * 2
def baseEnd_2514401 : Nat := 860730847430481418815991

theorem tailTrace_2514401 : CollatzResearch.WordTrace tailWord_2514401 prefixEnd_2514401 860730847430481418815991 := by
  unfold tailWord_2514401
  simp only [CollatzResearch.WordTrace]
  refine ⟨91707738563762077347599057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61138492375841384898399371 91707738563762077347599057)
  ·
    refine ⟨68780803922821558010699293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91707738563762077347599057 68780803922821558010699293)
    ·
      refine ⟨25792801471058084254012235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68780803922821558010699293 25792801471058084254012235)
      ·
        refine ⟨38689202206587126381018353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25792801471058084254012235 38689202206587126381018353)
        ·
          refine ⟨29016901654940344785763765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38689202206587126381018353 29016901654940344785763765)
          ·
            refine ⟨2720334530150657323665353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29016901654940344785763765 2720334530150657323665353)
            ·
              refine ⟨2040250897612992992749015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720334530150657323665353 2040250897612992992749015)
              ·
                refine ⟨3060376346419489489123523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040250897612992992749015 3060376346419489489123523)
                ·
                  refine ⟨4590564519629234233685285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060376346419489489123523 4590564519629234233685285)
                  ·
                    refine ⟨860730847430481418815991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4590564519629234233685285 860730847430481418815991)
                    ·
                      rfl

theorem cell22_2514401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_2514401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514401 prefixEnd_2514401 := by exact prefixLift 2514401
  have htrace : WordTrace (prefixWord ++ tailWord_2514401) baseStart_2514401 baseEnd_2514401 := by
    simpa [prefixWord, tailWord_2514401, baseEnd_2514401] using wordTrace_append hprefix tailTrace_2514401
  have hstable : (prefixWord ++ tailWord_2514401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514401).length < 2 ^ (prefixWord ++ tailWord_2514401).sum := by decide
  have hdescent : baseEnd_2514401 < baseStart_2514401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514414 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_2514414 : Nat := 118140960795 + 2514414 * 2 ^ 59
def prefixEnd_2514414 : Nat := 4983230072969 + 3 ^ 40 * 2514414 * 2
def baseEnd_2514414 : Nat := 860735297596153718240951

theorem tailTrace_2514414 : CollatzResearch.WordTrace tailWord_2514414 prefixEnd_2514414 860735297596153718240951 := by
  unfold tailWord_2514414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463526589089372570977787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61138808475143320378548197 11463526589089372570977787)
  ·
    refine ⟨17195289883634058856466681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11463526589089372570977787 17195289883634058856466681)
    ·
      refine ⟨12896467412725544142350011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17195289883634058856466681 12896467412725544142350011)
      ·
        refine ⟨19344701119088316213525017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12896467412725544142350011 19344701119088316213525017)
        ·
          refine ⟨14508525839316237160143763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19344701119088316213525017 14508525839316237160143763)
          ·
            refine ⟨21762788758974355740215645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14508525839316237160143763 21762788758974355740215645)
            ·
              refine ⟨8161045784615383402580867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21762788758974355740215645 8161045784615383402580867)
              ·
                refine ⟨12241568676923075103871301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8161045784615383402580867 12241568676923075103871301)
                ·
                  refine ⟨2295294126923076581975869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12241568676923075103871301 2295294126923076581975869)
                  ·
                    refine ⟨860735297596153718240951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295294126923076581975869 860735297596153718240951)
                    ·
                      rfl

theorem cell22_2514414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_2514414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514414 prefixEnd_2514414 := by exact prefixLift 2514414
  have htrace : WordTrace (prefixWord ++ tailWord_2514414) baseStart_2514414 baseEnd_2514414 := by
    simpa [prefixWord, tailWord_2514414, baseEnd_2514414] using wordTrace_append hprefix tailTrace_2514414
  have hstable : (prefixWord ++ tailWord_2514414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514414).length < 2 ^ (prefixWord ++ tailWord_2514414).sum := by decide
  have hdescent : baseEnd_2514414 < baseStart_2514414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514489 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 5]
def baseStart_2514489 : Nat := 118140960795 + 2514489 * 2 ^ 59
def prefixEnd_2514489 : Nat := 4983230072969 + 3 ^ 40 * 2514489 * 2
def baseEnd_2514489 : Nat := 286920323876292840871907

theorem tailTrace_2514489 : CollatzResearch.WordTrace tailWord_2514489 prefixEnd_2514489 286920323876292840871907 := by
  unfold tailWord_2514489
  simp only [CollatzResearch.WordTrace]
  refine ⟨91710948187443268376802521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61140632124962178917868347 91710948187443268376802521)
  ·
    refine ⟨68783211140582451282601891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91710948187443268376802521 68783211140582451282601891)
    ·
      refine ⟨103174816710873676923902837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68783211140582451282601891 103174816710873676923902837)
      ·
        refine ⟨9672639066644407211615891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103174816710873676923902837 9672639066644407211615891)
        ·
          refine ⟨14508958599966610817423837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9672639066644407211615891 14508958599966610817423837)
          ·
            refine ⟨5440859474987479056533939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14508958599966610817423837 5440859474987479056533939)
            ·
              refine ⟨8161289212481218584800909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440859474987479056533939 8161289212481218584800909)
              ·
                refine ⟨3060483454680456969300341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8161289212481218584800909 3060483454680456969300341)
                ·
                  refine ⟨286920323876292840871907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3060483454680456969300341 286920323876292840871907)
                  ·
                    rfl

theorem cell22_2514489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_2514489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514489 prefixEnd_2514489 := by exact prefixLift 2514489
  have htrace : WordTrace (prefixWord ++ tailWord_2514489) baseStart_2514489 baseEnd_2514489 := by
    simpa [prefixWord, tailWord_2514489, baseEnd_2514489] using wordTrace_append hprefix tailTrace_2514489
  have hstable : (prefixWord ++ tailWord_2514489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514489).length < 2 ^ (prefixWord ++ tailWord_2514489).sum := by decide
  have hdescent : baseEnd_2514489 < baseStart_2514489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514583 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 2, 3]
def baseStart_2514583 : Nat := 118140960795 + 2514583 * 2 ^ 59
def prefixEnd_2514583 : Nat := 4983230072969 + 3 ^ 40 * 2514583 * 2
def baseEnd_2514583 : Nat := 860793149749893610765433

theorem tailTrace_2514583 : CollatzResearch.WordTrace tailWord_2514583 prefixEnd_2514583 860793149749893610765433 := by
  unfold tailWord_2514583
  simp only [CollatzResearch.WordTrace]
  refine ⟨91714376649102722430724403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61142917766068481620482935 91714376649102722430724403)
  ·
    refine ⟨137571564973654083646086605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91714376649102722430724403 137571564973654083646086605)
    ·
      refine ⟨51589336865120281367282477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137571564973654083646086605 51589336865120281367282477)
      ·
        refine ⟨19346001324420105512730929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51589336865120281367282477 19346001324420105512730929)
        ·
          refine ⟨14509500993315079134548197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19346001324420105512730929 14509500993315079134548197)
          ·
            refine ⟨2720531436246577337727787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14509500993315079134548197 2720531436246577337727787)
            ·
              refine ⟨4080797154369866006591681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720531436246577337727787 4080797154369866006591681)
              ·
                refine ⟨3060597865777399504943761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4080797154369866006591681 3060597865777399504943761)
                ·
                  refine ⟨2295448399333049628707821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060597865777399504943761 2295448399333049628707821)
                  ·
                    refine ⟨860793149749893610765433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295448399333049628707821 860793149749893610765433)
                    ·
                      rfl

theorem cell22_2514583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_2514583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514583 prefixEnd_2514583 := by exact prefixLift 2514583
  have htrace : WordTrace (prefixWord ++ tailWord_2514583) baseStart_2514583 baseEnd_2514583 := by
    simpa [prefixWord, tailWord_2514583, baseEnd_2514583] using wordTrace_append hprefix tailTrace_2514583
  have hstable : (prefixWord ++ tailWord_2514583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514583).length < 2 ^ (prefixWord ++ tailWord_2514583).sum := by decide
  have hdescent : baseEnd_2514583 < baseStart_2514583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514613 : List Nat := [1, 3, 3, 3, 2, 2, 2, 6]
def baseStart_2514613 : Nat := 118140960795 + 2514613 * 2 ^ 59
def prefixEnd_2514613 : Nat := 4983230072969 + 3 ^ 40 * 2514613 * 2
def baseEnd_2514613 : Nat := 95644824373664836946149

theorem tailTrace_2514613 : CollatzResearch.WordTrace tailWord_2514613 prefixEnd_2514613 95644824373664836946149 := by
  unfold tailWord_2514613
  simp only [CollatzResearch.WordTrace]
  refine ⟨91715470838994037554316493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61143647225996025036210995 91715470838994037554316493)
  ·
    refine ⟨34393301564622764082868685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91715470838994037554316493 34393301564622764082868685)
    ·
      refine ⟨12897488086733536531075757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34393301564622764082868685 12897488086733536531075757)
      ·
        refine ⟨4836558032525076199153409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12897488086733536531075757 4836558032525076199153409)
        ·
          refine ⟨3627418524393807149365057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4836558032525076199153409 3627418524393807149365057)
          ·
            refine ⟨2720563893295355362023793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3627418524393807149365057 2720563893295355362023793)
            ·
              refine ⟨2040422919971516521517845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720563893295355362023793 2040422919971516521517845)
              ·
                refine ⟨95644824373664836946149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2040422919971516521517845 95644824373664836946149)
                ·
                  rfl

theorem cell22_2514613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 6].length) (baseStart_2514613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514613 prefixEnd_2514613 := by exact prefixLift 2514613
  have htrace : WordTrace (prefixWord ++ tailWord_2514613) baseStart_2514613 baseEnd_2514613 := by
    simpa [prefixWord, tailWord_2514613, baseEnd_2514613] using wordTrace_append hprefix tailTrace_2514613
  have hstable : (prefixWord ++ tailWord_2514613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514613).length < 2 ^ (prefixWord ++ tailWord_2514613).sum := by decide
  have hdescent : baseEnd_2514613 < baseStart_2514613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514840 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_2514840 : Nat := 118140960795 + 2514840 * 2 ^ 59
def prefixEnd_2514840 : Nat := 4983230072969 + 3 ^ 40 * 2514840 * 2
def baseEnd_2514840 : Nat := 860881126102030607089645

theorem tailTrace_2514840 : CollatzResearch.WordTrace tailWord_2514840 prefixEnd_2514840 860881126102030607089645 := by
  unfold tailWord_2514840
  simp only [CollatzResearch.WordTrace]
  refine ⟨45861875104585827661414987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61149166806114436881886649 45861875104585827661414987)
  ·
    refine ⟨68792812656878741492122481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45861875104585827661414987 68792812656878741492122481)
    ·
      refine ⟨51594609492659056119091861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68792812656878741492122481 51594609492659056119091861)
      ·
        refine ⟨2418497319968393255582431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51594609492659056119091861 2418497319968393255582431)
        ·
          refine ⟨3627745979952589883373647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418497319968393255582431 3627745979952589883373647)
          ·
            refine ⟨5441618969928884825060471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627745979952589883373647 5441618969928884825060471)
            ·
              refine ⟨8162428454893327237590707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441618969928884825060471 8162428454893327237590707)
              ·
                refine ⟨12243642682339990856386061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8162428454893327237590707 12243642682339990856386061)
                ·
                  refine ⟨4591366005877496571144773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12243642682339990856386061 4591366005877496571144773)
                  ·
                    refine ⟨860881126102030607089645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4591366005877496571144773 860881126102030607089645)
                    ·
                      rfl

theorem cell22_2514840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_2514840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514840 prefixEnd_2514840 := by exact prefixLift 2514840
  have htrace : WordTrace (prefixWord ++ tailWord_2514840) baseStart_2514840 baseEnd_2514840 := by
    simpa [prefixWord, tailWord_2514840, baseEnd_2514840] using wordTrace_append hprefix tailTrace_2514840
  have hstable : (prefixWord ++ tailWord_2514840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514840).length < 2 ^ (prefixWord ++ tailWord_2514840).sum := by decide
  have hdescent : baseEnd_2514840 < baseStart_2514840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514908 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2514908 : Nat := 118140960795 + 2514908 * 2 ^ 59
def prefixEnd_2514908 : Nat := 4983230072969 + 3 ^ 40 * 2514908 * 2
def baseEnd_2514908 : Nat := 860904403891701096389437

theorem tailTrace_2514908 : CollatzResearch.WordTrace tailWord_2514908 prefixEnd_2514908 860904403891701096389437 := by
  unfold tailWord_2514908
  simp only [CollatzResearch.WordTrace]
  refine ⟨45863115186462651468152689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61150820248616868624203585 45863115186462651468152689)
  ·
    refine ⟨34397336389846988601114517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45863115186462651468152689 34397336389846988601114517)
    ·
      refine ⟨1612375143274077590677243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34397336389846988601114517 1612375143274077590677243)
      ·
        refine ⟨2418562714911116386015865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612375143274077590677243 2418562714911116386015865)
        ·
          refine ⟨1813922036183337289511899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418562714911116386015865 1813922036183337289511899)
          ·
            refine ⟨2720883054275005934267849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813922036183337289511899 2720883054275005934267849)
            ·
              refine ⟨2040662290706254450700887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720883054275005934267849 2040662290706254450700887)
              ·
                refine ⟨3060993436059381676051331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040662290706254450700887 3060993436059381676051331)
                ·
                  refine ⟨4591490154089072514076997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060993436059381676051331 4591490154089072514076997)
                  ·
                    refine ⟨860904403891701096389437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4591490154089072514076997 860904403891701096389437)
                    ·
                      rfl

theorem cell22_2514908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2514908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514908 prefixEnd_2514908 := by exact prefixLift 2514908
  have htrace : WordTrace (prefixWord ++ tailWord_2514908) baseStart_2514908 baseEnd_2514908 := by
    simpa [prefixWord, tailWord_2514908, baseEnd_2514908] using wordTrace_append hprefix tailTrace_2514908
  have hstable : (prefixWord ++ tailWord_2514908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514908).length < 2 ^ (prefixWord ++ tailWord_2514908).sum := by decide
  have hdescent : baseEnd_2514908 < baseStart_2514908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514928 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_2514928 : Nat := 118140960795 + 2514928 * 2 ^ 59
def prefixEnd_2514928 : Nat := 4983230072969 + 3 ^ 40 * 2514928 * 2
def baseEnd_2514928 : Nat := 286970416766809236963125

theorem tailTrace_2514928 : CollatzResearch.WordTrace tailWord_2514928 prefixEnd_2514928 286970416766809236963125 := by
  unfold tailWord_2514928
  simp only [CollatzResearch.WordTrace]
  refine ⟨45863479916426423176016719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61151306555235230901355625 45863479916426423176016719)
  ·
    refine ⟨68795219874639634764025079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45863479916426423176016719 68795219874639634764025079)
    ·
      refine ⟨103192829811959452146037619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68795219874639634764025079 103192829811959452146037619)
      ·
        refine ⟨154789244717939178219056429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103192829811959452146037619 154789244717939178219056429)
        ·
          refine ⟨58045966769227191832146161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154789244717939178219056429 58045966769227191832146161)
          ·
            refine ⟨43534475076920393874109621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58045966769227191832146161 43534475076920393874109621)
            ·
              refine ⟨4081357038461286925697777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43534475076920393874109621 4081357038461286925697777)
              ·
                refine ⟨3061017778845965194273333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081357038461286925697777 3061017778845965194273333)
                ·
                  refine ⟨286970416766809236963125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061017778845965194273333 286970416766809236963125)
                  ·
                    rfl

theorem cell22_2514928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_2514928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514928 prefixEnd_2514928 := by exact prefixLift 2514928
  have htrace : WordTrace (prefixWord ++ tailWord_2514928) baseStart_2514928 baseEnd_2514928 := by
    simpa [prefixWord, tailWord_2514928, baseEnd_2514928] using wordTrace_append hprefix tailTrace_2514928
  have hstable : (prefixWord ++ tailWord_2514928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514928).length < 2 ^ (prefixWord ++ tailWord_2514928).sum := by decide
  have hdescent : baseEnd_2514928 < baseStart_2514928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514945 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 5]
def baseStart_2514945 : Nat := 118140960795 + 2514945 * 2 ^ 59
def prefixEnd_2514945 : Nat := 4983230072969 + 3 ^ 40 * 2514945 * 2
def baseEnd_2514945 : Nat := 286972356582615111071441

theorem tailTrace_2514945 : CollatzResearch.WordTrace tailWord_2514945 prefixEnd_2514945 286972356582615111071441 := by
  unfold tailWord_2514945
  simp only [CollatzResearch.WordTrace]
  refine ⟨91727579873791258255402289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61151719915860838836934859 91727579873791258255402289)
  ·
    refine ⟨68795684905343443691551717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91727579873791258255402289 68795684905343443691551717)
    ·
      refine ⟨12899190919751895692165947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68795684905343443691551717 12899190919751895692165947)
      ·
        refine ⟨19348786379627843538248921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12899190919751895692165947 19348786379627843538248921)
        ·
          refine ⟨14511589784720882653686691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19348786379627843538248921 14511589784720882653686691)
          ·
            refine ⟨21767384677081323980530037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14511589784720882653686691 21767384677081323980530037)
            ·
              refine ⟨2040692313476374123174691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21767384677081323980530037 2040692313476374123174691)
              ·
                refine ⟨3061038470214561184762037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040692313476374123174691 3061038470214561184762037)
                ·
                  refine ⟨286972356582615111071441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061038470214561184762037 286972356582615111071441)
                  ·
                    rfl

theorem cell22_2514945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_2514945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514945 prefixEnd_2514945 := by exact prefixLift 2514945
  have htrace : WordTrace (prefixWord ++ tailWord_2514945) baseStart_2514945 baseEnd_2514945 := by
    simpa [prefixWord, tailWord_2514945, baseEnd_2514945] using wordTrace_append hprefix tailTrace_2514945
  have hstable : (prefixWord ++ tailWord_2514945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514945).length < 2 ^ (prefixWord ++ tailWord_2514945).sum := by decide
  have hdescent : baseEnd_2514945 < baseStart_2514945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514990 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_2514990 : Nat := 118140960795 + 2514990 * 2 ^ 59
def prefixEnd_2514990 : Nat := 4983230072969 + 3 ^ 40 * 2514990 * 2
def baseEnd_2514990 : Nat := 286977491389160071946395

theorem tailTrace_2514990 : CollatzResearch.WordTrace tailWord_2514990 prefixEnd_2514990 286977491389160071946395 := by
  unfold tailWord_2514990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466152644828528867598803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61152814105752153960526949 11466152644828528867598803)
  ·
    refine ⟨17199228967242793301398205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11466152644828528867598803 17199228967242793301398205)
    ·
      refine ⟨6449710862716047488024327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17199228967242793301398205 6449710862716047488024327)
      ·
        refine ⟨9674566294074071232036491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6449710862716047488024327 9674566294074071232036491)
        ·
          refine ⟨14511849441111106848054737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9674566294074071232036491 14511849441111106848054737)
          ·
            refine ⟨10883887080833330136041053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14511849441111106848054737 10883887080833330136041053)
            ·
              refine ⟨4081457655312498801015395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10883887080833330136041053 4081457655312498801015395)
              ·
                refine ⟨6122186482968748201523093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4081457655312498801015395 6122186482968748201523093)
                ·
                  refine ⟨286977491389160071946395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6122186482968748201523093 286977491389160071946395)
                  ·
                    rfl

theorem cell22_2514990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_2514990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514990 prefixEnd_2514990 := by exact prefixLift 2514990
  have htrace : WordTrace (prefixWord ++ tailWord_2514990) baseStart_2514990 baseEnd_2514990 := by
    simpa [prefixWord, tailWord_2514990, baseEnd_2514990] using wordTrace_append hprefix tailTrace_2514990
  have hstable : (prefixWord ++ tailWord_2514990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514990).length < 2 ^ (prefixWord ++ tailWord_2514990).sum := by decide
  have hdescent : baseEnd_2514990 < baseStart_2514990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514996 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2514996 : Nat := 118140960795 + 2514996 * 2 ^ 59
def prefixEnd_2514996 : Nat := 4983230072969 + 3 ^ 40 * 2514996 * 2
def baseEnd_2514996 : Nat := 286978176030032733396389

theorem tailTrace_2514996 : CollatzResearch.WordTrace tailWord_2514996 prefixEnd_2514996 286978176030032733396389 := by
  unfold tailWord_2514996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45864719998303246982754421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61152959997737662643672561 45864719998303246982754421)
  ·
    refine ⟨4299817499840929404633227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45864719998303246982754421 4299817499840929404633227)
    ·
      refine ⟨6449726249761394106949841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4299817499840929404633227 6449726249761394106949841)
      ·
        refine ⟨4837294687321045580212381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6449726249761394106949841 4837294687321045580212381)
        ·
          refine ⟨1813985507745392092579643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4837294687321045580212381 1813985507745392092579643)
          ·
            refine ⟨2720978261618088138869465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813985507745392092579643 2720978261618088138869465)
            ·
              refine ⟨2040733696213566104152099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720978261618088138869465 2040733696213566104152099)
              ·
                refine ⟨3061100544320349156228149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040733696213566104152099 3061100544320349156228149)
                ·
                  refine ⟨286978176030032733396389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061100544320349156228149 286978176030032733396389)
                  ·
                    rfl

theorem cell22_2514996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2514996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2514996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2514996 prefixEnd_2514996 := by exact prefixLift 2514996
  have htrace : WordTrace (prefixWord ++ tailWord_2514996) baseStart_2514996 baseEnd_2514996 := by
    simpa [prefixWord, tailWord_2514996, baseEnd_2514996] using wordTrace_append hprefix tailTrace_2514996
  have hstable : (prefixWord ++ tailWord_2514996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514996).length < 2 ^ (prefixWord ++ tailWord_2514996).sum := by decide
  have hdescent : baseEnd_2514996 < baseStart_2514996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515037 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2515037 : Nat := 118140960795 + 2515037 * 2 ^ 59
def prefixEnd_2515037 : Nat := 4983230072969 + 3 ^ 40 * 2515037 * 2
def baseEnd_2515037 : Nat := 860948563227987759914041

theorem tailTrace_2515037 : CollatzResearch.WordTrace tailWord_2515037 prefixEnd_2515037 860948563227987759914041 := by
  unfold tailWord_2515037
  simp only [CollatzResearch.WordTrace]
  refine ⟨91730935389457957967751365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61153956926305305311834243 91730935389457957967751365)
  ·
    refine ⟨17199550385523367118953381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91730935389457957967751365 17199550385523367118953381)
    ·
      refine ⟨3224915697285631334803759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17199550385523367118953381 3224915697285631334803759)
      ·
        refine ⟨4837373545928447002205639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224915697285631334803759 4837373545928447002205639)
        ·
          refine ⟨7256060318892670503308459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4837373545928447002205639 7256060318892670503308459)
          ·
            refine ⟨10884090478339005754962689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7256060318892670503308459 10884090478339005754962689)
            ·
              refine ⟨8163067858754254316222017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10884090478339005754962689 8163067858754254316222017)
              ·
                refine ⟨6122300894065690737166513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8163067858754254316222017 6122300894065690737166513)
                ·
                  refine ⟨4591725670549268052874885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122300894065690737166513 4591725670549268052874885)
                  ·
                    refine ⟨860948563227987759914041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4591725670549268052874885 860948563227987759914041)
                    ·
                      rfl

theorem cell22_2515037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2515037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515037 prefixEnd_2515037 := by exact prefixLift 2515037
  have htrace : WordTrace (prefixWord ++ tailWord_2515037) baseStart_2515037 baseEnd_2515037 := by
    simpa [prefixWord, tailWord_2515037, baseEnd_2515037] using wordTrace_append hprefix tailTrace_2515037
  have hstable : (prefixWord ++ tailWord_2515037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515037).length < 2 ^ (prefixWord ++ tailWord_2515037).sum := by decide
  have hdescent : baseEnd_2515037 < baseStart_2515037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515127 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 1, 4]
def baseStart_2515127 : Nat := 118140960795 + 2515127 * 2 ^ 59
def prefixEnd_2515127 : Nat := 4983230072969 + 3 ^ 40 * 2515127 * 2
def baseEnd_2515127 : Nat := 860979372067257525163765

theorem tailTrace_2515127 : CollatzResearch.WordTrace tailWord_2515127 prefixEnd_2515127 860979372067257525163765 := by
  unfold tailWord_2515127
  simp only [CollatzResearch.WordTrace]
  refine ⟨91734217959131903338527635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61156145306087935559018423 91734217959131903338527635)
  ·
    refine ⟨137601326938697855007791453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91734217959131903338527635 137601326938697855007791453)
    ·
      refine ⟨51600497602011695627921795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137601326938697855007791453 51600497602011695627921795)
      ·
        refine ⟨77400746403017543441882693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51600497602011695627921795 77400746403017543441882693)
        ·
          refine ⟨14512639950565789395353005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77400746403017543441882693 14512639950565789395353005)
          ·
            refine ⟨5442239981462171023257377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14512639950565789395353005 5442239981462171023257377)
            ·
              refine ⟨4081679986096628267443033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5442239981462171023257377 4081679986096628267443033)
              ·
                refine ⟨3061259989572471200582275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081679986096628267443033 3061259989572471200582275)
                ·
                  refine ⟨4591889984358706800873413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061259989572471200582275 4591889984358706800873413)
                  ·
                    refine ⟨860979372067257525163765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4591889984358706800873413 860979372067257525163765)
                    ·
                      rfl

theorem cell22_2515127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_2515127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515127 prefixEnd_2515127 := by exact prefixLift 2515127
  have htrace : WordTrace (prefixWord ++ tailWord_2515127) baseStart_2515127 baseEnd_2515127 := by
    simpa [prefixWord, tailWord_2515127, baseEnd_2515127] using wordTrace_append hprefix tailTrace_2515127
  have hstable : (prefixWord ++ tailWord_2515127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515127).length < 2 ^ (prefixWord ++ tailWord_2515127).sum := by decide
  have hdescent : baseEnd_2515127 < baseStart_2515127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515153 : List Nat := [1, 2, 2, 1, 2, 2, 12]
def baseStart_2515153 : Nat := 118140960795 + 2515153 * 2 ^ 59
def prefixEnd_2515153 : Nat := 4983230072969 + 3 ^ 40 * 2515153 * 2
def baseEnd_2515153 : Nat := 31888454533281560148655

theorem tailTrace_2515153 : CollatzResearch.WordTrace tailWord_2515153 prefixEnd_2515153 31888454533281560148655 := by
  unfold tailWord_2515153
  simp only [CollatzResearch.WordTrace]
  refine ⟨91735166257037709778974113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61156777504691806519316075 91735166257037709778974113)
  ·
    refine ⟨68801374692778282334230585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91735166257037709778974113 68801374692778282334230585)
    ·
      refine ⟨51601031019583711750672939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68801374692778282334230585 51601031019583711750672939)
      ·
        refine ⟨77401546529375567626009409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51601031019583711750672939 77401546529375567626009409)
        ·
          refine ⟨58051159897031675719507057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77401546529375567626009409 58051159897031675719507057)
          ·
            refine ⟨43538369922773756789630293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58051159897031675719507057 43538369922773756789630293)
            ·
              refine ⟨31888454533281560148655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 43538369922773756789630293 31888454533281560148655)
              ·
                rfl

theorem cell22_2515153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 12].length) (baseStart_2515153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515153 prefixEnd_2515153 := by exact prefixLift 2515153
  have htrace : WordTrace (prefixWord ++ tailWord_2515153) baseStart_2515153 baseEnd_2515153 := by
    simpa [prefixWord, tailWord_2515153, baseEnd_2515153] using wordTrace_append hprefix tailTrace_2515153
  have hstable : (prefixWord ++ tailWord_2515153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515153).length < 2 ^ (prefixWord ++ tailWord_2515153).sum := by decide
  have hdescent : baseEnd_2515153 < baseStart_2515153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515232 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_2515232 : Nat := 118140960795 + 2515232 * 2 ^ 59
def prefixEnd_2515232 : Nat := 4983230072969 + 3 ^ 40 * 2515232 * 2
def baseEnd_2515232 : Nat := 287005105237690750429481

theorem tailTrace_2515232 : CollatzResearch.WordTrace tailWord_2515232 prefixEnd_2515232 287005105237690750429481 := by
  unfold tailWord_2515232
  simp only [CollatzResearch.WordTrace]
  refine ⟨45869023811875753135549975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61158698415834337514066633 45869023811875753135549975)
  ·
    refine ⟨68803535717813629703324963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45869023811875753135549975 68803535717813629703324963)
    ·
      refine ⟨103205303576720444554987445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68803535717813629703324963 103205303576720444554987445)
      ·
        refine ⟨9675497210317541677030073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103205303576720444554987445 9675497210317541677030073)
        ·
          refine ⟨7256622907738156257772555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9675497210317541677030073 7256622907738156257772555)
          ·
            refine ⟨10884934361607234386658833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7256622907738156257772555 10884934361607234386658833)
            ·
              refine ⟨8163700771205425789994125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10884934361607234386658833 8163700771205425789994125)
              ·
                refine ⟨3061387789202034671247797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8163700771205425789994125 3061387789202034671247797)
                ·
                  refine ⟨287005105237690750429481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061387789202034671247797 287005105237690750429481)
                  ·
                    rfl

theorem cell22_2515232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_2515232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515232 prefixEnd_2515232 := by exact prefixLift 2515232
  have htrace : WordTrace (prefixWord ++ tailWord_2515232) baseStart_2515232 baseEnd_2515232 := by
    simpa [prefixWord, tailWord_2515232, baseEnd_2515232] using wordTrace_append hprefix tailTrace_2515232
  have hstable : (prefixWord ++ tailWord_2515232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515232).length < 2 ^ (prefixWord ++ tailWord_2515232).sum := by decide
  have hdescent : baseEnd_2515232 < baseStart_2515232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515260 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_2515260 : Nat := 118140960795 + 2515260 * 2 ^ 59
def prefixEnd_2515260 : Nat := 4983230072969 + 3 ^ 40 * 2515260 * 2
def baseEnd_2515260 : Nat := 287008300228429837196119

theorem tailTrace_2515260 : CollatzResearch.WordTrace tailWord_2515260 prefixEnd_2515260 287008300228429837196119 := by
  unfold tailWord_2515260
  simp only [CollatzResearch.WordTrace]
  refine ⟨45869534433825033526559617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61159379245100044702079489 45869534433825033526559617)
  ·
    refine ⟨34402150825368775144919713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45869534433825033526559617 34402150825368775144919713)
    ·
      refine ⟨25801613119026581358689785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34402150825368775144919713 25801613119026581358689785)
      ·
        refine ⟨19351209839269936019017339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25801613119026581358689785 19351209839269936019017339)
        ·
          refine ⟨29026814758904904028526009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19351209839269936019017339 29026814758904904028526009)
          ·
            refine ⟨21770111069178678021394507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29026814758904904028526009 21770111069178678021394507)
            ·
              refine ⟨32655166603768017032091761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21770111069178678021394507 32655166603768017032091761)
              ·
                refine ⟨24491374952826012774068821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32655166603768017032091761 24491374952826012774068821)
                ·
                  refine ⟨287008300228429837196119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24491374952826012774068821 287008300228429837196119)
                  ·
                    rfl

theorem cell22_2515260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_2515260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515260 prefixEnd_2515260 := by exact prefixLift 2515260
  have htrace : WordTrace (prefixWord ++ tailWord_2515260) baseStart_2515260 baseEnd_2515260 := by
    simpa [prefixWord, tailWord_2515260, baseEnd_2515260] using wordTrace_append hprefix tailTrace_2515260
  have hstable : (prefixWord ++ tailWord_2515260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515260).length < 2 ^ (prefixWord ++ tailWord_2515260).sum := by decide
  have hdescent : baseEnd_2515260 < baseStart_2515260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515305 : List Nat := [1, 2, 1, 1, 1, 3, 5, 8]
def baseStart_2515305 : Nat := 118140960795 + 2515305 * 2 ^ 59
def prefixEnd_2515305 : Nat := 4983230072969 + 3 ^ 40 * 2515305 * 2
def baseEnd_2515305 : Nat := 95671145011658266023691

theorem tailTrace_2515305 : CollatzResearch.WordTrace tailWord_2515305 prefixEnd_2515305 95671145011658266023691 := by
  unfold tailWord_2515305
  simp only [CollatzResearch.WordTrace]
  refine ⟨91740710152487039738507369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61160473434991359825671579 91740710152487039738507369)
  ·
    refine ⟨68805532614365279803880527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91740710152487039738507369 68805532614365279803880527)
    ·
      refine ⟨103208298921547919705820791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68805532614365279803880527 103208298921547919705820791)
      ·
        refine ⟨154812448382321879558731187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103208298921547919705820791 154812448382321879558731187)
        ·
          refine ⟨232218672573482819338096781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154812448382321879558731187 232218672573482819338096781)
          ·
            refine ⟨87082002215056057251786293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232218672573482819338096781 87082002215056057251786293)
            ·
              refine ⟨8163937707661505367354965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87082002215056057251786293 8163937707661505367354965)
              ·
                refine ⟨95671145011658266023691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8163937707661505367354965 95671145011658266023691)
                ·
                  rfl

theorem cell22_2515305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 8].length) (baseStart_2515305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515305 prefixEnd_2515305 := by exact prefixLift 2515305
  have htrace : WordTrace (prefixWord ++ tailWord_2515305) baseStart_2515305 baseEnd_2515305 := by
    simpa [prefixWord, tailWord_2515305, baseEnd_2515305] using wordTrace_append hprefix tailTrace_2515305
  have hstable : (prefixWord ++ tailWord_2515305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515305).length < 2 ^ (prefixWord ++ tailWord_2515305).sum := by decide
  have hdescent : baseEnd_2515305 < baseStart_2515305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515388 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_2515388 : Nat := 118140960795 + 2515388 * 2 ^ 59
def prefixEnd_2515388 : Nat := 4983230072969 + 3 ^ 40 * 2515388 * 2
def baseEnd_2515388 : Nat := 861068717701139844387965

theorem tailTrace_2515388 : CollatzResearch.WordTrace tailWord_2515388 prefixEnd_2515388 861068717701139844387965 := by
  unfold tailWord_2515388
  simp only [CollatzResearch.WordTrace]
  refine ⟨45871868705593172456889409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61162491607457563275852545 45871868705593172456889409)
  ·
    refine ⟨34403901529194879342667057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45871868705593172456889409 34403901529194879342667057)
    ·
      refine ⟨25802926146896159507000293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34403901529194879342667057 25802926146896159507000293)
      ·
        refine ⟨4838048652543029907562555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25802926146896159507000293 4838048652543029907562555)
        ·
          refine ⟨7257072978814544861343833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838048652543029907562555 7257072978814544861343833)
          ·
            refine ⟨5442804734110908646007875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7257072978814544861343833 5442804734110908646007875)
            ·
              refine ⟨8164207101166362969011813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442804734110908646007875 8164207101166362969011813)
              ·
                refine ⟨1530788831468693056689715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8164207101166362969011813 1530788831468693056689715)
                ·
                  refine ⟨2296183247203039585034573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530788831468693056689715 2296183247203039585034573)
                  ·
                    refine ⟨861068717701139844387965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296183247203039585034573 861068717701139844387965)
                    ·
                      rfl

theorem cell22_2515388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_2515388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515388 prefixEnd_2515388 := by exact prefixLift 2515388
  have htrace : WordTrace (prefixWord ++ tailWord_2515388) baseStart_2515388 baseEnd_2515388 := by
    simpa [prefixWord, tailWord_2515388, baseEnd_2515388] using wordTrace_append hprefix tailTrace_2515388
  have hstable : (prefixWord ++ tailWord_2515388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515388).length < 2 ^ (prefixWord ++ tailWord_2515388).sum := by decide
  have hdescent : baseEnd_2515388 < baseStart_2515388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515446 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2515446 : Nat := 118140960795 + 2515446 * 2 ^ 59
def prefixEnd_2515446 : Nat := 4983230072969 + 3 ^ 40 * 2515446 * 2
def baseEnd_2515446 : Nat := 287029524095482342145929

theorem tailTrace_2515446 : CollatzResearch.WordTrace tailWord_2515446 prefixEnd_2515446 287029524095482342145929 := by
  unfold tailWord_2515446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734115802811013801211887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61163901896650813879593461 5734115802811013801211887)
  ·
    refine ⟨8601173704216520701817831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5734115802811013801211887 8601173704216520701817831)
    ·
      refine ⟨12901760556324781052726747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8601173704216520701817831 12901760556324781052726747)
      ·
        refine ⟨19352640834487171579090121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12901760556324781052726747 19352640834487171579090121)
        ·
          refine ⟨14514480625865378684317591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19352640834487171579090121 14514480625865378684317591)
          ·
            refine ⟨21771720938798068026476387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14514480625865378684317591 21771720938798068026476387)
            ·
              refine ⟨32657581408197102039714581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21771720938798068026476387 32657581408197102039714581)
              ·
                refine ⟨1530824128509239158111621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32657581408197102039714581 1530824128509239158111621)
                ·
                  refine ⟨287029524095482342145929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530824128509239158111621 287029524095482342145929)
                  ·
                    rfl

theorem cell22_2515446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2515446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515446 prefixEnd_2515446 := by exact prefixLift 2515446
  have htrace : WordTrace (prefixWord ++ tailWord_2515446) baseStart_2515446 baseEnd_2515446 := by
    simpa [prefixWord, tailWord_2515446, baseEnd_2515446] using wordTrace_append hprefix tailTrace_2515446
  have hstable : (prefixWord ++ tailWord_2515446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515446).length < 2 ^ (prefixWord ++ tailWord_2515446).sum := by decide
  have hdescent : baseEnd_2515446 < baseStart_2515446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515476 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2515476 : Nat := 118140960795 + 2515476 * 2 ^ 59
def prefixEnd_2515476 : Nat := 4983230072969 + 3 ^ 40 * 2515476 * 2
def baseEnd_2515476 : Nat := 861098841899536948187695

theorem tailTrace_2515476 : CollatzResearch.WordTrace tailWord_2515476 prefixEnd_2515476 861098841899536948187695 := by
  unfold tailWord_2515476
  simp only [CollatzResearch.WordTrace]
  refine ⟨45873473517433767971491141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61164631356578357295321521 45873473517433767971491141)
  ·
    refine ⟨8601276284518831494654589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45873473517433767971491141 8601276284518831494654589)
    ·
      refine ⟨3225478606694561810495471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8601276284518831494654589 3225478606694561810495471)
      ·
        refine ⟨4838217910041842715743207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225478606694561810495471 4838217910041842715743207)
        ·
          refine ⟨7257326865062764073614811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838217910041842715743207 7257326865062764073614811)
          ·
            refine ⟨10885990297594146110422217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7257326865062764073614811 10885990297594146110422217)
            ·
              refine ⟨8164492723195609582816663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10885990297594146110422217 8164492723195609582816663)
              ·
                refine ⟨12246739084793414374224995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8164492723195609582816663 12246739084793414374224995)
                ·
                  refine ⟨18370108627190121561337493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12246739084793414374224995 18370108627190121561337493)
                  ·
                    refine ⟨861098841899536948187695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18370108627190121561337493 861098841899536948187695)
                    ·
                      rfl

theorem cell22_2515476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2515476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515476 prefixEnd_2515476 := by exact prefixLift 2515476
  have htrace : WordTrace (prefixWord ++ tailWord_2515476) baseStart_2515476 baseEnd_2515476 := by
    simpa [prefixWord, tailWord_2515476, baseEnd_2515476] using wordTrace_append hprefix tailTrace_2515476
  have hstable : (prefixWord ++ tailWord_2515476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515476).length < 2 ^ (prefixWord ++ tailWord_2515476).sum := by decide
  have hdescent : baseEnd_2515476 < baseStart_2515476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515487 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_2515487 : Nat := 118140960795 + 2515487 * 2 ^ 59
def prefixEnd_2515487 : Nat := 4983230072969 + 3 ^ 40 * 2515487 * 2
def baseEnd_2515487 : Nat := 861102607424336586162661

theorem tailTrace_2515487 : CollatzResearch.WordTrace tailWord_2515487 prefixEnd_2515487 861102607424336586162661 := by
  unfold tailWord_2515487
  simp only [CollatzResearch.WordTrace]
  refine ⟨91747348237827684821632715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61164898825218456547755143 91747348237827684821632715)
  ·
    refine ⟨137621022356741527232449073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91747348237827684821632715 137621022356741527232449073)
    ·
      refine ⟨103215766767556145424336805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137621022356741527232449073 103215766767556145424336805)
      ·
        refine ⟨19352956268916777267063151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103215766767556145424336805 19352956268916777267063151)
        ·
          refine ⟨29029434403375165900594727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19352956268916777267063151 29029434403375165900594727)
          ·
            refine ⟨43544151605062748850892091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29029434403375165900594727 43544151605062748850892091)
            ·
              refine ⟨65316227407594123276338137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43544151605062748850892091 65316227407594123276338137)
              ·
                refine ⟨48987170555695592457253603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65316227407594123276338137 48987170555695592457253603)
                ·
                  refine ⟨73480755833543388685880405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48987170555695592457253603 73480755833543388685880405)
                  ·
                    refine ⟨861102607424336586162661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73480755833543388685880405 861102607424336586162661)
                    ·
                      rfl

theorem cell22_2515487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_2515487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515487 prefixEnd_2515487 := by exact prefixLift 2515487
  have htrace : WordTrace (prefixWord ++ tailWord_2515487) baseStart_2515487 baseEnd_2515487 := by
    simpa [prefixWord, tailWord_2515487, baseEnd_2515487] using wordTrace_append hprefix tailTrace_2515487
  have hstable : (prefixWord ++ tailWord_2515487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515487).length < 2 ^ (prefixWord ++ tailWord_2515487).sum := by decide
  have hdescent : baseEnd_2515487 < baseStart_2515487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515506 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_2515506 : Nat := 118140960795 + 2515506 * 2 ^ 59
def prefixEnd_2515506 : Nat := 4983230072969 + 3 ^ 40 * 2515506 * 2
def baseEnd_2515506 : Nat := 861109111512626869937603

theorem tailTrace_2515506 : CollatzResearch.WordTrace tailWord_2515506 prefixEnd_2515506 861109111512626869937603 := by
  unfold tailWord_2515506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22937010306189712766643593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61165360816505900711049581 22937010306189712766643593)
  ·
    refine ⟨17202757729642284574982695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22937010306189712766643593 17202757729642284574982695)
    ·
      refine ⟨25804136594463426862474043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17202757729642284574982695 25804136594463426862474043)
      ·
        refine ⟨38706204891695140293711065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25804136594463426862474043 38706204891695140293711065)
        ·
          refine ⟨29029653668771355220283299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38706204891695140293711065 29029653668771355220283299)
          ·
            refine ⟨43544480503157032830424949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29029653668771355220283299 43544480503157032830424949)
            ·
              refine ⟨4082295047170971827852339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43544480503157032830424949 4082295047170971827852339)
              ·
                refine ⟨6123442570756457741778509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082295047170971827852339 6123442570756457741778509)
                ·
                  refine ⟨2296290964033671653166941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6123442570756457741778509 2296290964033671653166941)
                  ·
                    refine ⟨861109111512626869937603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296290964033671653166941 861109111512626869937603)
                    ·
                      rfl

theorem cell22_2515506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_2515506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515506 prefixEnd_2515506 := by exact prefixLift 2515506
  have htrace : WordTrace (prefixWord ++ tailWord_2515506) baseStart_2515506 baseEnd_2515506 := by
    simpa [prefixWord, tailWord_2515506, baseEnd_2515506] using wordTrace_append hprefix tailTrace_2515506
  have hstable : (prefixWord ++ tailWord_2515506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515506).length < 2 ^ (prefixWord ++ tailWord_2515506).sum := by decide
  have hdescent : baseEnd_2515506 < baseStart_2515506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515508 : List Nat := [2, 5, 1, 3, 1, 1, 2, 7]
def baseStart_2515508 : Nat := 118140960795 + 2515508 * 2 ^ 59
def prefixEnd_2515508 : Nat := 4983230072969 + 3 ^ 40 * 2515508 * 2
def baseEnd_2515508 : Nat := 95678866239277725709733

theorem tailTrace_2515508 : CollatzResearch.WordTrace tailWord_2515508 prefixEnd_2515508 95678866239277725709733 := by
  unfold tailWord_2515508
  simp only [CollatzResearch.WordTrace]
  refine ⟨45874057085375802704073589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61165409447167736938764785 45874057085375802704073589)
  ·
    refine ⟨4300692851753981503506899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45874057085375802704073589 4300692851753981503506899)
    ·
      refine ⟨6451039277630972255260349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4300692851753981503506899 6451039277630972255260349)
      ·
        refine ⟨2419139729111614595722631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6451039277630972255260349 2419139729111614595722631)
        ·
          refine ⟨3628709593667421893583947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419139729111614595722631 3628709593667421893583947)
          ·
            refine ⟨5443064390501132840375921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628709593667421893583947 5443064390501132840375921)
            ·
              refine ⟨4082298292875849630281941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5443064390501132840375921 4082298292875849630281941)
              ·
                refine ⟨95678866239277725709733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4082298292875849630281941 95678866239277725709733)
                ·
                  rfl

theorem cell22_2515508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 7].length) (baseStart_2515508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2515508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2515508 prefixEnd_2515508 := by exact prefixLift 2515508
  have htrace : WordTrace (prefixWord ++ tailWord_2515508) baseStart_2515508 baseEnd_2515508 := by
    simpa [prefixWord, tailWord_2515508, baseEnd_2515508] using wordTrace_append hprefix tailTrace_2515508
  have hstable : (prefixWord ++ tailWord_2515508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515508).length < 2 ^ (prefixWord ++ tailWord_2515508).sum := by decide
  have hdescent : baseEnd_2515508 < baseStart_2515508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
