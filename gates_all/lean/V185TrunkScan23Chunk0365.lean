import V185TrunkScan23Chunk0364

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2158697 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_2158697 : Nat := 118140960795 + 2158697 * 2 ^ 59
def prefixEnd_2158697 : Nat := 4983230072969 + 3 ^ 40 * 2158697 * 2
def baseEnd_2158697 : Nat := 1108449148418845821759839

theorem tailTrace_2158697 : CollatzResearch.WordTrace tailWord_2158697 prefixEnd_2158697 1108449148418845821759839 := by
  unfold tailWord_2158697
  simp only [CollatzResearch.WordTrace]
  refine ⟨78734147860416919940906345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52489431906944613293937563 78734147860416919940906345)
  ·
    refine ⟨59050610895312689955679759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78734147860416919940906345 59050610895312689955679759)
    ·
      refine ⟨88575916342969034933519639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59050610895312689955679759 88575916342969034933519639)
      ·
        refine ⟨132863874514453552400279459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88575916342969034933519639 132863874514453552400279459)
        ·
          refine ⟨199295811771680328600419189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132863874514453552400279459 199295811771680328600419189)
          ·
            refine ⟨18683982353595030806289299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 199295811771680328600419189 18683982353595030806289299)
            ·
              refine ⟨28025973530392546209433949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18683982353595030806289299 28025973530392546209433949)
              ·
                refine ⟨10509740073897204828537731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28025973530392546209433949 10509740073897204828537731)
                ·
                  refine ⟨15764610110845807242806597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10509740073897204828537731 15764610110845807242806597)
                  ·
                    refine ⟨2955864395783588858026237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15764610110845807242806597 2955864395783588858026237)
                    ·
                      refine ⟨1108449148418845821759839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955864395783588858026237 1108449148418845821759839)
                      ·
                        rfl

theorem cell23_2158697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_2158697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158697 prefixEnd_2158697 := by exact prefixLift 2158697
  have htrace : WordTrace (prefixWord ++ tailWord_2158697) baseStart_2158697 baseEnd_2158697 := by
    simpa [prefixWord, tailWord_2158697, baseEnd_2158697] using wordTrace_append hprefix tailTrace_2158697
  have hstable : (prefixWord ++ tailWord_2158697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158697).length < 2 ^ (prefixWord ++ tailWord_2158697).sum := by decide
  have hdescent : baseEnd_2158697 < baseStart_2158697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158717 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 8]
def baseStart_2158717 : Nat := 118140960795 + 2158717 * 2 ^ 59
def prefixEnd_2158717 : Nat := 4983230072969 + 3 ^ 40 * 2158717 * 2
def baseEnd_2158717 : Nat := 123162157559103971501083

theorem tailTrace_2158717 : CollatzResearch.WordTrace tailWord_2158717 prefixEnd_2158717 123162157559103971501083 := by
  unfold tailWord_2158717
  simp only [CollatzResearch.WordTrace]
  refine ⟨78734877320344463356634405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52489918213562975571089603 78734877320344463356634405)
  ·
    refine ⟨14762789497564586879368951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78734877320344463356634405 14762789497564586879368951)
    ·
      refine ⟨22144184246346880319053427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14762789497564586879368951 22144184246346880319053427)
      ·
        refine ⟨33216276369520320478580141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22144184246346880319053427 33216276369520320478580141)
        ·
          refine ⟨12456103638570120179467553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33216276369520320478580141 12456103638570120179467553)
          ·
            refine ⟨9342077728927590134600665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12456103638570120179467553 9342077728927590134600665)
            ·
              refine ⟨7006558296695692600950499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9342077728927590134600665 7006558296695692600950499)
              ·
                refine ⟨10509837445043538901425749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7006558296695692600950499 10509837445043538901425749)
                ·
                  refine ⟨123162157559103971501083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10509837445043538901425749 123162157559103971501083)
                  ·
                    rfl

theorem cell23_2158717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_2158717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158717 prefixEnd_2158717 := by exact prefixLift 2158717
  have htrace : WordTrace (prefixWord ++ tailWord_2158717) baseStart_2158717 baseEnd_2158717 := by
    simpa [prefixWord, tailWord_2158717, baseEnd_2158717] using wordTrace_append hprefix tailTrace_2158717
  have hstable : (prefixWord ++ tailWord_2158717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158717).length < 2 ^ (prefixWord ++ tailWord_2158717).sum := by decide
  have hdescent : baseEnd_2158717 < baseStart_2158717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158742 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2158742 : Nat := 118140960795 + 2158742 * 2 ^ 59
def prefixEnd_2158742 : Nat := 4983230072969 + 3 ^ 40 * 2158742 * 2
def baseEnd_2158742 : Nat := 369490751682766048565711

theorem tailTrace_2158742 : CollatzResearch.WordTrace tailWord_2158742 prefixEnd_2158742 369490751682766048565711 := by
  unfold tailWord_2158742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920986821578368289143405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52490526096835928417529653 4920986821578368289143405)
  ·
    refine ⟨1845370058091888108428777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4920986821578368289143405 1845370058091888108428777)
    ·
      refine ⟨1384027543568916081321583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1845370058091888108428777 1384027543568916081321583)
      ·
        refine ⟨2076041315353374121982375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384027543568916081321583 2076041315353374121982375)
        ·
          refine ⟨3114061973030061182973563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076041315353374121982375 3114061973030061182973563)
          ·
            refine ⟨4671092959545091774460345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114061973030061182973563 4671092959545091774460345)
            ·
              refine ⟨3503319719658818830845259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671092959545091774460345 3503319719658818830845259)
              ·
                refine ⟨5254979579488228246267889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503319719658818830845259 5254979579488228246267889)
                ·
                  refine ⟨3941234684616171184700917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254979579488228246267889 3941234684616171184700917)
                  ·
                    refine ⟨369490751682766048565711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3941234684616171184700917 369490751682766048565711)
                    ·
                      rfl

theorem cell23_2158742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2158742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158742 prefixEnd_2158742 := by exact prefixLift 2158742
  have htrace : WordTrace (prefixWord ++ tailWord_2158742) baseStart_2158742 baseEnd_2158742 := by
    simpa [prefixWord, tailWord_2158742, baseEnd_2158742] using wordTrace_append hprefix tailTrace_2158742
  have hstable : (prefixWord ++ tailWord_2158742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158742).length < 2 ^ (prefixWord ++ tailWord_2158742).sum := by decide
  have hdescent : baseEnd_2158742 < baseStart_2158742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158777 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_2158777 : Nat := 118140960795 + 2158777 * 2 ^ 59
def prefixEnd_2158777 : Nat := 4983230072969 + 3 ^ 40 * 2158777 * 2
def baseEnd_2158777 : Nat := 369496742290401836253157

theorem tailTrace_2158777 : CollatzResearch.WordTrace tailWord_2158777 prefixEnd_2158777 369496742290401836253157 := by
  unfold tailWord_2158777
  simp only [CollatzResearch.WordTrace]
  refine ⟨78737065700127093603818585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52491377133418062402545723 78737065700127093603818585)
  ·
    refine ⟨59052799275095320202863939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78737065700127093603818585 59052799275095320202863939)
    ·
      refine ⟨88579198912642980304295909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59052799275095320202863939 88579198912642980304295909)
      ·
        refine ⟨16608599796120558807055483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88579198912642980304295909 16608599796120558807055483)
        ·
          refine ⟨24912899694180838210583225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16608599796120558807055483 24912899694180838210583225)
          ·
            refine ⟨18684674770635628657937419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24912899694180838210583225 18684674770635628657937419)
            ·
              refine ⟨28027012155953442986906129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18684674770635628657937419 28027012155953442986906129)
              ·
                refine ⟨21020259116965082240179597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28027012155953442986906129 21020259116965082240179597)
                ·
                  refine ⟨7882597168861905840067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21020259116965082240179597 7882597168861905840067349)
                  ·
                    refine ⟨369496742290401836253157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7882597168861905840067349 369496742290401836253157)
                    ·
                      rfl

theorem cell23_2158777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_2158777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158777 prefixEnd_2158777 := by exact prefixLift 2158777
  have htrace : WordTrace (prefixWord ++ tailWord_2158777) baseStart_2158777 baseEnd_2158777 := by
    simpa [prefixWord, tailWord_2158777, baseEnd_2158777] using wordTrace_append hprefix tailTrace_2158777
  have hstable : (prefixWord ++ tailWord_2158777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158777).length < 2 ^ (prefixWord ++ tailWord_2158777).sum := by decide
  have hdescent : baseEnd_2158777 < baseStart_2158777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158784 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_2158784 : Nat := 118140960795 + 2158784 * 2 ^ 59
def prefixEnd_2158784 : Nat := 4983230072969 + 3 ^ 40 * 2158784 * 2
def baseEnd_2158784 : Nat := 1108493821235786981371939

theorem tailTrace_2158784 : CollatzResearch.WordTrace tailWord_2158784 prefixEnd_2158784 1108493821235786981371939 := by
  unfold tailWord_2158784
  simp only [CollatzResearch.WordTrace]
  refine ⟨39368660505550866899661703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52491547340734489199548937 39368660505550866899661703)
  ·
    refine ⟨59052990758326300349492555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39368660505550866899661703 59052990758326300349492555)
    ·
      refine ⟨88579486137489450524238833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59052990758326300349492555 88579486137489450524238833)
      ·
        refine ⟨66434614603117087893179125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88579486137489450524238833 66434614603117087893179125)
        ·
          refine ⟨6228245119042226989985543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66434614603117087893179125 6228245119042226989985543)
          ·
            refine ⟨9342367678563340484978315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6228245119042226989985543 9342367678563340484978315)
            ·
              refine ⟨14013551517845010727467473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9342367678563340484978315 14013551517845010727467473)
              ·
                refine ⟨10510163638383758045600605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14013551517845010727467473 10510163638383758045600605)
                ·
                  refine ⟨3941311364393909267100227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10510163638383758045600605 3941311364393909267100227)
                  ·
                    refine ⟨5911967046590863900650341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3941311364393909267100227 5911967046590863900650341)
                    ·
                      refine ⟨1108493821235786981371939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5911967046590863900650341 1108493821235786981371939)
                      ·
                        rfl

theorem cell23_2158784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_2158784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158784 prefixEnd_2158784 := by exact prefixLift 2158784
  have htrace : WordTrace (prefixWord ++ tailWord_2158784) baseStart_2158784 baseEnd_2158784 := by
    simpa [prefixWord, tailWord_2158784, baseEnd_2158784] using wordTrace_append hprefix tailTrace_2158784
  have hstable : (prefixWord ++ tailWord_2158784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158784).length < 2 ^ (prefixWord ++ tailWord_2158784).sum := by decide
  have hdescent : baseEnd_2158784 < baseStart_2158784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158794 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_2158794 : Nat := 118140960795 + 2158794 * 2 ^ 59
def prefixEnd_2158794 : Nat := 4983230072969 + 3 ^ 40 * 2158794 * 2
def baseEnd_2158794 : Nat := 369499652014110647415631

theorem tailTrace_2158794 : CollatzResearch.WordTrace tailWord_2158794 prefixEnd_2158794 369499652014110647415631 := by
  unfold tailWord_2158794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19684421435266376376796859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52491790494043670338124957 19684421435266376376796859)
  ·
    refine ⟨29526632152899564565195289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19684421435266376376796859 29526632152899564565195289)
    ·
      refine ⟨22144974114674673423896467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29526632152899564565195289 22144974114674673423896467)
      ·
        refine ⟨33217461172012010135844701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22144974114674673423896467 33217461172012010135844701)
        ·
          refine ⟨12456547939504503800941763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33217461172012010135844701 12456547939504503800941763)
          ·
            refine ⟨18684821909256755701412645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12456547939504503800941763 18684821909256755701412645)
            ·
              refine ⟨3503404107985641694014871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18684821909256755701412645 3503404107985641694014871)
              ·
                refine ⟨5255106161978462541022307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503404107985641694014871 5255106161978462541022307)
                ·
                  refine ⟨7882659242967693811533461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255106161978462541022307 7882659242967693811533461)
                  ·
                    refine ⟨369499652014110647415631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7882659242967693811533461 369499652014110647415631)
                    ·
                      rfl

theorem cell23_2158794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_2158794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158794 prefixEnd_2158794 := by exact prefixLift 2158794
  have htrace : WordTrace (prefixWord ++ tailWord_2158794) baseStart_2158794 baseEnd_2158794 := by
    simpa [prefixWord, tailWord_2158794, baseEnd_2158794] using wordTrace_append hprefix tailTrace_2158794
  have hstable : (prefixWord ++ tailWord_2158794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158794).length < 2 ^ (prefixWord ++ tailWord_2158794).sum := by decide
  have hdescent : baseEnd_2158794 < baseStart_2158794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158801 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 5, 2, 2]
def baseStart_2158801 : Nat := 118140960795 + 2158801 * 2 ^ 59
def prefixEnd_2158801 : Nat := 4983230072969 + 3 ^ 40 * 2158801 * 2
def baseEnd_2158801 : Nat := 1108502550406913414859361

theorem tailTrace_2158801 : CollatzResearch.WordTrace tailWord_2158801 prefixEnd_2158801 1108502550406913414859361 := by
  unfold tailWord_2158801
  simp only [CollatzResearch.WordTrace]
  refine ⟨78737941052040145702692257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52491960701360097135128171 78737941052040145702692257)
  ·
    refine ⟨59053455789030109277019193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78737941052040145702692257 59053455789030109277019193)
    ·
      refine ⟨44290091841772581957764395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59053455789030109277019193 44290091841772581957764395)
      ·
        refine ⟨66435137762658872936646593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44290091841772581957764395 66435137762658872936646593)
        ·
          refine ⟨49826353321994154702484945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66435137762658872936646593 49826353321994154702484945)
          ·
            refine ⟨37369764991495616026863709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49826353321994154702484945 37369764991495616026863709)
            ·
              refine ⟨14013661871810856010073891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37369764991495616026863709 14013661871810856010073891)
              ·
                refine ⟨21020492807716284015110837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14013661871810856010073891 21020492807716284015110837)
                ·
                  refine ⟨1970671200723401626416641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21020492807716284015110837 1970671200723401626416641)
                  ·
                    refine ⟨1478003400542551219812481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1970671200723401626416641 1478003400542551219812481)
                    ·
                      refine ⟨1108502550406913414859361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478003400542551219812481 1108502550406913414859361)
                      ·
                        rfl

theorem cell23_2158801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_2158801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158801 prefixEnd_2158801 := by exact prefixLift 2158801
  have htrace : WordTrace (prefixWord ++ tailWord_2158801) baseStart_2158801 baseEnd_2158801 := by
    simpa [prefixWord, tailWord_2158801, baseEnd_2158801] using wordTrace_append hprefix tailTrace_2158801
  have hstable : (prefixWord ++ tailWord_2158801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158801).length < 2 ^ (prefixWord ++ tailWord_2158801).sum := by decide
  have hdescent : baseEnd_2158801 < baseStart_2158801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158805 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2158805 : Nat := 118140960795 + 2158805 * 2 ^ 59
def prefixEnd_2158805 : Nat := 4983230072969 + 3 ^ 40 * 2158805 * 2
def baseEnd_2158805 : Nat := 1108504604329531399209343

theorem tailTrace_2158805 : CollatzResearch.WordTrace tailWord_2158805 prefixEnd_2158805 1108504604329531399209343 := by
  unfold tailWord_2158805
  simp only [CollatzResearch.WordTrace]
  refine ⟨78738086944025654385837869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52492057962683769590558579 78738086944025654385837869)
  ·
    refine ⟨29526782604009620394689201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78738086944025654385837869 29526782604009620394689201)
    ·
      refine ⟨22145086953007215296016901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29526782604009620394689201 22145086953007215296016901)
      ·
        refine ⟨4152203803688852868003169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22145086953007215296016901 4152203803688852868003169)
        ·
          refine ⟨3114152852766639651002377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4152203803688852868003169 3114152852766639651002377)
          ·
            refine ⟨2335614639574979738251783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3114152852766639651002377 2335614639574979738251783)
            ·
              refine ⟨3503421959362469607377675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335614639574979738251783 3503421959362469607377675)
              ·
                refine ⟨5255132939043704411066513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503421959362469607377675 5255132939043704411066513)
                ·
                  refine ⟨3941349704282778308299885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5255132939043704411066513 3941349704282778308299885)
                  ·
                    refine ⟨1478006139106041865612457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3941349704282778308299885 1478006139106041865612457)
                    ·
                      refine ⟨1108504604329531399209343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478006139106041865612457 1108504604329531399209343)
                      ·
                        rfl

theorem cell23_2158805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2158805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158805 prefixEnd_2158805 := by exact prefixLift 2158805
  have htrace : WordTrace (prefixWord ++ tailWord_2158805) baseStart_2158805 baseEnd_2158805 := by
    simpa [prefixWord, tailWord_2158805, baseEnd_2158805] using wordTrace_append hprefix tailTrace_2158805
  have hstable : (prefixWord ++ tailWord_2158805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158805).length < 2 ^ (prefixWord ++ tailWord_2158805).sum := by decide
  have hdescent : baseEnd_2158805 < baseStart_2158805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158855 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2158855 : Nat := 118140960795 + 2158855 * 2 ^ 59
def prefixEnd_2158855 : Nat := 4983230072969 + 3 ^ 40 * 2158855 * 2
def baseEnd_2158855 : Nat := 1108530278362256203584113

theorem tailTrace_2158855 : CollatzResearch.WordTrace tailWord_2158855 prefixEnd_2158855 1108530278362256203584113 := by
  unfold tailWord_2158855
  simp only [CollatzResearch.WordTrace]
  refine ⟨78739910593844512925158019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52493273729229675283438679 78739910593844512925158019)
  ·
    refine ⟨118109865890766769387737029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78739910593844512925158019 118109865890766769387737029)
    ·
      refine ⟨22145599854518769260200693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118109865890766769387737029 22145599854518769260200693)
      ·
        refine ⟨2076149986361134618143815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22145599854518769260200693 2076149986361134618143815)
        ·
          refine ⟨3114224979541701927215723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076149986361134618143815 3114224979541701927215723)
          ·
            refine ⟨4671337469312552890823585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114224979541701927215723 4671337469312552890823585)
            ·
              refine ⟨3503503101984414668117689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671337469312552890823585 3503503101984414668117689)
              ·
                refine ⟨2627627326488311001088267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503503101984414668117689 2627627326488311001088267)
                ·
                  refine ⟨3941440989732466501632401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627627326488311001088267 3941440989732466501632401)
                  ·
                    refine ⟨2956080742299349876224301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3941440989732466501632401 2956080742299349876224301)
                    ·
                      refine ⟨1108530278362256203584113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956080742299349876224301 1108530278362256203584113)
                      ·
                        rfl

theorem cell23_2158855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2158855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158855 prefixEnd_2158855 := by exact prefixLift 2158855
  have htrace : WordTrace (prefixWord ++ tailWord_2158855) baseStart_2158855 baseEnd_2158855 := by
    simpa [prefixWord, tailWord_2158855, baseEnd_2158855] using wordTrace_append hprefix tailTrace_2158855
  have hstable : (prefixWord ++ tailWord_2158855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158855).length < 2 ^ (prefixWord ++ tailWord_2158855).sum := by decide
  have hdescent : baseEnd_2158855 < baseStart_2158855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158867 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 8]
def baseStart_2158867 : Nat := 118140960795 + 2158867 * 2 ^ 59
def prefixEnd_2158867 : Nat := 4983230072969 + 3 ^ 40 * 2158867 * 2
def baseEnd_2158867 : Nat := 369512146710036718878019

theorem tailTrace_2158867 : CollatzResearch.WordTrace tailWord_2158867 prefixEnd_2158867 369512146710036718878019 := by
  unfold tailWord_2158867
  simp only [CollatzResearch.WordTrace]
  refine ⟨78740348269801038974594855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52493565513200692649729903 78740348269801038974594855)
  ·
    refine ⟨118110522404701558461892283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78740348269801038974594855 118110522404701558461892283)
    ·
      refine ⟨177165783607052337692838425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118110522404701558461892283 177165783607052337692838425)
      ·
        refine ⟨132874337705289253269628819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177165783607052337692838425 132874337705289253269628819)
        ·
          refine ⟨199311506557933879904443229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132874337705289253269628819 199311506557933879904443229)
          ·
            refine ⟨74741814959225204964166211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199311506557933879904443229 74741814959225204964166211)
            ·
              refine ⟨112112722438837807446249317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74741814959225204964166211 112112722438837807446249317)
              ·
                refine ⟨21021135457282088896171747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112112722438837807446249317 21021135457282088896171747)
                ·
                  refine ⟨31531703185923133344257621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21021135457282088896171747 31531703185923133344257621)
                  ·
                    refine ⟨369512146710036718878019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31531703185923133344257621 369512146710036718878019)
                    ·
                      rfl

theorem cell23_2158867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_2158867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158867 prefixEnd_2158867 := by exact prefixLift 2158867
  have htrace : WordTrace (prefixWord ++ tailWord_2158867) baseStart_2158867 baseEnd_2158867 := by
    simpa [prefixWord, tailWord_2158867, baseEnd_2158867] using wordTrace_append hprefix tailTrace_2158867
  have hstable : (prefixWord ++ tailWord_2158867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158867).length < 2 ^ (prefixWord ++ tailWord_2158867).sum := by decide
  have hdescent : baseEnd_2158867 < baseStart_2158867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158904 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2158904 : Nat := 118140960795 + 2158904 * 2 ^ 59
def prefixEnd_2158904 : Nat := 4983230072969 + 3 ^ 40 * 2158904 * 2
def baseEnd_2158904 : Nat := 1108555438914326511871387

theorem tailTrace_2158904 : CollatzResearch.WordTrace tailWord_2158904 prefixEnd_2158904 1108555438914326511871387 := by
  unfold tailWord_2158904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39370848885333497146845883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52494465180444662862461177 39370848885333497146845883)
  ·
    refine ⟨59056273328000245720268825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39370848885333497146845883 59056273328000245720268825)
    ·
      refine ⟨44292204996000184290201619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59056273328000245720268825 44292204996000184290201619)
      ·
        refine ⟨66438307494000276435302429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44292204996000184290201619 66438307494000276435302429)
        ·
          refine ⟨24914365310250103663238411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66438307494000276435302429 24914365310250103663238411)
          ·
            refine ⟨37371547965375155494857617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24914365310250103663238411 37371547965375155494857617)
            ·
              refine ⟨28028660974031366621143213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37371547965375155494857617 28028660974031366621143213)
              ·
                refine ⟨10510747865261762482928705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28028660974031366621143213 10510747865261762482928705)
                ·
                  refine ⟨7883060898946321862196529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10510747865261762482928705 7883060898946321862196529)
                  ·
                    refine ⟨5912295674209741396647397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7883060898946321862196529 5912295674209741396647397)
                    ·
                      refine ⟨1108555438914326511871387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5912295674209741396647397 1108555438914326511871387)
                      ·
                        rfl

theorem cell23_2158904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2158904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158904 prefixEnd_2158904 := by exact prefixLift 2158904
  have htrace : WordTrace (prefixWord ++ tailWord_2158904) baseStart_2158904 baseEnd_2158904 := by
    simpa [prefixWord, tailWord_2158904, baseEnd_2158904] using wordTrace_append hprefix tailTrace_2158904
  have hstable : (prefixWord ++ tailWord_2158904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158904).length < 2 ^ (prefixWord ++ tailWord_2158904).sum := by decide
  have hdescent : baseEnd_2158904 < baseStart_2158904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158981 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 6, 2]
def baseStart_2158981 : Nat := 118140960795 + 2158981 * 2 ^ 59
def prefixEnd_2158981 : Nat := 4983230072969 + 3 ^ 40 * 2158981 * 2
def baseEnd_2158981 : Nat := 1108594976924722710608533

theorem tailTrace_2158981 : CollatzResearch.WordTrace tailWord_2158981 prefixEnd_2158981 1108594976924722710608533 := by
  unfold tailWord_2158981
  simp only [CollatzResearch.WordTrace]
  refine ⟨78744506191388036444244797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52496337460925357629496531 78744506191388036444244797)
  ·
    refine ⟨29529189821770513666591799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78744506191388036444244797 29529189821770513666591799)
    ·
      refine ⟨44293784732655770499887699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29529189821770513666591799 44293784732655770499887699)
      ·
        refine ⟨66440677098983655749831549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44293784732655770499887699 66440677098983655749831549)
        ·
          refine ⟨24915253912118870906186831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66440677098983655749831549 24915253912118870906186831)
          ·
            refine ⟨37372880868178306359280247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24915253912118870906186831 37372880868178306359280247)
            ·
              refine ⟨56059321302267459538920371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37372880868178306359280247 56059321302267459538920371)
              ·
                refine ⟨84088981953401189308380557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56059321302267459538920371 84088981953401189308380557)
                ·
                  refine ⟨31533368232525445990642709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84088981953401189308380557 31533368232525445990642709)
                  ·
                    refine ⟨1478126635899630280811377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31533368232525445990642709 1478126635899630280811377)
                    ·
                      refine ⟨1108594976924722710608533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478126635899630280811377 1108594976924722710608533)
                      ·
                        rfl

theorem cell23_2158981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_2158981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158981 prefixEnd_2158981 := by exact prefixLift 2158981
  have htrace : WordTrace (prefixWord ++ tailWord_2158981) baseStart_2158981 baseEnd_2158981 := by
    simpa [prefixWord, tailWord_2158981, baseEnd_2158981] using wordTrace_append hprefix tailTrace_2158981
  have hstable : (prefixWord ++ tailWord_2158981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158981).length < 2 ^ (prefixWord ++ tailWord_2158981).sum := by decide
  have hdescent : baseEnd_2158981 < baseStart_2158981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159001 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_2159001 : Nat := 118140960795 + 2159001 * 2 ^ 59
def prefixEnd_2159001 : Nat := 4983230072969 + 3 ^ 40 * 2159001 * 2
def baseEnd_2159001 : Nat := 1108605246537812632358441

theorem tailTrace_2159001 : CollatzResearch.WordTrace tailWord_2159001 prefixEnd_2159001 1108605246537812632358441 := by
  unfold tailWord_2159001
  simp only [CollatzResearch.WordTrace]
  refine ⟨78745235651315579859972857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52496823767543719906648571 78745235651315579859972857)
  ·
    refine ⟨59058926738486684894979643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78745235651315579859972857 59058926738486684894979643)
    ·
      refine ⟨88588390107730027342469465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59058926738486684894979643 88588390107730027342469465)
      ·
        refine ⟨66441292580797520506852099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88588390107730027342469465 66441292580797520506852099)
        ·
          refine ⟨99661938871196280760278149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66441292580797520506852099 99661938871196280760278149)
          ·
            refine ⟨18686613538349302642552153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99661938871196280760278149 18686613538349302642552153)
            ·
              refine ⟨14014960153761976981914115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18686613538349302642552153 14014960153761976981914115)
              ·
                refine ⟨21022440230642965472871173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14014960153761976981914115 21022440230642965472871173)
                ·
                  refine ⟨3941707543245556026163345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21022440230642965472871173 3941707543245556026163345)
                  ·
                    refine ⟨2956280657434167019622509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3941707543245556026163345 2956280657434167019622509)
                    ·
                      refine ⟨1108605246537812632358441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956280657434167019622509 1108605246537812632358441)
                      ·
                        rfl

theorem cell23_2159001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_2159001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159001 prefixEnd_2159001 := by exact prefixLift 2159001
  have htrace : WordTrace (prefixWord ++ tailWord_2159001) baseStart_2159001 baseEnd_2159001 := by
    simpa [prefixWord, tailWord_2159001, baseEnd_2159001] using wordTrace_append hprefix tailTrace_2159001
  have hstable : (prefixWord ++ tailWord_2159001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159001).length < 2 ^ (prefixWord ++ tailWord_2159001).sum := by decide
  have hdescent : baseEnd_2159001 < baseStart_2159001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159008 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 3, 4]
def baseStart_2159008 : Nat := 118140960795 + 2159008 * 2 ^ 59
def prefixEnd_2159008 : Nat := 4983230072969 + 3 ^ 40 * 2159008 * 2
def baseEnd_2159008 : Nat := 369536280300798034990303

theorem tailTrace_2159008 : CollatzResearch.WordTrace tailWord_2159008 prefixEnd_2159008 369536280300798034990303 := by
  unfold tailWord_2159008
  simp only [CollatzResearch.WordTrace]
  refine ⟨39372745481145110027738839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52496993974860146703651785 39372745481145110027738839)
  ·
    refine ⟨59059118221717665041608259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39372745481145110027738839 59059118221717665041608259)
    ·
      refine ⟨88588677332576497562412389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59059118221717665041608259 88588677332576497562412389)
      ·
        refine ⟨16610376999858093292952323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88588677332576497562412389 16610376999858093292952323)
        ·
          refine ⟨24915565499787139939428485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16610376999858093292952323 24915565499787139939428485)
          ·
            refine ⟨4671668531210088738642841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24915565499787139939428485 4671668531210088738642841)
            ·
              refine ⟨3503751398407566553982131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671668531210088738642841 3503751398407566553982131)
              ·
                refine ⟨5255627097611349830973197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503751398407566553982131 5255627097611349830973197)
                ·
                  refine ⟨1970860161604256186614949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5255627097611349830973197 1970860161604256186614949)
                  ·
                    refine ⟨369536280300798034990303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970860161604256186614949 369536280300798034990303)
                    ·
                      rfl

theorem cell23_2159008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_2159008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159008 prefixEnd_2159008 := by exact prefixLift 2159008
  have htrace : WordTrace (prefixWord ++ tailWord_2159008) baseStart_2159008 baseEnd_2159008 := by
    simpa [prefixWord, tailWord_2159008, baseEnd_2159008] using wordTrace_append hprefix tailTrace_2159008
  have hstable : (prefixWord ++ tailWord_2159008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159008).length < 2 ^ (prefixWord ++ tailWord_2159008).sum := by decide
  have hdescent : baseEnd_2159008 < baseStart_2159008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159034 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_2159034 : Nat := 118140960795 + 2159034 * 2 ^ 59
def prefixEnd_2159034 : Nat := 4983230072969 + 3 ^ 40 * 2159034 * 2
def baseEnd_2159034 : Nat := 369540730466470334415263

theorem tailTrace_2159034 : CollatzResearch.WordTrace tailWord_2159034 prefixEnd_2159034 369540730466470334415263 := by
  unfold tailWord_2159034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19686609815049006623981039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52497626173464017663949437 19686609815049006623981039)
  ·
    refine ⟨29529914722573509935971559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19686609815049006623981039 29529914722573509935971559)
    ·
      refine ⟨44294872083860264903957339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29529914722573509935971559 44294872083860264903957339)
      ·
        refine ⟨66442308125790397355936009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44294872083860264903957339 66442308125790397355936009)
        ·
          refine ⟨49831731094342798016952007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66442308125790397355936009 49831731094342798016952007)
          ·
            refine ⟨74747596641514197025428011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49831731094342798016952007 74747596641514197025428011)
            ·
              refine ⟨112121394962271295538142017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74747596641514197025428011 112121394962271295538142017)
              ·
                refine ⟨84091046221703471653606513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112121394962271295538142017 84091046221703471653606513)
                ·
                  refine ⟨63068284666277603740204885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84091046221703471653606513 63068284666277603740204885)
                  ·
                    refine ⟨369540730466470334415263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63068284666277603740204885 369540730466470334415263)
                    ·
                      rfl

theorem cell23_2159034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_2159034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159034 prefixEnd_2159034 := by exact prefixLift 2159034
  have htrace : WordTrace (prefixWord ++ tailWord_2159034) baseStart_2159034 baseEnd_2159034 := by
    simpa [prefixWord, tailWord_2159034, baseEnd_2159034] using wordTrace_append hprefix tailTrace_2159034
  have hstable : (prefixWord ++ tailWord_2159034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159034).length < 2 ^ (prefixWord ++ tailWord_2159034).sum := by decide
  have hdescent : baseEnd_2159034 < baseStart_2159034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159081 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 6, 4]
def baseStart_2159081 : Nat := 118140960795 + 2159081 * 2 ^ 59
def prefixEnd_2159081 : Nat := 4983230072969 + 3 ^ 40 * 2159081 * 2
def baseEnd_2159081 : Nat := 369548774996724106452691

theorem tailTrace_2159081 : CollatzResearch.WordTrace tailWord_2159081 prefixEnd_2159081 369548774996724106452691 := by
  unfold tailWord_2159081
  simp only [CollatzResearch.WordTrace]
  refine ⟨78748153491025753522885097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52498768994017169015256731 78748153491025753522885097)
  ·
    refine ⟨59061115118269315142163823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78748153491025753522885097 59061115118269315142163823)
    ·
      refine ⟨88591672677403972713245735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59061115118269315142163823 88591672677403972713245735)
      ·
        refine ⟨132887509016105959069868603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88591672677403972713245735 132887509016105959069868603)
        ·
          refine ⟨199331263524158938604802905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132887509016105959069868603 199331263524158938604802905)
          ·
            refine ⟨149498447643119203953602179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199331263524158938604802905 149498447643119203953602179)
            ·
              refine ⟨224247671464678805930403269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149498447643119203953602179 224247671464678805930403269)
              ·
                refine ⟨42046438399627276111950613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224247671464678805930403269 42046438399627276111950613)
                ·
                  refine ⟨1970926799982528567747685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42046438399627276111950613 1970926799982528567747685)
                  ·
                    refine ⟨369548774996724106452691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970926799982528567747685 369548774996724106452691)
                    ·
                      rfl

theorem cell23_2159081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 4].length) (baseStart_2159081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159081 prefixEnd_2159081 := by exact prefixLift 2159081
  have htrace : WordTrace (prefixWord ++ tailWord_2159081) baseStart_2159081 baseEnd_2159081 := by
    simpa [prefixWord, tailWord_2159081, baseEnd_2159081] using wordTrace_append hprefix tailTrace_2159081
  have hstable : (prefixWord ++ tailWord_2159081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159081).length < 2 ^ (prefixWord ++ tailWord_2159081).sum := by decide
  have hdescent : baseEnd_2159081 < baseStart_2159081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159085 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2159085 : Nat := 118140960795 + 2159085 * 2 ^ 59
def prefixEnd_2159085 : Nat := 4983230072969 + 3 ^ 40 * 2159085 * 2
def baseEnd_2159085 : Nat := 369549459637596767902685

theorem tailTrace_2159085 : CollatzResearch.WordTrace tailWord_2159085 prefixEnd_2159085 369549459637596767902685 := by
  unfold tailWord_2159085
  simp only [CollatzResearch.WordTrace]
  refine ⟨78748299383011262206030709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52498866255340841470687139 78748299383011262206030709)
  ·
    refine ⟨7382653067157305831815379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78748299383011262206030709 7382653067157305831815379)
    ·
      refine ⟨11073979600735958747723069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7382653067157305831815379 11073979600735958747723069)
      ·
        refine ⟨4152742350275984530396151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11073979600735958747723069 4152742350275984530396151)
        ·
          refine ⟨6229113525413976795594227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152742350275984530396151 6229113525413976795594227)
          ·
            refine ⟨9343670288120965193391341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229113525413976795594227 9343670288120965193391341)
            ·
              refine ⟨3503876358045361947521753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9343670288120965193391341 3503876358045361947521753)
              ·
                refine ⟨2627907268534021460641315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503876358045361947521753 2627907268534021460641315)
                ·
                  refine ⟨3941860902801032190961973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627907268534021460641315 3941860902801032190961973)
                  ·
                    refine ⟨369549459637596767902685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3941860902801032190961973 369549459637596767902685)
                    ·
                      rfl

theorem cell23_2159085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2159085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159085 prefixEnd_2159085 := by exact prefixLift 2159085
  have htrace : WordTrace (prefixWord ++ tailWord_2159085) baseStart_2159085 baseEnd_2159085 := by
    simpa [prefixWord, tailWord_2159085, baseEnd_2159085] using wordTrace_append hprefix tailTrace_2159085
  have hstable : (prefixWord ++ tailWord_2159085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159085).length < 2 ^ (prefixWord ++ tailWord_2159085).sum := by decide
  have hdescent : baseEnd_2159085 < baseStart_2159085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159111 : List Nat := [1, 1, 4, 3, 3, 11]
def baseStart_2159111 : Nat := 118140960795 + 2159111 * 2 ^ 59
def prefixEnd_2159111 : Nat := 4983230072969 + 3 ^ 40 * 2159111 * 2
def baseEnd_2159111 : Nat := 4562393948188507004045

theorem tailTrace_2159111 : CollatzResearch.WordTrace tailWord_2159111 prefixEnd_2159111 4562393948188507004045 := by
  unfold tailWord_2159111
  simp only [CollatzResearch.WordTrace]
  refine ⟨78749247680917068646477187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52499498453944712430984791 78749247680917068646477187)
  ·
    refine ⟨118123871521375602969715781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78749247680917068646477187 118123871521375602969715781)
    ·
      refine ⟨22148225910257925556821709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118123871521375602969715781 22148225910257925556821709)
      ·
        refine ⟨8305584716346722083808141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22148225910257925556821709 8305584716346722083808141)
        ·
          refine ⟨3114594268630020781428053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8305584716346722083808141 3114594268630020781428053)
          ·
            refine ⟨4562393948188507004045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3114594268630020781428053 4562393948188507004045)
            ·
              rfl

theorem cell23_2159111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 11].length) (baseStart_2159111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159111 prefixEnd_2159111 := by exact prefixLift 2159111
  have htrace : WordTrace (prefixWord ++ tailWord_2159111) baseStart_2159111 baseEnd_2159111 := by
    simpa [prefixWord, tailWord_2159111, baseEnd_2159111] using wordTrace_append hprefix tailTrace_2159111
  have hstable : (prefixWord ++ tailWord_2159111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159111).length < 2 ^ (prefixWord ++ tailWord_2159111).sum := by decide
  have hdescent : baseEnd_2159111 < baseStart_2159111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159115 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 2, 4]
def baseStart_2159115 : Nat := 118140960795 + 2159115 * 2 ^ 59
def prefixEnd_2159115 : Nat := 4983230072969 + 3 ^ 40 * 2159115 * 2
def baseEnd_2159115 : Nat := 369554594444141728777639

theorem tailTrace_2159115 : CollatzResearch.WordTrace tailWord_2159115 prefixEnd_2159115 369554594444141728777639 := by
  unfold tailWord_2159115
  simp only [CollatzResearch.WordTrace]
  refine ⟨78749393572902577329622799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52499595715268384886415199 78749393572902577329622799)
  ·
    refine ⟨118124090359353865994434199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78749393572902577329622799 118124090359353865994434199)
    ·
      refine ⟨177186135539030798991651299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118124090359353865994434199 177186135539030798991651299)
      ·
        refine ⟨265779203308546198487476949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177186135539030798991651299 265779203308546198487476949)
        ·
          refine ⟨6229200077544051527050241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 265779203308546198487476949 6229200077544051527050241)
          ·
            refine ⟨4671900058158038645287681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6229200077544051527050241 4671900058158038645287681)
            ·
              refine ⟨3503925043618528983965761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671900058158038645287681 3503925043618528983965761)
              ·
                refine ⟨2627943782713896737974321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503925043618528983965761 2627943782713896737974321)
                ·
                  refine ⟨1970957837035422553480741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2627943782713896737974321 1970957837035422553480741)
                  ·
                    refine ⟨369554594444141728777639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970957837035422553480741 369554594444141728777639)
                    ·
                      rfl

theorem cell23_2159115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 4].length) (baseStart_2159115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159115 prefixEnd_2159115 := by exact prefixLift 2159115
  have htrace : WordTrace (prefixWord ++ tailWord_2159115) baseStart_2159115 baseEnd_2159115 := by
    simpa [prefixWord, tailWord_2159115, baseEnd_2159115] using wordTrace_append hprefix tailTrace_2159115
  have hstable : (prefixWord ++ tailWord_2159115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159115).length < 2 ^ (prefixWord ++ tailWord_2159115).sum := by decide
  have hdescent : baseEnd_2159115 < baseStart_2159115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159128 : List Nat := [2, 1, 2, 3, 3, 3, 1, 8]
def baseStart_2159128 : Nat := 118140960795 + 2159128 * 2 ^ 59
def prefixEnd_2159128 : Nat := 4983230072969 + 3 ^ 40 * 2159128 * 2
def baseEnd_2159128 : Nat := 41061868836330875387791

theorem tailTrace_2159128 : CollatzResearch.WordTrace tailWord_2159128 prefixEnd_2159128 41061868836330875387791 := by
  unfold tailWord_2159128
  simp only [CollatzResearch.WordTrace]
  refine ⟨39374933860927740274923019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52499911814570320366564025 39374933860927740274923019)
  ·
    refine ⟨59062400791391610412384529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39374933860927740274923019 59062400791391610412384529)
    ·
      refine ⟨44296800593543707809288397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59062400791391610412384529 44296800593543707809288397)
      ·
        refine ⟨16611300222578890428483149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44296800593543707809288397 16611300222578890428483149)
        ·
          refine ⟨6229237583467083910681181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16611300222578890428483149 6229237583467083910681181)
          ·
            refine ⟨2335964093800156466505443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6229237583467083910681181 2335964093800156466505443)
            ·
              refine ⟨3503946140700234699758165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335964093800156466505443 3503946140700234699758165)
              ·
                refine ⟨41061868836330875387791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3503946140700234699758165 41061868836330875387791)
                ·
                  rfl

theorem cell23_2159128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 8].length) (baseStart_2159128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159128 prefixEnd_2159128 := by exact prefixLift 2159128
  have htrace : WordTrace (prefixWord ++ tailWord_2159128) baseStart_2159128 baseEnd_2159128 := by
    simpa [prefixWord, tailWord_2159128, baseEnd_2159128] using wordTrace_append hprefix tailTrace_2159128
  have hstable : (prefixWord ++ tailWord_2159128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159128).length < 2 ^ (prefixWord ++ tailWord_2159128).sum := by decide
  have hdescent : baseEnd_2159128 < baseStart_2159128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159156 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2159156 : Nat := 118140960795 + 2159156 * 2 ^ 59
def prefixEnd_2159156 : Nat := 4983230072969 + 3 ^ 40 * 2159156 * 2
def baseEnd_2159156 : Nat := 1108684836039259525920229

theorem tailTrace_2159156 : CollatzResearch.WordTrace tailWord_2159156 prefixEnd_2159156 1108684836039259525920229 := by
  unfold tailWord_2159156
  simp only [CollatzResearch.WordTrace]
  refine ⟨39375444482877020665932661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52500592643836027554576881 39375444482877020665932661)
  ·
    refine ⟨3691447920269720687431187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39375444482877020665932661 3691447920269720687431187)
    ·
      refine ⟨5537171880404581031146781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691447920269720687431187 5537171880404581031146781)
      ·
        refine ⟨2076439455151717886680043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5537171880404581031146781 2076439455151717886680043)
        ·
          refine ⟨3114659182727576830020065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076439455151717886680043 3114659182727576830020065)
          ·
            refine ⟨2335994387045682622515049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3114659182727576830020065 2335994387045682622515049)
            ·
              refine ⟨1751995790284261966886287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335994387045682622515049 1751995790284261966886287)
              ·
                refine ⟨2627993685426392950329431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751995790284261966886287 2627993685426392950329431)
                ·
                  refine ⟨3941990528139589425494147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627993685426392950329431 3941990528139589425494147)
                  ·
                    refine ⟨5912985792209384138241221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3941990528139589425494147 5912985792209384138241221)
                    ·
                      refine ⟨1108684836039259525920229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5912985792209384138241221 1108684836039259525920229)
                      ·
                        rfl

theorem cell23_2159156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2159156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159156 prefixEnd_2159156 := by exact prefixLift 2159156
  have htrace : WordTrace (prefixWord ++ tailWord_2159156) baseStart_2159156 baseEnd_2159156 := by
    simpa [prefixWord, tailWord_2159156, baseEnd_2159156] using wordTrace_append hprefix tailTrace_2159156
  have hstable : (prefixWord ++ tailWord_2159156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159156).length < 2 ^ (prefixWord ++ tailWord_2159156).sum := by decide
  have hdescent : baseEnd_2159156 < baseStart_2159156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159166 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2159166 : Nat := 118140960795 + 2159166 * 2 ^ 59
def prefixEnd_2159166 : Nat := 4983230072969 + 3 ^ 40 * 2159166 * 2
def baseEnd_2159166 : Nat := 369563323615268162265061

theorem tailTrace_2159166 : CollatzResearch.WordTrace tailWord_2159166 prefixEnd_2159166 369563323615268162265061 := by
  unfold tailWord_2159166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843906711964726629966169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52500835797145208693152901 9843906711964726629966169)
  ·
    refine ⟨7382930033973544972474627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9843906711964726629966169 7382930033973544972474627)
    ·
      refine ⟨11074395050960317458711941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7382930033973544972474627 11074395050960317458711941)
      ·
        refine ⟨2076449072055059523508489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11074395050960317458711941 2076449072055059523508489)
        ·
          refine ⟨1557336804041294642631367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076449072055059523508489 1557336804041294642631367)
          ·
            refine ⟨2336005206061941963947051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557336804041294642631367 2336005206061941963947051)
            ·
              refine ⟨3504007809092912945920577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336005206061941963947051 3504007809092912945920577)
              ·
                refine ⟨2628005856819684709440433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504007809092912945920577 2628005856819684709440433)
                ·
                  refine ⟨1971004392614763532080325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628005856819684709440433 1971004392614763532080325)
                  ·
                    refine ⟨369563323615268162265061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971004392614763532080325 369563323615268162265061)
                    ·
                      rfl

theorem cell23_2159166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2159166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159166 prefixEnd_2159166 := by exact prefixLift 2159166
  have htrace : WordTrace (prefixWord ++ tailWord_2159166) baseStart_2159166 baseEnd_2159166 := by
    simpa [prefixWord, tailWord_2159166, baseEnd_2159166] using wordTrace_append hprefix tailTrace_2159166
  have hstable : (prefixWord ++ tailWord_2159166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159166).length < 2 ^ (prefixWord ++ tailWord_2159166).sum := by decide
  have hdescent : baseEnd_2159166 < baseStart_2159166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159188 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_2159188 : Nat := 118140960795 + 2159188 * 2 ^ 59
def prefixEnd_2159188 : Nat := 4983230072969 + 3 ^ 40 * 2159188 * 2
def baseEnd_2159188 : Nat := 369567089140067800240027

theorem tailTrace_2159188 : CollatzResearch.WordTrace tailWord_2159188 prefixEnd_2159188 369567089140067800240027 := by
  unfold tailWord_2159188
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376028050819055398515109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52501370734425407198020145 39376028050819055398515109)
  ·
    refine ⟨7383005259528572887221583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39376028050819055398515109 7383005259528572887221583)
    ·
      refine ⟨11074507889292859330832375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7383005259528572887221583 11074507889292859330832375)
      ·
        refine ⟨16611761833939288996248563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11074507889292859330832375 16611761833939288996248563)
        ·
          refine ⟨24917642750908933494372845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16611761833939288996248563 24917642750908933494372845)
          ·
            refine ⟨9344116031590850060389817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24917642750908933494372845 9344116031590850060389817)
            ·
              refine ⟨7008087023693137545292363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9344116031590850060389817 7008087023693137545292363)
              ·
                refine ⟨10512130535539706317938545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008087023693137545292363 10512130535539706317938545)
                ·
                  refine ⟨7884097901654779738453909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10512130535539706317938545 7884097901654779738453909)
                  ·
                    refine ⟨369567089140067800240027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7884097901654779738453909 369567089140067800240027)
                    ·
                      rfl

theorem cell23_2159188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_2159188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159188 prefixEnd_2159188 := by exact prefixLift 2159188
  have htrace : WordTrace (prefixWord ++ tailWord_2159188) baseStart_2159188 baseEnd_2159188 := by
    simpa [prefixWord, tailWord_2159188, baseEnd_2159188] using wordTrace_append hprefix tailTrace_2159188
  have hstable : (prefixWord ++ tailWord_2159188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159188).length < 2 ^ (prefixWord ++ tailWord_2159188).sum := by decide
  have hdescent : baseEnd_2159188 < baseStart_2159188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159228 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_2159228 : Nat := 118140960795 + 2159228 * 2 ^ 59
def prefixEnd_2159228 : Nat := 4983230072969 + 3 ^ 40 * 2159228 * 2
def baseEnd_2159228 : Nat := 1108721806646383244219897

theorem tailTrace_2159228 : CollatzResearch.WordTrace tailWord_2159228 prefixEnd_2159228 1108721806646383244219897 := by
  unfold tailWord_2159228
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376757510746598814243169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52502343347662131752324225 39376757510746598814243169)
  ·
    refine ⟨29532568133059949110682377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39376757510746598814243169 29532568133059949110682377)
    ·
      refine ⟨22149426099794961833011783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29532568133059949110682377 22149426099794961833011783)
      ·
        refine ⟨33224139149692442749517675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22149426099794961833011783 33224139149692442749517675)
        ·
          refine ⟨49836208724538664124276513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33224139149692442749517675 49836208724538664124276513)
          ·
            refine ⟨37377156543403998093207385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49836208724538664124276513 37377156543403998093207385)
            ·
              refine ⟨28032867407552998569905539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37377156543403998093207385 28032867407552998569905539)
              ·
                refine ⟨42049301111329497854858309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28032867407552998569905539 42049301111329497854858309)
                ·
                  refine ⟨7884243958374280847785933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42049301111329497854858309 7884243958374280847785933)
                  ·
                    refine ⟨2956591484390355317919725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7884243958374280847785933 2956591484390355317919725)
                    ·
                      refine ⟨1108721806646383244219897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956591484390355317919725 1108721806646383244219897)
                      ·
                        rfl

theorem cell23_2159228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_2159228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159228 prefixEnd_2159228 := by exact prefixLift 2159228
  have htrace : WordTrace (prefixWord ++ tailWord_2159228) baseStart_2159228 baseEnd_2159228 := by
    simpa [prefixWord, tailWord_2159228, baseEnd_2159228] using wordTrace_append hprefix tailTrace_2159228
  have hstable : (prefixWord ++ tailWord_2159228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159228).length < 2 ^ (prefixWord ++ tailWord_2159228).sum := by decide
  have hdescent : baseEnd_2159228 < baseStart_2159228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159231 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 3, 7]
def baseStart_2159231 : Nat := 118140960795 + 2159231 * 2 ^ 59
def prefixEnd_2159231 : Nat := 4983230072969 + 3 ^ 40 * 2159231 * 2
def baseEnd_2159231 : Nat := 369574449029448910827461

theorem tailTrace_2159231 : CollatzResearch.WordTrace tailWord_2159231 prefixEnd_2159231 369574449029448910827461 := by
  unfold tailWord_2159231
  simp only [CollatzResearch.WordTrace]
  refine ⟨78753624440482329140845547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52502416293654886093897031 78753624440482329140845547)
  ·
    refine ⟨118130436660723493711268321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78753624440482329140845547 118130436660723493711268321)
    ·
      refine ⟨88597827495542620283451241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118130436660723493711268321 88597827495542620283451241)
      ·
        refine ⟨66448370621656965212588431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88597827495542620283451241 66448370621656965212588431)
        ·
          refine ⟨99672555932485447818882647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66448370621656965212588431 99672555932485447818882647)
          ·
            refine ⟨149508833898728171728323971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99672555932485447818882647 149508833898728171728323971)
            ·
              refine ⟨224263250848092257592485957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149508833898728171728323971 224263250848092257592485957)
              ·
                refine ⟨42049359534017298298591117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224263250848092257592485957 42049359534017298298591117)
                ·
                  refine ⟨15768509825256486861971669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42049359534017298298591117 15768509825256486861971669)
                  ·
                    refine ⟨369574449029448910827461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15768509825256486861971669 369574449029448910827461)
                    ·
                      rfl

theorem cell23_2159231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_2159231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159231 prefixEnd_2159231 := by exact prefixLift 2159231
  have htrace : WordTrace (prefixWord ++ tailWord_2159231) baseStart_2159231 baseEnd_2159231 := by
    simpa [prefixWord, tailWord_2159231, baseEnd_2159231] using wordTrace_append hprefix tailTrace_2159231
  have hstable : (prefixWord ++ tailWord_2159231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159231).length < 2 ^ (prefixWord ++ tailWord_2159231).sum := by decide
  have hdescent : baseEnd_2159231 < baseStart_2159231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159288 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_2159288 : Nat := 118140960795 + 2159288 * 2 ^ 59
def prefixEnd_2159288 : Nat := 4983230072969 + 3 ^ 40 * 2159288 * 2
def baseEnd_2159288 : Nat := 1108752615485653009469621

theorem tailTrace_2159288 : CollatzResearch.WordTrace tailWord_2159288 prefixEnd_2159288 1108752615485653009469621 := by
  unfold tailWord_2159288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39377851700637913937835259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52503802267517218583780345 39377851700637913937835259)
  ·
    refine ⟨59066777550956870906752889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39377851700637913937835259 59066777550956870906752889)
    ·
      refine ⟨44300083163217653180064667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59066777550956870906752889 44300083163217653180064667)
      ·
        refine ⟨66450124744826479770097001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44300083163217653180064667 66450124744826479770097001)
        ·
          refine ⟨49837593558619859827572751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66450124744826479770097001 49837593558619859827572751)
          ·
            refine ⟨74756390337929789741359127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49837593558619859827572751 74756390337929789741359127)
            ·
              refine ⟨112134585506894684612038691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74756390337929789741359127 112134585506894684612038691)
              ·
                refine ⟨168201878260342026918058037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112134585506894684612038691 168201878260342026918058037)
                ·
                  refine ⟨15768926086907065023567941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168201878260342026918058037 15768926086907065023567941)
                  ·
                    refine ⟨2956673641295074691918989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15768926086907065023567941 2956673641295074691918989)
                    ·
                      refine ⟨1108752615485653009469621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956673641295074691918989 1108752615485653009469621)
                      ·
                        rfl

theorem cell23_2159288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_2159288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159288 prefixEnd_2159288 := by exact prefixLift 2159288
  have htrace : WordTrace (prefixWord ++ tailWord_2159288) baseStart_2159288 baseEnd_2159288 := by
    simpa [prefixWord, tailWord_2159288, baseEnd_2159288] using wordTrace_append hprefix tailTrace_2159288
  have hstable : (prefixWord ++ tailWord_2159288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159288).length < 2 ^ (prefixWord ++ tailWord_2159288).sum := by decide
  have hdescent : baseEnd_2159288 < baseStart_2159288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159329 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 1, 4]
def baseStart_2159329 : Nat := 118140960795 + 2159329 * 2 ^ 59
def prefixEnd_2159329 : Nat := 4983230072969 + 3 ^ 40 * 2159329 * 2
def baseEnd_2159329 : Nat := 369591222730829116352311

theorem tailTrace_2159329 : CollatzResearch.WordTrace tailWord_2159329 prefixEnd_2159329 369591222730829116352311 := by
  unfold tailWord_2159329
  simp only [CollatzResearch.WordTrace]
  refine ⟨78757198794127291877913041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52504799196084861251942027 78757198794127291877913041)
  ·
    refine ⟨59067899095595468908434781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78757198794127291877913041 59067899095595468908434781)
    ·
      refine ⟨22150462160848300840663043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59067899095595468908434781 22150462160848300840663043)
      ·
        refine ⟨33225693241272451260994565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22150462160848300840663043 33225693241272451260994565)
        ·
          refine ⟨6229817482738584611436481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33225693241272451260994565 6229817482738584611436481)
          ·
            refine ⟨4672363112053938458577361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6229817482738584611436481 4672363112053938458577361)
            ·
              refine ⟨3504272334040453843933021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4672363112053938458577361 3504272334040453843933021)
              ·
                refine ⟨1314102125265170191474883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3504272334040453843933021 1314102125265170191474883)
                ·
                  refine ⟨1971153187897755287212325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314102125265170191474883 1971153187897755287212325)
                  ·
                    refine ⟨369591222730829116352311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971153187897755287212325 369591222730829116352311)
                    ·
                      rfl

theorem cell23_2159329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_2159329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159329 prefixEnd_2159329 := by exact prefixLift 2159329
  have htrace : WordTrace (prefixWord ++ tailWord_2159329) baseStart_2159329 baseEnd_2159329 := by
    simpa [prefixWord, tailWord_2159329, baseEnd_2159329] using wordTrace_append hprefix tailTrace_2159329
  have hstable : (prefixWord ++ tailWord_2159329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159329).length < 2 ^ (prefixWord ++ tailWord_2159329).sum := by decide
  have hdescent : baseEnd_2159329 < baseStart_2159329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159342 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_2159342 : Nat := 118140960795 + 2159342 * 2 ^ 59
def prefixEnd_2159342 : Nat := 4983230072969 + 3 ^ 40 * 2159342 * 2
def baseEnd_2159342 : Nat := 123197815937888422021597

theorem tailTrace_2159342 : CollatzResearch.WordTrace tailWord_2159342 prefixEnd_2159342 123197815937888422021597 := by
  unfold tailWord_2159342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9844709117885024387267035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52505115295386796732090853 9844709117885024387267035)
  ·
    refine ⟨14767063676827536580900553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9844709117885024387267035 14767063676827536580900553)
    ·
      refine ⟨11075297757620652435675415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14767063676827536580900553 11075297757620652435675415)
      ·
        refine ⟨16612946636430978653513123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11075297757620652435675415 16612946636430978653513123)
        ·
          refine ⟨24919419954646467980269685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16612946636430978653513123 24919419954646467980269685)
          ·
            refine ⟨2336195620748106373150283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24919419954646467980269685 2336195620748106373150283)
            ·
              refine ⟨3504293431122159559725425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336195620748106373150283 3504293431122159559725425)
              ·
                refine ⟨2628220073341619669794069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504293431122159559725425 2628220073341619669794069)
                ·
                  refine ⟨123197815937888422021597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2628220073341619669794069 123197815937888422021597)
                  ·
                    rfl

theorem cell23_2159342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_2159342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159342 prefixEnd_2159342 := by exact prefixLift 2159342
  have htrace : WordTrace (prefixWord ++ tailWord_2159342) baseStart_2159342 baseEnd_2159342 := by
    simpa [prefixWord, tailWord_2159342, baseEnd_2159342] using wordTrace_append hprefix tailTrace_2159342
  have hstable : (prefixWord ++ tailWord_2159342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159342).length < 2 ^ (prefixWord ++ tailWord_2159342).sum := by decide
  have hdescent : baseEnd_2159342 < baseStart_2159342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159352 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_2159352 : Nat := 118140960795 + 2159352 * 2 ^ 59
def prefixEnd_2159352 : Nat := 4983230072969 + 3 ^ 40 * 2159352 * 2
def baseEnd_2159352 : Nat := 1108785478247540759069327

theorem tailTrace_2159352 : CollatzResearch.WordTrace tailWord_2159352 prefixEnd_2159352 1108785478247540759069327 := by
  unfold tailWord_2159352
  simp only [CollatzResearch.WordTrace]
  refine ⟨39379018836521983403000155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52505358448695977870666873 39379018836521983403000155)
  ·
    refine ⟨59068528254782975104500233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39379018836521983403000155 59068528254782975104500233)
    ·
      refine ⟨44301396191087231328375175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59068528254782975104500233 44301396191087231328375175)
      ·
        refine ⟨66452094286630846992562763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44301396191087231328375175 66452094286630846992562763)
        ·
          refine ⟨99678141429946270488844145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66452094286630846992562763 99678141429946270488844145)
          ·
            refine ⟨74758606072459702866633109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99678141429946270488844145 74758606072459702866633109)
            ·
              refine ⟨3504309659646548571873427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74758606072459702866633109 3504309659646548571873427)
              ·
                refine ⟨5256464489469822857810141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504309659646548571873427 5256464489469822857810141)
                ·
                  refine ⟨1971174183551183571678803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5256464489469822857810141 1971174183551183571678803)
                  ·
                    refine ⟨2956761275326775357518205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1971174183551183571678803 2956761275326775357518205)
                    ·
                      refine ⟨1108785478247540759069327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956761275326775357518205 1108785478247540759069327)
                      ·
                        rfl

theorem cell23_2159352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_2159352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159352 prefixEnd_2159352 := by exact prefixLift 2159352
  have htrace : WordTrace (prefixWord ++ tailWord_2159352) baseStart_2159352 baseEnd_2159352 := by
    simpa [prefixWord, tailWord_2159352, baseEnd_2159352] using wordTrace_append hprefix tailTrace_2159352
  have hstable : (prefixWord ++ tailWord_2159352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159352).length < 2 ^ (prefixWord ++ tailWord_2159352).sum := by decide
  have hdescent : baseEnd_2159352 < baseStart_2159352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159375 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 6, 2]
def baseStart_2159375 : Nat := 118140960795 + 2159375 * 2 ^ 59
def prefixEnd_2159375 : Nat := 4983230072969 + 3 ^ 40 * 2159375 * 2
def baseEnd_2159375 : Nat := 1108797288302594169081721

theorem tailTrace_2159375 : CollatzResearch.WordTrace tailWord_2159375 prefixEnd_2159375 1108797288302594169081721 := by
  unfold tailWord_2159375
  simp only [CollatzResearch.WordTrace]
  refine ⟨78758876551960641734087579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52505917701307094489391719 78758876551960641734087579)
  ·
    refine ⟨118138314827940962601131369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78758876551960641734087579 118138314827940962601131369)
    ·
      refine ⟨88603736120955721950848527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118138314827940962601131369 88603736120955721950848527)
      ·
        refine ⟨132905604181433582926272791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88603736120955721950848527 132905604181433582926272791)
        ·
          refine ⟨199358406272150374389409187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132905604181433582926272791 199358406272150374389409187)
          ·
            refine ⟨299037609408225561584113781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199358406272150374389409187 299037609408225561584113781)
            ·
              refine ⟨28034775882021146398510667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 299037609408225561584113781 28034775882021146398510667)
              ·
                refine ⟨42052163823031719597766001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28034775882021146398510667 42052163823031719597766001)
                ·
                  refine ⟨31539122867273789698324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42052163823031719597766001 31539122867273789698324501)
                  ·
                    refine ⟨1478396384403458892108961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31539122867273789698324501 1478396384403458892108961)
                    ·
                      refine ⟨1108797288302594169081721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478396384403458892108961 1108797288302594169081721)
                      ·
                        rfl

theorem cell23_2159375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6, 2].length) (baseStart_2159375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159375 prefixEnd_2159375 := by exact prefixLift 2159375
  have htrace : WordTrace (prefixWord ++ tailWord_2159375) baseStart_2159375 baseEnd_2159375 := by
    simpa [prefixWord, tailWord_2159375, baseEnd_2159375] using wordTrace_append hprefix tailTrace_2159375
  have hstable : (prefixWord ++ tailWord_2159375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159375).length < 2 ^ (prefixWord ++ tailWord_2159375).sum := by decide
  have hdescent : baseEnd_2159375 < baseStart_2159375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159392 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2159392 : Nat := 118140960795 + 2159392 * 2 ^ 59
def prefixEnd_2159392 : Nat := 4983230072969 + 3 ^ 40 * 2159392 * 2
def baseEnd_2159392 : Nat := 1108806017473720602569143

theorem tailTrace_2159392 : CollatzResearch.WordTrace tailWord_2159392 prefixEnd_2159392 1108806017473720602569143 := by
  unfold tailWord_2159392
  simp only [CollatzResearch.WordTrace]
  refine ⟨39379748296449526818728215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52506331061932702424970953 39379748296449526818728215)
  ·
    refine ⟨59069622444674290228092323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39379748296449526818728215 59069622444674290228092323)
    ·
      refine ⟨88604433667011435342138485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59069622444674290228092323 88604433667011435342138485)
      ·
        refine ⟨8306665656282322063325483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88604433667011435342138485 8306665656282322063325483)
        ·
          refine ⟨12459998484423483094988225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8306665656282322063325483 12459998484423483094988225)
          ·
            refine ⟨9344998863317612321241169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12459998484423483094988225 9344998863317612321241169)
            ·
              refine ⟨7008749147488209240930877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9344998863317612321241169 7008749147488209240930877)
              ·
                refine ⟨2628280930308078465349079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7008749147488209240930877 2628280930308078465349079)
                ·
                  refine ⟨3942421395462117698023619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628280930308078465349079 3942421395462117698023619)
                  ·
                    refine ⟨5913632093193176547035429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942421395462117698023619 5913632093193176547035429)
                    ·
                      refine ⟨1108806017473720602569143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5913632093193176547035429 1108806017473720602569143)
                      ·
                        rfl

theorem cell23_2159392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2159392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159392 prefixEnd_2159392 := by exact prefixLift 2159392
  have htrace : WordTrace (prefixWord ++ tailWord_2159392) baseStart_2159392 baseEnd_2159392 := by
    simpa [prefixWord, tailWord_2159392, baseEnd_2159392] using wordTrace_append hprefix tailTrace_2159392
  have hstable : (prefixWord ++ tailWord_2159392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159392).length < 2 ^ (prefixWord ++ tailWord_2159392).sum := by decide
  have hdescent : baseEnd_2159392 < baseStart_2159392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159395 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 3]
def baseStart_2159395 : Nat := 118140960795 + 2159395 * 2 ^ 59
def prefixEnd_2159395 : Nat := 4983230072969 + 3 ^ 40 * 2159395 * 2
def baseEnd_2159395 : Nat := 1108807557915684090831629

theorem tailTrace_2159395 : CollatzResearch.WordTrace tailWord_2159395 prefixEnd_2159395 1108807557915684090831629 := by
  unfold tailWord_2159395
  simp only [CollatzResearch.WordTrace]
  refine ⟨78759606011888185149815639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52506404007925456766543759 78759606011888185149815639)
  ·
    refine ⟨118139409017832277724723459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78759606011888185149815639 118139409017832277724723459)
    ·
      refine ⟨177209113526748416587085189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118139409017832277724723459 177209113526748416587085189)
      ·
        refine ⟨33226708786265328110078473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177209113526748416587085189 33226708786265328110078473)
        ·
          refine ⟨24920031589698996082558855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33226708786265328110078473 24920031589698996082558855)
          ·
            refine ⟨37380047384548494123838283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24920031589698996082558855 37380047384548494123838283)
            ·
              refine ⟨56070071076822741185757425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37380047384548494123838283 56070071076822741185757425)
              ·
                refine ⟨42052553307617055889318069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56070071076822741185757425 42052553307617055889318069)
                ·
                  refine ⟨3942426872589098989623569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42052553307617055889318069 3942426872589098989623569)
                  ·
                    refine ⟨2956820154441824242217677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3942426872589098989623569 2956820154441824242217677)
                    ·
                      refine ⟨1108807557915684090831629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956820154441824242217677 1108807557915684090831629)
                      ·
                        rfl

theorem cell23_2159395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_2159395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159395 prefixEnd_2159395 := by exact prefixLift 2159395
  have htrace : WordTrace (prefixWord ++ tailWord_2159395) baseStart_2159395 baseEnd_2159395 := by
    simpa [prefixWord, tailWord_2159395, baseEnd_2159395] using wordTrace_append hprefix tailTrace_2159395
  have hstable : (prefixWord ++ tailWord_2159395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159395).length < 2 ^ (prefixWord ++ tailWord_2159395).sum := by decide
  have hdescent : baseEnd_2159395 < baseStart_2159395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159442 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_2159442 : Nat := 118140960795 + 2159442 * 2 ^ 59
def prefixEnd_2159442 : Nat := 4983230072969 + 3 ^ 40 * 2159442 * 2
def baseEnd_2159442 : Nat := 1108831691506445406943913

theorem tailTrace_2159442 : CollatzResearch.WordTrace tailWord_2159442 prefixEnd_2159442 1108831691506445406943913 := by
  unfold tailWord_2159442
  simp only [CollatzResearch.WordTrace]
  refine ⟨19690330060679478044194145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52507546828478608117851053 19690330060679478044194145)
  ·
    refine ⟨14767747545509608533145609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19690330060679478044194145 14767747545509608533145609)
    ·
      refine ⟨11075810659132206399859207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14767747545509608533145609 11075810659132206399859207)
      ·
        refine ⟨16613715988698309599788811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11075810659132206399859207 16613715988698309599788811)
        ·
          refine ⟨24920573983047464399683217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16613715988698309599788811 24920573983047464399683217)
          ·
            refine ⟨18690430487285598299762413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24920573983047464399683217 18690430487285598299762413)
            ·
              refine ⟨7008911432732099362410905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18690430487285598299762413 7008911432732099362410905)
              ·
                refine ⟨5256683574549074521808179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7008911432732099362410905 5256683574549074521808179)
                ·
                  refine ⟨7885025361823611782712269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5256683574549074521808179 7885025361823611782712269)
                  ·
                    refine ⟨2956884510683854418517101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7885025361823611782712269 2956884510683854418517101)
                    ·
                      refine ⟨1108831691506445406943913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956884510683854418517101 1108831691506445406943913)
                      ·
                        rfl

theorem cell23_2159442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_2159442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159442 prefixEnd_2159442 := by exact prefixLift 2159442
  have htrace : WordTrace (prefixWord ++ tailWord_2159442) baseStart_2159442 baseEnd_2159442 := by
    simpa [prefixWord, tailWord_2159442, baseEnd_2159442] using wordTrace_append hprefix tailTrace_2159442
  have hstable : (prefixWord ++ tailWord_2159442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159442).length < 2 ^ (prefixWord ++ tailWord_2159442).sum := by decide
  have hdescent : baseEnd_2159442 < baseStart_2159442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159459 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2159459 : Nat := 118140960795 + 2159459 * 2 ^ 59
def prefixEnd_2159459 : Nat := 4983230072969 + 3 ^ 40 * 2159459 * 2
def baseEnd_2159459 : Nat := 1108840420677571840431335

theorem tailTrace_2159459 : CollatzResearch.WordTrace tailWord_2159459 prefixEnd_2159459 1108840420677571840431335 := by
  unfold tailWord_2159459
  simp only [CollatzResearch.WordTrace]
  refine ⟨78761940283656324080145431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52507960189104216053430287 78761940283656324080145431)
  ·
    refine ⟨118142910425484486120218147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78761940283656324080145431 118142910425484486120218147)
    ·
      refine ⟨177214365638226729180327221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118142910425484486120218147 177214365638226729180327221)
      ·
        refine ⟨16613846778583755860655677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177214365638226729180327221 16613846778583755860655677)
        ·
          refine ⟨6230192541968908447745879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16613846778583755860655677 6230192541968908447745879)
          ·
            refine ⟨9345288812953362671618819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230192541968908447745879 9345288812953362671618819)
            ·
              refine ⟨14017933219430044007428229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9345288812953362671618819 14017933219430044007428229)
              ·
                refine ⟨2628362478643133251392793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14017933219430044007428229 2628362478643133251392793)
                ·
                  refine ⟨1971271858982349938544595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628362478643133251392793 1971271858982349938544595)
                  ·
                    refine ⟨2956907788473524907816893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1971271858982349938544595 2956907788473524907816893)
                    ·
                      refine ⟨1108840420677571840431335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956907788473524907816893 1108840420677571840431335)
                      ·
                        rfl

theorem cell23_2159459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2159459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159459 prefixEnd_2159459 := by exact prefixLift 2159459
  have htrace : WordTrace (prefixWord ++ tailWord_2159459) baseStart_2159459 baseEnd_2159459 := by
    simpa [prefixWord, tailWord_2159459, baseEnd_2159459] using wordTrace_append hprefix tailTrace_2159459
  have hstable : (prefixWord ++ tailWord_2159459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159459).length < 2 ^ (prefixWord ++ tailWord_2159459).sum := by decide
  have hdescent : baseEnd_2159459 < baseStart_2159459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159460 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_2159460 : Nat := 118140960795 + 2159460 * 2 ^ 59
def prefixEnd_2159460 : Nat := 4983230072969 + 3 ^ 40 * 2159460 * 2
def baseEnd_2159460 : Nat := 1108840934158226336518831

theorem tailTrace_2159460 : CollatzResearch.WordTrace tailWord_2159460 prefixEnd_2159460 1108840934158226336518831 := by
  unfold tailWord_2159460
  simp only [CollatzResearch.WordTrace]
  refine ⟨39380988378326350625465917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52507984504435134167287889 39380988378326350625465917)
  ·
    refine ⟨14767870641872381484549719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39380988378326350625465917 14767870641872381484549719)
    ·
      refine ⟨22151805962808572226824579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14767870641872381484549719 22151805962808572226824579)
      ·
        refine ⟨33227708944212858340236869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22151805962808572226824579 33227708944212858340236869)
        ·
          refine ⟨6230195427039910938794413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33227708944212858340236869 6230195427039910938794413)
          ·
            refine ⟨2336323285139966602047905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6230195427039910938794413 2336323285139966602047905)
            ·
              refine ⟨1752242463854974951535929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336323285139966602047905 1752242463854974951535929)
              ·
                refine ⟨1314181847891231213651947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752242463854974951535929 1314181847891231213651947)
                ·
                  refine ⟨1971272771836846820477921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314181847891231213651947 1971272771836846820477921)
                  ·
                    refine ⟨1478454578877635115358441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1971272771836846820477921 1478454578877635115358441)
                    ·
                      refine ⟨1108840934158226336518831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478454578877635115358441 1108840934158226336518831)
                      ·
                        rfl

theorem cell23_2159460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_2159460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159460 prefixEnd_2159460 := by exact prefixLift 2159460
  have htrace : WordTrace (prefixWord ++ tailWord_2159460) baseStart_2159460 baseEnd_2159460 := by
    simpa [prefixWord, tailWord_2159460, baseEnd_2159460] using wordTrace_append hprefix tailTrace_2159460
  have hstable : (prefixWord ++ tailWord_2159460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159460).length < 2 ^ (prefixWord ++ tailWord_2159460).sum := by decide
  have hdescent : baseEnd_2159460 < baseStart_2159460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159485 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2159485 : Nat := 118140960795 + 2159485 * 2 ^ 59
def prefixEnd_2159485 : Nat := 4983230072969 + 3 ^ 40 * 2159485 * 2
def baseEnd_2159485 : Nat := 1108853771174588738706215

theorem tailTrace_2159485 : CollatzResearch.WordTrace tailWord_2159485 prefixEnd_2159485 1108853771174588738706215 := by
  unfold tailWord_2159485
  simp only [CollatzResearch.WordTrace]
  refine ⟨78762888581562130520591909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52508592387708087013727939 78762888581562130520591909)
  ·
    refine ⟨14768041609042899472610983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78762888581562130520591909 14768041609042899472610983)
    ·
      refine ⟨22152062413564349208916475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14768041609042899472610983 22152062413564349208916475)
      ·
        refine ⟨33228093620346523813374713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22152062413564349208916475 33228093620346523813374713)
        ·
          refine ⟨24921070215259892860031035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33228093620346523813374713 24921070215259892860031035)
          ·
            refine ⟨37381605322889839290046553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24921070215259892860031035 37381605322889839290046553)
            ·
              refine ⟨28036203992167379467534915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37381605322889839290046553 28036203992167379467534915)
              ·
                refine ⟨42054305988251069201302373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28036203992167379467534915 42054305988251069201302373)
                ·
                  refine ⟨7885182372797075475244195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42054305988251069201302373 7885182372797075475244195)
                  ·
                    refine ⟨11827773559195613212866293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7885182372797075475244195 11827773559195613212866293)
                    ·
                      refine ⟨1108853771174588738706215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11827773559195613212866293 1108853771174588738706215)
                      ·
                        rfl

theorem cell23_2159485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2159485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159485 prefixEnd_2159485 := by exact prefixLift 2159485
  have htrace : WordTrace (prefixWord ++ tailWord_2159485) baseStart_2159485 baseEnd_2159485 := by
    simpa [prefixWord, tailWord_2159485, baseEnd_2159485] using wordTrace_append hprefix tailTrace_2159485
  have hstable : (prefixWord ++ tailWord_2159485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159485).length < 2 ^ (prefixWord ++ tailWord_2159485).sum := by decide
  have hdescent : baseEnd_2159485 < baseStart_2159485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159510 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2159510 : Nat := 118140960795 + 2159510 * 2 ^ 59
def prefixEnd_2159510 : Nat := 4983230072969 + 3 ^ 40 * 2159510 * 2
def baseEnd_2159510 : Nat := 1108866608190951140893601

theorem tailTrace_2159510 : CollatzResearch.WordTrace tailWord_2159510 prefixEnd_2159510 1108866608190951140893601 := by
  unfold tailWord_2159510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922737525404472486890749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52509200270981039860167989 4922737525404472486890749)
  ·
    refine ⟨1846026572026677182584031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4922737525404472486890749 1846026572026677182584031)
    ·
      refine ⟨2769039858040015773876047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846026572026677182584031 2769039858040015773876047)
      ·
        refine ⟨4153559787060023660814071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769039858040015773876047 4153559787060023660814071)
        ·
          refine ⟨6230339680590035491221107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153559787060023660814071 6230339680590035491221107)
          ·
            refine ⟨9345509520885053236831661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230339680590035491221107 9345509520885053236831661)
            ·
              refine ⟨3504566070331894963811873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9345509520885053236831661 3504566070331894963811873)
              ·
                refine ⟨2628424552748921222858905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504566070331894963811873 2628424552748921222858905)
                ·
                  refine ⟨1971318414561690917144179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628424552748921222858905 1971318414561690917144179)
                  ·
                    refine ⟨2956977621842536375716269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1971318414561690917144179 2956977621842536375716269)
                    ·
                      refine ⟨1108866608190951140893601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2956977621842536375716269 1108866608190951140893601)
                      ·
                        rfl

theorem cell23_2159510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2159510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159510 prefixEnd_2159510 := by exact prefixLift 2159510
  have htrace : WordTrace (prefixWord ++ tailWord_2159510) baseStart_2159510 baseEnd_2159510 := by
    simpa [prefixWord, tailWord_2159510, baseEnd_2159510] using wordTrace_append hprefix tailTrace_2159510
  have hstable : (prefixWord ++ tailWord_2159510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159510).length < 2 ^ (prefixWord ++ tailWord_2159510).sum := by decide
  have hdescent : baseEnd_2159510 < baseStart_2159510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159522 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2159522 : Nat := 118140960795 + 2159522 * 2 ^ 59
def prefixEnd_2159522 : Nat := 4983230072969 + 3 ^ 40 * 2159522 * 2
def baseEnd_2159522 : Nat := 123208085550978343771505

theorem tailTrace_2159522 : CollatzResearch.WordTrace tailWord_2159522 prefixEnd_2159522 123208085550978343771505 := by
  unfold tailWord_2159522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19691059520607021459922205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52509492054952057226459213 19691059520607021459922205)
  ·
    refine ⟨7384147320227633047470827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19691059520607021459922205 7384147320227633047470827)
    ·
      refine ⟨11076220980341449571206241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7384147320227633047470827 11076220980341449571206241)
      ·
        refine ⟨8307165735256087178404681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11076220980341449571206241 8307165735256087178404681)
        ·
          refine ⟨6230374301442065383803511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8307165735256087178404681 6230374301442065383803511)
          ·
            refine ⟨9345561452163098075705267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230374301442065383803511 9345561452163098075705267)
            ·
              refine ⟨14018342178244647113557901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9345561452163098075705267 14018342178244647113557901)
              ·
                refine ⟨5256878316841742667584213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14018342178244647113557901 5256878316841742667584213)
                ·
                  refine ⟨123208085550978343771505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5256878316841742667584213 123208085550978343771505)
                  ·
                    rfl

theorem cell23_2159522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2159522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159522 prefixEnd_2159522 := by exact prefixLift 2159522
  have htrace : WordTrace (prefixWord ++ tailWord_2159522) baseStart_2159522 baseEnd_2159522 := by
    simpa [prefixWord, tailWord_2159522, baseEnd_2159522] using wordTrace_append hprefix tailTrace_2159522
  have hstable : (prefixWord ++ tailWord_2159522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159522).length < 2 ^ (prefixWord ++ tailWord_2159522).sum := by decide
  have hdescent : baseEnd_2159522 < baseStart_2159522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159535 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 6, 5]
def baseStart_2159535 : Nat := 118140960795 + 2159535 * 2 ^ 59
def prefixEnd_2159535 : Nat := 4983230072969 + 3 ^ 40 * 2159535 * 2
def baseEnd_2159535 : Nat := 369626481735771181026995

theorem tailTrace_2159535 : CollatzResearch.WordTrace tailWord_2159535 prefixEnd_2159535 369626481735771181026995 := by
  unfold tailWord_2159535
  simp only [CollatzResearch.WordTrace]
  refine ⟨78764712231380989059912059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52509808154253992706608039 78764712231380989059912059)
  ·
    refine ⟨118147068347071483589868089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78764712231380989059912059 118147068347071483589868089)
    ·
      refine ⟨88610301260303612692401067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118147068347071483589868089 88610301260303612692401067)
      ·
        refine ⟨132915451890455419038601601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88610301260303612692401067 132915451890455419038601601)
        ·
          refine ⟨99686588917841564278951201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132915451890455419038601601 99686588917841564278951201)
          ·
            refine ⟨74764941688381173209213401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99686588917841564278951201 74764941688381173209213401)
            ·
              refine ⟨56073706266285879906910051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74764941688381173209213401 56073706266285879906910051)
              ·
                refine ⟨84110559399428819860365077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56073706266285879906910051 84110559399428819860365077)
                ·
                  refine ⟨3942682471848225930954613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84110559399428819860365077 3942682471848225930954613)
                  ·
                    refine ⟨369626481735771181026995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3942682471848225930954613 369626481735771181026995)
                    ·
                      rfl

theorem cell23_2159535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_2159535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159535 prefixEnd_2159535 := by exact prefixLift 2159535
  have htrace : WordTrace (prefixWord ++ tailWord_2159535) baseStart_2159535 baseEnd_2159535 := by
    simpa [prefixWord, tailWord_2159535, baseEnd_2159535] using wordTrace_append hprefix tailTrace_2159535
  have hstable : (prefixWord ++ tailWord_2159535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159535).length < 2 ^ (prefixWord ++ tailWord_2159535).sum := by decide
  have hdescent : baseEnd_2159535 < baseStart_2159535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159575 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_2159575 : Nat := 118140960795 + 2159575 * 2 ^ 59
def prefixEnd_2159575 : Nat := 4983230072969 + 3 ^ 40 * 2159575 * 2
def baseEnd_2159575 : Nat := 1108899984433493386580801

theorem tailTrace_2159575 : CollatzResearch.WordTrace tailWord_2159575 prefixEnd_2159575 1108899984433493386580801 := by
  unfold tailWord_2159575
  simp only [CollatzResearch.WordTrace]
  refine ⟨78766171151236075891368179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52510780767490717260912119 78766171151236075891368179)
  ·
    refine ⟨118149256726854113837052269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78766171151236075891368179 118149256726854113837052269)
    ·
      refine ⟨44305971272570292688894601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118149256726854113837052269 44305971272570292688894601)
      ·
        refine ⟨33229478454427719516670951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44305971272570292688894601 33229478454427719516670951)
        ·
          refine ⟨49844217681641579275006427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33229478454427719516670951 49844217681641579275006427)
          ·
            refine ⟨74766326522462368912509641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49844217681641579275006427 74766326522462368912509641)
            ·
              refine ⟨56074744891846776684382231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74766326522462368912509641 56074744891846776684382231)
              ·
                refine ⟨84112117337770165026573347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56074744891846776684382231 84112117337770165026573347)
                ·
                  refine ⟨126168176006655247539860021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84112117337770165026573347 126168176006655247539860021)
                  ·
                    refine ⟨11828266500623929456861877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126168176006655247539860021 11828266500623929456861877)
                    ·
                      refine ⟨1108899984433493386580801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11828266500623929456861877 1108899984433493386580801)
                      ·
                        rfl

theorem cell23_2159575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_2159575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159575 prefixEnd_2159575 := by exact prefixLift 2159575
  have htrace : WordTrace (prefixWord ++ tailWord_2159575) baseStart_2159575 baseEnd_2159575 := by
    simpa [prefixWord, tailWord_2159575, baseEnd_2159575] using wordTrace_append hprefix tailTrace_2159575
  have hstable : (prefixWord ++ tailWord_2159575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159575).length < 2 ^ (prefixWord ++ tailWord_2159575).sum := by decide
  have hdescent : baseEnd_2159575 < baseStart_2159575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159592 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2159592 : Nat := 118140960795 + 2159592 * 2 ^ 59
def prefixEnd_2159592 : Nat := 4983230072969 + 3 ^ 40 * 2159592 * 2
def baseEnd_2159592 : Nat := 1108908713604619820068223

theorem tailTrace_2159592 : CollatzResearch.WordTrace tailWord_2159592 prefixEnd_2159592 1108908713604619820068223 := by
  unfold tailWord_2159592
  simp only [CollatzResearch.WordTrace]
  refine ⟨39383395596087243897368515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52511194128116325196491353 39383395596087243897368515)
  ·
    refine ⟨59075093394130865846052773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39383395596087243897368515 59075093394130865846052773)
    ·
      refine ⟨11076580011399537346134895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59075093394130865846052773 11076580011399537346134895)
      ·
        refine ⟨16614870017099306019202343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11076580011399537346134895 16614870017099306019202343)
        ·
          refine ⟨24922305025648959028803515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16614870017099306019202343 24922305025648959028803515)
          ·
            refine ⟨37383457538473438543205273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24922305025648959028803515 37383457538473438543205273)
            ·
              refine ⟨28037593153855078907403955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37383457538473438543205273 28037593153855078907403955)
              ·
                refine ⟨42056389730782618361105933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28037593153855078907403955 42056389730782618361105933)
                ·
                  refine ⟨15771146149043481885414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42056389730782618361105933 15771146149043481885414725)
                  ·
                    refine ⟨2957089902945652853515261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15771146149043481885414725 2957089902945652853515261)
                    ·
                      refine ⟨1108908713604619820068223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957089902945652853515261 1108908713604619820068223)
                      ·
                        rfl

theorem cell23_2159592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2159592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159592 prefixEnd_2159592 := by exact prefixLift 2159592
  have htrace : WordTrace (prefixWord ++ tailWord_2159592) baseStart_2159592 baseEnd_2159592 := by
    simpa [prefixWord, tailWord_2159592, baseEnd_2159592] using wordTrace_append hprefix tailTrace_2159592
  have hstable : (prefixWord ++ tailWord_2159592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159592).length < 2 ^ (prefixWord ++ tailWord_2159592).sum := by decide
  have hdescent : baseEnd_2159592 < baseStart_2159592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159606 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2159606 : Nat := 118140960795 + 2159606 * 2 ^ 59
def prefixEnd_2159606 : Nat := 4983230072969 + 3 ^ 40 * 2159606 * 2
def baseEnd_2159606 : Nat := 1108915902333782765293159

theorem tailTrace_2159606 : CollatzResearch.WordTrace tailWord_2159606 prefixEnd_2159606 1108915902333782765293159 := by
  unfold tailWord_2159606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922956363382735511609167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52511534542749178790497781 4922956363382735511609167)
  ·
    refine ⟨7384434545074103267413751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4922956363382735511609167 7384434545074103267413751)
    ·
      refine ⟨11076651817611154901120627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7384434545074103267413751 11076651817611154901120627)
      ·
        refine ⟨16614977726416732351680941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11076651817611154901120627 16614977726416732351680941)
        ·
          refine ⟨6230616647406274631880353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16614977726416732351680941 6230616647406274631880353)
          ·
            refine ⟨4672962485554705973910265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6230616647406274631880353 4672962485554705973910265)
            ·
              refine ⟨3504721864166029480432699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4672962485554705973910265 3504721864166029480432699)
              ·
                refine ⟨5257082796249044220649049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504721864166029480432699 5257082796249044220649049)
                ·
                  refine ⟨3942812097186783165486787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257082796249044220649049 3942812097186783165486787)
                  ·
                    refine ⟨5914218145780174748230181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942812097186783165486787 5914218145780174748230181)
                    ·
                      refine ⟨1108915902333782765293159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5914218145780174748230181 1108915902333782765293159)
                      ·
                        rfl

theorem cell23_2159606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2159606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159606 prefixEnd_2159606 := by exact prefixLift 2159606
  have htrace : WordTrace (prefixWord ++ tailWord_2159606) baseStart_2159606 baseEnd_2159606 := by
    simpa [prefixWord, tailWord_2159606, baseEnd_2159606] using wordTrace_append hprefix tailTrace_2159606
  have hstable : (prefixWord ++ tailWord_2159606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159606).length < 2 ^ (prefixWord ++ tailWord_2159606).sum := by decide
  have hdescent : baseEnd_2159606 < baseStart_2159606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159609 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 3]
def baseStart_2159609 : Nat := 118140960795 + 2159609 * 2 ^ 59
def prefixEnd_2159609 : Nat := 4983230072969 + 3 ^ 40 * 2159609 * 2
def baseEnd_2159609 : Nat := 1108917442775746253555645

theorem tailTrace_2159609 : CollatzResearch.WordTrace tailWord_2159609 prefixEnd_2159609 1108917442775746253555645 := by
  unfold tailWord_2159609
  simp only [CollatzResearch.WordTrace]
  refine ⟨78767411233112899698105881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52511607488741933132070587 78767411233112899698105881)
  ·
    refine ⟨59075558424834674773579411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78767411233112899698105881 59075558424834674773579411)
    ·
      refine ⟨88613337637252012160369117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59075558424834674773579411 88613337637252012160369117)
      ·
        refine ⟨33230001613969504560138419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88613337637252012160369117 33230001613969504560138419)
        ·
          refine ⟨49845002420954256840207629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33230001613969504560138419 49845002420954256840207629)
          ·
            refine ⟨18691875907857846315077861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49845002420954256840207629 18691875907857846315077861)
            ·
              refine ⟨3504726732723346184077099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18691875907857846315077861 3504726732723346184077099)
              ·
                refine ⟨5257090099085019276115649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504726732723346184077099 5257090099085019276115649)
                ·
                  refine ⟨3942817574313764457086737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257090099085019276115649 3942817574313764457086737)
                  ·
                    refine ⟨2957113180735323342815053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3942817574313764457086737 2957113180735323342815053)
                    ·
                      refine ⟨1108917442775746253555645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957113180735323342815053 1108917442775746253555645)
                      ·
                        rfl

theorem cell23_2159609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_2159609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159609 prefixEnd_2159609 := by exact prefixLift 2159609
  have htrace : WordTrace (prefixWord ++ tailWord_2159609) baseStart_2159609 baseEnd_2159609 := by
    simpa [prefixWord, tailWord_2159609, baseEnd_2159609] using wordTrace_append hprefix tailTrace_2159609
  have hstable : (prefixWord ++ tailWord_2159609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159609).length < 2 ^ (prefixWord ++ tailWord_2159609).sum := by decide
  have hdescent : baseEnd_2159609 < baseStart_2159609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159615 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_2159615 : Nat := 118140960795 + 2159615 * 2 ^ 59
def prefixEnd_2159615 : Nat := 4983230072969 + 3 ^ 40 * 2159615 * 2
def baseEnd_2159615 : Nat := 1108920523659673230080617

theorem tailTrace_2159615 : CollatzResearch.WordTrace tailWord_2159615 prefixEnd_2159615 1108920523659673230080617 := by
  unfold tailWord_2159615
  simp only [CollatzResearch.WordTrace]
  refine ⟨78767630071091162722824299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52511753380727441815216199 78767630071091162722824299)
  ·
    refine ⟨118151445106636744084236449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78767630071091162722824299 118151445106636744084236449)
    ·
      refine ⟨88613583829977558063177337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118151445106636744084236449 88613583829977558063177337)
      ·
        refine ⟨66460187872483168547383003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88613583829977558063177337 66460187872483168547383003)
        ·
          refine ⟨99690281808724752821074505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66460187872483168547383003 99690281808724752821074505)
          ·
            refine ⟨74767711356543564615805879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99690281808724752821074505 74767711356543564615805879)
            ·
              refine ⟨112151567034815346923708819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74767711356543564615805879 112151567034815346923708819)
              ·
                refine ⟨168227350552223020385563229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112151567034815346923708819 168227350552223020385563229)
                ·
                  refine ⟨63085256457083632644586211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168227350552223020385563229 63085256457083632644586211)
                  ·
                    refine ⟨94627884685625448966879317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63085256457083632644586211 94627884685625448966879317)
                    ·
                      refine ⟨1108920523659673230080617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94627884685625448966879317 1108920523659673230080617)
                      ·
                        rfl

theorem cell23_2159615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_2159615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159615 prefixEnd_2159615 := by exact prefixLift 2159615
  have htrace : WordTrace (prefixWord ++ tailWord_2159615) baseStart_2159615 baseEnd_2159615 := by
    simpa [prefixWord, tailWord_2159615, baseEnd_2159615] using wordTrace_append hprefix tailTrace_2159615
  have hstable : (prefixWord ++ tailWord_2159615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159615).length < 2 ^ (prefixWord ++ tailWord_2159615).sum := by decide
  have hdescent : baseEnd_2159615 < baseStart_2159615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159642 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_2159642 : Nat := 118140960795 + 2159642 * 2 ^ 59
def prefixEnd_2159642 : Nat := 4983230072969 + 3 ^ 40 * 2159642 * 2
def baseEnd_2159642 : Nat := 369644795879114874814331

theorem tailTrace_2159642 : CollatzResearch.WordTrace tailWord_2159642 prefixEnd_2159642 369644795879114874814331 := by
  unfold tailWord_2159642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19692153710498336583514295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52512409894662230889371453 19692153710498336583514295)
  ·
    refine ⟨29538230565747504875271443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19692153710498336583514295 29538230565747504875271443)
    ·
      refine ⟨44307345848621257312907165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29538230565747504875271443 44307345848621257312907165)
      ·
        refine ⟨16615254693232971492340187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44307345848621257312907165 16615254693232971492340187)
        ·
          refine ⟨24922882039849457238510281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16615254693232971492340187 24922882039849457238510281)
          ·
            refine ⟨18692161529887092928882711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24922882039849457238510281 18692161529887092928882711)
            ·
              refine ⟨28038242294830639393324067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18692161529887092928882711 28038242294830639393324067)
              ·
                refine ⟨42057363442245959089986101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28038242294830639393324067 42057363442245959089986101)
                ·
                  refine ⟨3942877822710558664686197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42057363442245959089986101 3942877822710558664686197)
                  ·
                    refine ⟨369644795879114874814331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3942877822710558664686197 369644795879114874814331)
                    ·
                      rfl

theorem cell23_2159642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_2159642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159642 prefixEnd_2159642 := by exact prefixLift 2159642
  have htrace : WordTrace (prefixWord ++ tailWord_2159642) baseStart_2159642 baseEnd_2159642 := by
    simpa [prefixWord, tailWord_2159642, baseEnd_2159642] using wordTrace_append hprefix tailTrace_2159642
  have hstable : (prefixWord ++ tailWord_2159642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159642).length < 2 ^ (prefixWord ++ tailWord_2159642).sum := by decide
  have hdescent : baseEnd_2159642 < baseStart_2159642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159673 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2159673 : Nat := 118140960795 + 2159673 * 2 ^ 59
def prefixEnd_2159673 : Nat := 4983230072969 + 3 ^ 40 * 2159673 * 2
def baseEnd_2159673 : Nat := 1108950305537634003155351

theorem tailTrace_2159673 : CollatzResearch.WordTrace tailWord_2159673 prefixEnd_2159673 1108950305537634003155351 := by
  unfold tailWord_2159673
  simp only [CollatzResearch.WordTrace]
  refine ⟨78769745504881038628435673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52513163669920692418957115 78769745504881038628435673)
  ·
    refine ⟨59077309128660778971326755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78769745504881038628435673 59077309128660778971326755)
    ·
      refine ⟨88615963692991168456990133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59077309128660778971326755 88615963692991168456990133)
      ·
        refine ⟨8307746596217922042842825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88615963692991168456990133 8307746596217922042842825)
        ·
          refine ⟨6230809947163441532132119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8307746596217922042842825 6230809947163441532132119)
          ·
            refine ⟨9346214920745162298198179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230809947163441532132119 9346214920745162298198179)
            ·
              refine ⟨14019322381117743447297269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346214920745162298198179 14019322381117743447297269)
              ·
                refine ⟨1314311473229788448184119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14019322381117743447297269 1314311473229788448184119)
                ·
                  refine ⟨1971467209844682672276179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314311473229788448184119 1971467209844682672276179)
                  ·
                    refine ⟨2957200814767024008414269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1971467209844682672276179 2957200814767024008414269)
                    ·
                      refine ⟨1108950305537634003155351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957200814767024008414269 1108950305537634003155351)
                      ·
                        rfl

theorem cell23_2159673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2159673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159673 prefixEnd_2159673 := by exact prefixLift 2159673
  have htrace : WordTrace (prefixWord ++ tailWord_2159673) baseStart_2159673 baseEnd_2159673 := by
    simpa [prefixWord, tailWord_2159673, baseEnd_2159673] using wordTrace_append hprefix tailTrace_2159673
  have hstable : (prefixWord ++ tailWord_2159673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159673).length < 2 ^ (prefixWord ++ tailWord_2159673).sum := by decide
  have hdescent : baseEnd_2159673 < baseStart_2159673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159676 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_2159676 : Nat := 118140960795 + 2159676 * 2 ^ 59
def prefixEnd_2159676 : Nat := 4983230072969 + 3 ^ 40 * 2159676 * 2
def baseEnd_2159676 : Nat := 369650615326532497139279

theorem tailTrace_2159676 : CollatzResearch.WordTrace tailWord_2159676 prefixEnd_2159676 369650615326532497139279 := by
  unfold tailWord_2159676
  simp only [CollatzResearch.WordTrace]
  refine ⟨39384927461935085070397441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52513236615913446760529921 39384927461935085070397441)
  ·
    refine ⟨29538695596451313802798081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39384927461935085070397441 29538695596451313802798081)
    ·
      refine ⟨22154021697338485352098561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29538695596451313802798081 22154021697338485352098561)
      ·
        refine ⟨16615516273003864014073921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22154021697338485352098561 16615516273003864014073921)
        ·
          refine ⟨12461637204752898010555441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16615516273003864014073921 12461637204752898010555441)
          ·
            refine ⟨9346227903564673507916581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12461637204752898010555441 9346227903564673507916581)
            ·
              refine ⟨1752417731918376282734359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9346227903564673507916581 1752417731918376282734359)
              ·
                refine ⟨2628626597877564424101539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752417731918376282734359 2628626597877564424101539)
                ·
                  refine ⟨3942939896816346636152309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628626597877564424101539 3942939896816346636152309)
                  ·
                    refine ⟨369650615326532497139279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3942939896816346636152309 369650615326532497139279)
                    ·
                      rfl

theorem cell23_2159676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_2159676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159676 prefixEnd_2159676 := by exact prefixLift 2159676
  have htrace : WordTrace (prefixWord ++ tailWord_2159676) baseStart_2159676 baseEnd_2159676 := by
    simpa [prefixWord, tailWord_2159676, baseEnd_2159676] using wordTrace_append hprefix tailTrace_2159676
  have hstable : (prefixWord ++ tailWord_2159676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159676).length < 2 ^ (prefixWord ++ tailWord_2159676).sum := by decide
  have hdescent : baseEnd_2159676 < baseStart_2159676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159689 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 2, 4]
def baseStart_2159689 : Nat := 118140960795 + 2159689 * 2 ^ 59
def prefixEnd_2159689 : Nat := 4983230072969 + 3 ^ 40 * 2159689 * 2
def baseEnd_2159689 : Nat := 369652840409368646851759

theorem tailTrace_2159689 : CollatzResearch.WordTrace tailWord_2159689 prefixEnd_2159689 369652840409368646851759 := by
  unfold tailWord_2159689
  simp only [CollatzResearch.WordTrace]
  refine ⟨78770329072823073361018121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52513552715215382240678747 78770329072823073361018121)
  ·
    refine ⟨59077746804617305020763591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78770329072823073361018121 59077746804617305020763591)
    ·
      refine ⟨88616620206925957531145387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59077746804617305020763591 88616620206925957531145387)
      ·
        refine ⟨132924930310388936296718081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88616620206925957531145387 132924930310388936296718081)
        ·
          refine ⟨99693697732791702222538561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132924930310388936296718081 99693697732791702222538561)
          ·
            refine ⟨74770273299593776666903921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99693697732791702222538561 74770273299593776666903921)
            ·
              refine ⟨56077704974695332500177941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74770273299593776666903921 56077704974695332500177941)
              ·
                refine ⟨2628642420688843710945841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56077704974695332500177941 2628642420688843710945841)
                ·
                  refine ⟨1971481815516632783209381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628642420688843710945841 1971481815516632783209381)
                  ·
                    refine ⟨369652840409368646851759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971481815516632783209381 369652840409368646851759)
                    ·
                      rfl

theorem cell23_2159689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 4].length) (baseStart_2159689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159689 prefixEnd_2159689 := by exact prefixLift 2159689
  have htrace : WordTrace (prefixWord ++ tailWord_2159689) baseStart_2159689 baseEnd_2159689 := by
    simpa [prefixWord, tailWord_2159689, baseEnd_2159689] using wordTrace_append hprefix tailTrace_2159689
  have hstable : (prefixWord ++ tailWord_2159689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159689).length < 2 ^ (prefixWord ++ tailWord_2159689).sum := by decide
  have hdescent : baseEnd_2159689 < baseStart_2159689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159692 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2159692 : Nat := 118140960795 + 2159692 * 2 ^ 59
def prefixEnd_2159692 : Nat := 4983230072969 + 3 ^ 40 * 2159692 * 2
def baseEnd_2159692 : Nat := 1108960061670069428817763

theorem tailTrace_2159692 : CollatzResearch.WordTrace tailWord_2159692 prefixEnd_2159692 1108960061670069428817763 := by
  unfold tailWord_2159692
  simp only [CollatzResearch.WordTrace]
  refine ⟨39385219245906102436688665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52513625661208136582251553 39385219245906102436688665)
  ·
    refine ⟨29538914434429576827516499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39385219245906102436688665 29538914434429576827516499)
    ·
      refine ⟨44308371651644365241274749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29538914434429576827516499 44308371651644365241274749)
      ·
        refine ⟨16615639369366636965478031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44308371651644365241274749 16615639369366636965478031)
        ·
          refine ⟨24923459054049955448217047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16615639369366636965478031 24923459054049955448217047)
          ·
            refine ⟨37385188581074933172325571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24923459054049955448217047 37385188581074933172325571)
            ·
              refine ⟨56077782871612399758488357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37385188581074933172325571 56077782871612399758488357)
              ·
                refine ⟨10514584288427324954716567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56077782871612399758488357 10514584288427324954716567)
                ·
                  refine ⟨15771876432640987432074851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10514584288427324954716567 15771876432640987432074851)
                  ·
                    refine ⟨23657814648961481148112277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15771876432640987432074851 23657814648961481148112277)
                    ·
                      refine ⟨1108960061670069428817763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23657814648961481148112277 1108960061670069428817763)
                      ·
                        rfl

theorem cell23_2159692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2159692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159692 prefixEnd_2159692 := by exact prefixLift 2159692
  have htrace : WordTrace (prefixWord ++ tailWord_2159692) baseStart_2159692 baseEnd_2159692 := by
    simpa [prefixWord, tailWord_2159692, baseEnd_2159692] using wordTrace_append hprefix tailTrace_2159692
  have hstable : (prefixWord ++ tailWord_2159692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159692).length < 2 ^ (prefixWord ++ tailWord_2159692).sum := by decide
  have hdescent : baseEnd_2159692 < baseStart_2159692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159710 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2159710 : Nat := 118140960795 + 2159710 * 2 ^ 59
def prefixEnd_2159710 : Nat := 4983230072969 + 3 ^ 40 * 2159710 * 2
def baseEnd_2159710 : Nat := 369656434773950119464227

theorem tailTrace_2159710 : CollatzResearch.WordTrace tailWord_2159710 prefixEnd_2159710 369656434773950119464227 := by
  unfold tailWord_2159710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846386875718374243441573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52514063337164662631688389 9846386875718374243441573)
  ·
    refine ⟨1846197539197195170645295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9846386875718374243441573 1846197539197195170645295)
    ·
      refine ⟨2769296308795792755967943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846197539197195170645295 2769296308795792755967943)
      ·
        refine ⟨4153944463193689133951915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769296308795792755967943 4153944463193689133951915)
        ·
          refine ⟨6230916694790533700927873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153944463193689133951915 6230916694790533700927873)
          ·
            refine ⟨4673187521092900275695905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6230916694790533700927873 4673187521092900275695905)
            ·
              refine ⟨3504890640819675206771929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4673187521092900275695905 3504890640819675206771929)
              ·
                refine ⟨2628667980614756405078947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504890640819675206771929 2628667980614756405078947)
                ·
                  refine ⟨3943001970922134607618421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2628667980614756405078947 3943001970922134607618421)
                  ·
                    refine ⟨369656434773950119464227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3943001970922134607618421 369656434773950119464227)
                    ·
                      rfl

theorem cell23_2159710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2159710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159710 prefixEnd_2159710 := by exact prefixLift 2159710
  have htrace : WordTrace (prefixWord ++ tailWord_2159710) baseStart_2159710 baseEnd_2159710 := by
    simpa [prefixWord, tailWord_2159710, baseEnd_2159710] using wordTrace_append hprefix tailTrace_2159710
  have hstable : (prefixWord ++ tailWord_2159710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159710).length < 2 ^ (prefixWord ++ tailWord_2159710).sum := by decide
  have hdescent : baseEnd_2159710 < baseStart_2159710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159719 : List Nat := [1, 1, 5, 1, 1, 3, 4, 7]
def baseStart_2159719 : Nat := 118140960795 + 2159719 * 2 ^ 59
def prefixEnd_2159719 : Nat := 4983230072969 + 3 ^ 40 * 2159719 * 2
def baseEnd_2159719 : Nat := 41073108357323734191857

theorem tailTrace_2159719 : CollatzResearch.WordTrace tailWord_2159719 prefixEnd_2159719 41073108357323734191857 := by
  unfold tailWord_2159719
  simp only [CollatzResearch.WordTrace]
  refine ⟨78771423262714388484610211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52514282175142925656406807 78771423262714388484610211)
  ·
    refine ⟨118157134894071582726915317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78771423262714388484610211 118157134894071582726915317)
    ·
      refine ⟨11077231396319210880648311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118157134894071582726915317 11077231396319210880648311)
      ·
        refine ⟨16615847094478816320972467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11077231396319210880648311 16615847094478816320972467)
        ·
          refine ⟨24923770641718224481458701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16615847094478816320972467 24923770641718224481458701)
          ·
            refine ⟨9346413990644334180547013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24923770641718224481458701 9346413990644334180547013)
            ·
              refine ⟨1752452623245812658852565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9346413990644334180547013 1752452623245812658852565)
              ·
                refine ⟨41073108357323734191857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1752452623245812658852565 41073108357323734191857)
                ·
                  rfl

theorem cell23_2159719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 7].length) (baseStart_2159719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159719 prefixEnd_2159719 := by exact prefixLift 2159719
  have htrace : WordTrace (prefixWord ++ tailWord_2159719) baseStart_2159719 baseEnd_2159719 := by
    simpa [prefixWord, tailWord_2159719, baseEnd_2159719] using wordTrace_append hprefix tailTrace_2159719
  have hstable : (prefixWord ++ tailWord_2159719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159719).length < 2 ^ (prefixWord ++ tailWord_2159719).sum := by decide
  have hdescent : baseEnd_2159719 < baseStart_2159719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159733 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2159733 : Nat := 118140960795 + 2159733 * 2 ^ 59
def prefixEnd_2159733 : Nat := 4983230072969 + 3 ^ 40 * 2159733 * 2
def baseEnd_2159733 : Nat := 1108981114376903768405075

theorem tailTrace_2159733 : CollatzResearch.WordTrace tailWord_2159733 prefixEnd_2159733 1108981114376903768405075 := by
  unfold tailWord_2159733
  simp only [CollatzResearch.WordTrace]
  refine ⟨78771933884663668875619853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52514622589775779250413235 78771933884663668875619853)
  ·
    refine ⟨29539475206748875828357445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78771933884663668875619853 29539475206748875828357445)
    ·
      refine ⟨5538651601265414217817021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29539475206748875828357445 5538651601265414217817021)
      ·
        refine ⟨2076994350474530331681383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5538651601265414217817021 2076994350474530331681383)
        ·
          refine ⟨3115491525711795497522075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076994350474530331681383 3115491525711795497522075)
          ·
            refine ⟨4673237288567693246283113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115491525711795497522075 4673237288567693246283113)
            ·
              refine ⟨3504927966425769934712335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4673237288567693246283113 3504927966425769934712335)
              ·
                refine ⟨5257391949638654902068503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504927966425769934712335 5257391949638654902068503)
                ·
                  refine ⟨7886087924457982353102755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5257391949638654902068503 7886087924457982353102755)
                  ·
                    refine ⟨11829131886686973529654133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7886087924457982353102755 11829131886686973529654133)
                    ·
                      refine ⟨1108981114376903768405075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11829131886686973529654133 1108981114376903768405075)
                      ·
                        rfl

theorem cell23_2159733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2159733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159733 prefixEnd_2159733 := by exact prefixLift 2159733
  have htrace : WordTrace (prefixWord ++ tailWord_2159733) baseStart_2159733 baseEnd_2159733 := by
    simpa [prefixWord, tailWord_2159733, baseEnd_2159733] using wordTrace_append hprefix tailTrace_2159733
  have hstable : (prefixWord ++ tailWord_2159733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159733).length < 2 ^ (prefixWord ++ tailWord_2159733).sum := by decide
  have hdescent : baseEnd_2159733 < baseStart_2159733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159763 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 2, 1, 3]
def baseStart_2159763 : Nat := 118140960795 + 2159763 * 2 ^ 59
def prefixEnd_2159763 : Nat := 4983230072969 + 3 ^ 40 * 2159763 * 2
def baseEnd_2159763 : Nat := 1108996518796538651029937

theorem tailTrace_2159763 : CollatzResearch.WordTrace tailWord_2159763 prefixEnd_2159763 1108996518796538651029937 := by
  unfold tailWord_2159763
  simp only [CollatzResearch.WordTrace]
  refine ⟨78773028074554983999211943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52515352049703322666141295 78773028074554983999211943)
  ·
    refine ⟨118159542111832475998817915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78773028074554983999211943 118159542111832475998817915)
    ·
      refine ⟨177239313167748713998226873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118159542111832475998817915 177239313167748713998226873)
      ·
        refine ⟨132929484875811535498670155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177239313167748713998226873 132929484875811535498670155)
        ·
          refine ⟨199394227313717303248005233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132929484875811535498670155 199394227313717303248005233)
          ·
            refine ⟨149545670485287977436003925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199394227313717303248005233 149545670485287977436003925)
            ·
              refine ⟨1752488325999468485578171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 149545670485287977436003925 1752488325999468485578171)
              ·
                refine ⟨2628732488999202728367257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752488325999468485578171 2628732488999202728367257)
                ·
                  refine ⟨1971549366749402046275443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628732488999202728367257 1971549366749402046275443)
                  ·
                    refine ⟨2957324050124103069413165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1971549366749402046275443 2957324050124103069413165)
                    ·
                      refine ⟨1108996518796538651029937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957324050124103069413165 1108996518796538651029937)
                      ·
                        rfl

theorem cell23_2159763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 2, 1, 3].length) (baseStart_2159763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159763 prefixEnd_2159763 := by exact prefixLift 2159763
  have htrace : WordTrace (prefixWord ++ tailWord_2159763) baseStart_2159763 baseEnd_2159763 := by
    simpa [prefixWord, tailWord_2159763, baseEnd_2159763] using wordTrace_append hprefix tailTrace_2159763
  have hstable : (prefixWord ++ tailWord_2159763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159763).length < 2 ^ (prefixWord ++ tailWord_2159763).sum := by decide
  have hdescent : baseEnd_2159763 < baseStart_2159763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159792 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 9]
def baseStart_2159792 : Nat := 118140960795 + 2159792 * 2 ^ 59
def prefixEnd_2159792 : Nat := 4983230072969 + 3 ^ 40 * 2159792 * 2
def baseEnd_2159792 : Nat := 123223489970613226396367

theorem tailTrace_2159792 : CollatzResearch.WordTrace tailWord_2159792 prefixEnd_2159792 123223489970613226396367 := by
  unfold tailWord_2159792
  simp only [CollatzResearch.WordTrace]
  refine ⟨39387042895724960976008815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52516057194299947968011753 39387042895724960976008815)
  ·
    refine ⟨59080564343587441464013223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39387042895724960976008815 59080564343587441464013223)
    ·
      refine ⟨88620846515381162196019835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59080564343587441464013223 88620846515381162196019835)
      ·
        refine ⟨132931269773071743294029753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88620846515381162196019835 132931269773071743294029753)
        ·
          refine ⟨99698452329803807470522315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132931269773071743294029753 99698452329803807470522315)
          ·
            refine ⟨149547678494705711205783473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99698452329803807470522315 149547678494705711205783473)
            ·
              refine ⟨112160758871029283404337605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149547678494705711205783473 112160758871029283404337605)
              ·
                refine ⟨21030142288317990638313301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112160758871029283404337605 21030142288317990638313301)
                ·
                  refine ⟨123223489970613226396367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21030142288317990638313301 123223489970613226396367)
                  ·
                    rfl

theorem cell23_2159792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_2159792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159792 prefixEnd_2159792 := by exact prefixLift 2159792
  have htrace : WordTrace (prefixWord ++ tailWord_2159792) baseStart_2159792 baseEnd_2159792 := by
    simpa [prefixWord, tailWord_2159792, baseEnd_2159792] using wordTrace_append hprefix tailTrace_2159792
  have hstable : (prefixWord ++ tailWord_2159792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159792).length < 2 ^ (prefixWord ++ tailWord_2159792).sum := by decide
  have hdescent : baseEnd_2159792 < baseStart_2159792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159798 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2159798 : Nat := 118140960795 + 2159798 * 2 ^ 59
def prefixEnd_2159798 : Nat := 4983230072969 + 3 ^ 40 * 2159798 * 2
def baseEnd_2159798 : Nat := 1109014490619446014092277

theorem tailTrace_2159798 : CollatzResearch.WordTrace tailWord_2159798 prefixEnd_2159798 1109014490619446014092277 := by
  unfold tailWord_2159798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4923394039339261561046003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52516203086285456651157365 4923394039339261561046003)
  ·
    refine ⟨7385091059008892341569005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4923394039339261561046003 7385091059008892341569005)
    ·
      refine ⟨2769409147128334628088377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7385091059008892341569005 2769409147128334628088377)
      ·
        refine ⟨2077056860346250971066283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2769409147128334628088377 2077056860346250971066283)
        ·
          refine ⟨3115585290519376456599425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077056860346250971066283 3115585290519376456599425)
          ·
            refine ⟨2336688967889532342449569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3115585290519376456599425 2336688967889532342449569)
            ·
              refine ⟨1752516725917149256837177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336688967889532342449569 1752516725917149256837177)
              ·
                refine ⟨1314387544437861942627883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752516725917149256837177 1314387544437861942627883)
                ·
                  refine ⟨1971581316656792913941825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314387544437861942627883 1971581316656792913941825)
                  ·
                    refine ⟨1478685987492594685456369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1971581316656792913941825 1478685987492594685456369)
                    ·
                      refine ⟨1109014490619446014092277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478685987492594685456369 1109014490619446014092277)
                      ·
                        rfl

theorem cell23_2159798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2159798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159798 prefixEnd_2159798 := by exact prefixLift 2159798
  have htrace : WordTrace (prefixWord ++ tailWord_2159798) baseStart_2159798 baseEnd_2159798 := by
    simpa [prefixWord, tailWord_2159798, baseEnd_2159798] using wordTrace_append hprefix tailTrace_2159798
  have hstable : (prefixWord ++ tailWord_2159798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159798).length < 2 ^ (prefixWord ++ tailWord_2159798).sum := by decide
  have hdescent : baseEnd_2159798 < baseStart_2159798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159799 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_2159799 : Nat := 118140960795 + 2159799 * 2 ^ 59
def prefixEnd_2159799 : Nat := 4983230072969 + 3 ^ 40 * 2159799 * 2
def baseEnd_2159799 : Nat := 1109015004100100510179771

theorem tailTrace_2159799 : CollatzResearch.WordTrace tailWord_2159799 prefixEnd_2159799 1109015004100100510179771 := by
  unfold tailWord_2159799
  simp only [CollatzResearch.WordTrace]
  refine ⟨78774341102424562147522451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52516227401616374765014967 78774341102424562147522451)
  ·
    refine ⟨118161511653636843221283677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78774341102424562147522451 118161511653636843221283677)
    ·
      refine ⟨44310566870113816207981379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118161511653636843221283677 44310566870113816207981379)
      ·
        refine ⟨66465850305170724311972069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44310566870113816207981379 66465850305170724311972069)
        ·
          refine ⟨12462346932219510808494763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66465850305170724311972069 12462346932219510808494763)
          ·
            refine ⟨18693520398329266212742145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12462346932219510808494763 18693520398329266212742145)
            ·
              refine ⟨14020140298746949659556609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18693520398329266212742145 14020140298746949659556609)
              ·
                refine ⟨10515105224060212244667457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14020140298746949659556609 10515105224060212244667457)
                ·
                  refine ⟨7886328918045159183500593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10515105224060212244667457 7886328918045159183500593)
                  ·
                    refine ⟨5914746688533869387625445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7886328918045159183500593 5914746688533869387625445)
                    ·
                      refine ⟨1109015004100100510179771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5914746688533869387625445 1109015004100100510179771)
                      ·
                        rfl

theorem cell23_2159799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_2159799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159799 prefixEnd_2159799 := by exact prefixLift 2159799
  have htrace : WordTrace (prefixWord ++ tailWord_2159799) baseStart_2159799 baseEnd_2159799 := by
    simpa [prefixWord, tailWord_2159799, baseEnd_2159799] using wordTrace_append hprefix tailTrace_2159799
  have hstable : (prefixWord ++ tailWord_2159799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159799).length < 2 ^ (prefixWord ++ tailWord_2159799).sum := by decide
  have hdescent : baseEnd_2159799 < baseStart_2159799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159806 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2159806 : Nat := 118140960795 + 2159806 * 2 ^ 59
def prefixEnd_2159806 : Nat := 4983230072969 + 3 ^ 40 * 2159806 * 2
def baseEnd_2159806 : Nat := 1109018598464681982792239

theorem tailTrace_2159806 : CollatzResearch.WordTrace tailWord_2159806 prefixEnd_2159806 1109018598464681982792239 := by
  unfold tailWord_2159806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846824551674900292878409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52516397608932801562018181 9846824551674900292878409)
  ·
    refine ⟨7385118413756175219658807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9846824551674900292878409 7385118413756175219658807)
    ·
      refine ⟨11077677620634262829488211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7385118413756175219658807 11077677620634262829488211)
      ·
        refine ⟨16616516430951394244232317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11077677620634262829488211 16616516430951394244232317)
        ·
          refine ⟨6231193661606772841587119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16616516430951394244232317 6231193661606772841587119)
          ·
            refine ⟨9346790492410159262380679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6231193661606772841587119 9346790492410159262380679)
            ·
              refine ⟨14020185738615238893571019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346790492410159262380679 14020185738615238893571019)
              ·
                refine ⟨21030278607922858340356529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14020185738615238893571019 21030278607922858340356529)
                ·
                  refine ⟨15772708955942143755267397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21030278607922858340356529 15772708955942143755267397)
                  ·
                    refine ⟨2957382929239151954112637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15772708955942143755267397 2957382929239151954112637)
                    ·
                      refine ⟨1109018598464681982792239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957382929239151954112637 1109018598464681982792239)
                      ·
                        rfl

theorem cell23_2159806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2159806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159806 prefixEnd_2159806 := by exact prefixLift 2159806
  have htrace : WordTrace (prefixWord ++ tailWord_2159806) baseStart_2159806 baseEnd_2159806 := by
    simpa [prefixWord, tailWord_2159806, baseEnd_2159806] using wordTrace_append hprefix tailTrace_2159806
  have hstable : (prefixWord ++ tailWord_2159806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159806).length < 2 ^ (prefixWord ++ tailWord_2159806).sum := by decide
  have hdescent : baseEnd_2159806 < baseStart_2159806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159876 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2159876 : Nat := 118140960795 + 2159876 * 2 ^ 59
def prefixEnd_2159876 : Nat := 4983230072969 + 3 ^ 40 * 2159876 * 2
def baseEnd_2159876 : Nat := 1109054542110496708916917

theorem tailTrace_2159876 : CollatzResearch.WordTrace tailWord_2159876 prefixEnd_2159876 1109054542110496708916917 := by
  unfold tailWord_2159876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39388574761572802149037741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52518099682097069532050321 39388574761572802149037741)
  ·
    refine ⟨14770715535589800805889153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39388574761572802149037741 14770715535589800805889153)
    ·
      refine ⟨11078036651692350604416865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14770715535589800805889153 11078036651692350604416865)
      ·
        refine ⟨8308527488769262953312649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11078036651692350604416865 8308527488769262953312649)
        ·
          refine ⟨6231395616576947214984487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8308527488769262953312649 6231395616576947214984487)
          ·
            refine ⟨9347093424865420822476731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6231395616576947214984487 9347093424865420822476731)
            ·
              refine ⟨14020640137298131233715097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9347093424865420822476731 14020640137298131233715097)
              ·
                refine ⟨10515480102973598425286323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14020640137298131233715097 10515480102973598425286323)
                ·
                  refine ⟨15773220154460397637929485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10515480102973598425286323 15773220154460397637929485)
                  ·
                    refine ⟨5914957557922649114223557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15773220154460397637929485 5914957557922649114223557)
                    ·
                      refine ⟨1109054542110496708916917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5914957557922649114223557 1109054542110496708916917)
                      ·
                        rfl

theorem cell23_2159876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2159876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159876 prefixEnd_2159876 := by exact prefixLift 2159876
  have htrace : WordTrace (prefixWord ++ tailWord_2159876) baseStart_2159876 baseEnd_2159876 := by
    simpa [prefixWord, tailWord_2159876, baseEnd_2159876] using wordTrace_append hprefix tailTrace_2159876
  have hstable : (prefixWord ++ tailWord_2159876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159876).length < 2 ^ (prefixWord ++ tailWord_2159876).sum := by decide
  have hdescent : baseEnd_2159876 < baseStart_2159876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159889 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_2159889 : Nat := 118140960795 + 2159889 * 2 ^ 59
def prefixEnd_2159889 : Nat := 4983230072969 + 3 ^ 40 * 2159889 * 2
def baseEnd_2159889 : Nat := 1109061217359005158054357

theorem tailTrace_2159889 : CollatzResearch.WordTrace tailWord_2159889 prefixEnd_2159889 1109061217359005158054357 := by
  unfold tailWord_2159889
  simp only [CollatzResearch.WordTrace]
  refine ⟨78777623672098507518298721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52518415781399005012199147 78777623672098507518298721)
  ·
    refine ⟨59083217754073880638724041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78777623672098507518298721 59083217754073880638724041)
    ·
      refine ⟨44312413315555410479043031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59083217754073880638724041 44312413315555410479043031)
      ·
        refine ⟨66468619973333115718564547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44312413315555410479043031 66468619973333115718564547)
        ·
          refine ⟨99702929959999673577846821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66468619973333115718564547 99702929959999673577846821)
          ·
            refine ⟨18694299367499938795846279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99702929959999673577846821 18694299367499938795846279)
            ·
              refine ⟨28041449051249908193769419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18694299367499938795846279 28041449051249908193769419)
              ·
                refine ⟨42062173576874862290654129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28041449051249908193769419 42062173576874862290654129)
                ·
                  refine ⟨31546630182656146717990597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42062173576874862290654129 31546630182656146717990597)
                  ·
                    refine ⟨5914993159248027509623237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31546630182656146717990597 5914993159248027509623237)
                    ·
                      refine ⟨1109061217359005158054357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5914993159248027509623237 1109061217359005158054357)
                      ·
                        rfl

theorem cell23_2159889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_2159889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159889 prefixEnd_2159889 := by exact prefixLift 2159889
  have htrace : WordTrace (prefixWord ++ tailWord_2159889) baseStart_2159889 baseEnd_2159889 := by
    simpa [prefixWord, tailWord_2159889, baseEnd_2159889] using wordTrace_append hprefix tailTrace_2159889
  have hstable : (prefixWord ++ tailWord_2159889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159889).length < 2 ^ (prefixWord ++ tailWord_2159889).sum := by decide
  have hdescent : baseEnd_2159889 < baseStart_2159889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159896 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2159896 : Nat := 118140960795 + 2159896 * 2 ^ 59
def prefixEnd_2159896 : Nat := 4983230072969 + 3 ^ 40 * 2159896 * 2
def baseEnd_2159896 : Nat := 1109064811723586630666825

theorem tailTrace_2159896 : CollatzResearch.WordTrace tailWord_2159896 prefixEnd_2159896 1109064811723586630666825 := by
  unfold tailWord_2159896
  simp only [CollatzResearch.WordTrace]
  refine ⟨39388939491536573856901771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52518585988715431809202361 39388939491536573856901771)
  ·
    refine ⟨59083409237304860785352657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39388939491536573856901771 59083409237304860785352657)
    ·
      refine ⟨44312556927978645589014493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59083409237304860785352657 44312556927978645589014493)
      ·
        refine ⟨16617208847991992095880435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44312556927978645589014493 16617208847991992095880435)
        ·
          refine ⟨24925813271987988143820653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16617208847991992095880435 24925813271987988143820653)
          ·
            refine ⟨9347179976995495553932745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24925813271987988143820653 9347179976995495553932745)
            ·
              refine ⟨7010384982746621665449559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9347179976995495553932745 7010384982746621665449559)
              ·
                refine ⟨10515577474119932498174339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7010384982746621665449559 10515577474119932498174339)
                ·
                  refine ⟨15773366211179898747261509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10515577474119932498174339 15773366211179898747261509)
                  ·
                    refine ⟨2957506164596231015111533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15773366211179898747261509 2957506164596231015111533)
                    ·
                      refine ⟨1109064811723586630666825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957506164596231015111533 1109064811723586630666825)
                      ·
                        rfl

theorem cell23_2159896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2159896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159896 prefixEnd_2159896 := by exact prefixLift 2159896
  have htrace : WordTrace (prefixWord ++ tailWord_2159896) baseStart_2159896 baseEnd_2159896 := by
    simpa [prefixWord, tailWord_2159896, baseEnd_2159896] using wordTrace_append hprefix tailTrace_2159896
  have hstable : (prefixWord ++ tailWord_2159896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159896).length < 2 ^ (prefixWord ++ tailWord_2159896).sum := by decide
  have hdescent : baseEnd_2159896 < baseStart_2159896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159920 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 1, 4]
def baseStart_2159920 : Nat := 118140960795 + 2159920 * 2 ^ 59
def prefixEnd_2159920 : Nat := 4983230072969 + 3 ^ 40 * 2159920 * 2
def baseEnd_2159920 : Nat := 369692378419764845588905

theorem tailTrace_2159920 : CollatzResearch.WordTrace tailWord_2159920 prefixEnd_2159920 369692378419764845588905 := by
  unfold tailWord_2159920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39389377167493099906338607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52519169556657466541784809 39389377167493099906338607)
  ·
    refine ⟨59084065751239649859507911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39389377167493099906338607 59084065751239649859507911)
    ·
      refine ⟨88626098626859474789261867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59084065751239649859507911 88626098626859474789261867)
      ·
        refine ⟨132939147940289212183892801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88626098626859474789261867 132939147940289212183892801)
        ·
          refine ⟨99704360955216909137919601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132939147940289212183892801 99704360955216909137919601)
          ·
            refine ⟨74778270716412681853439701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99704360955216909137919601 74778270716412681853439701)
            ·
              refine ⟨1752615719915922230939993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74778270716412681853439701 1752615719915922230939993)
              ·
                refine ⟨1314461789936941673204995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752615719915922230939993 1314461789936941673204995)
                ·
                  refine ⟨1971692684905412509807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314461789936941673204995 1971692684905412509807493)
                  ·
                    refine ⟨369692378419764845588905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971692684905412509807493 369692378419764845588905)
                    ·
                      rfl

theorem cell23_2159920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 4].length) (baseStart_2159920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159920 prefixEnd_2159920 := by exact prefixLift 2159920
  have htrace : WordTrace (prefixWord ++ tailWord_2159920) baseStart_2159920 baseEnd_2159920 := by
    simpa [prefixWord, tailWord_2159920, baseEnd_2159920] using wordTrace_append hprefix tailTrace_2159920
  have hstable : (prefixWord ++ tailWord_2159920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159920).length < 2 ^ (prefixWord ++ tailWord_2159920).sum := by decide
  have hdescent : baseEnd_2159920 < baseStart_2159920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159960 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 1, 1, 3]
def baseStart_2159960 : Nat := 118140960795 + 2159960 * 2 ^ 59
def prefixEnd_2159960 : Nat := 4983230072969 + 3 ^ 40 * 2159960 * 2
def baseEnd_2159960 : Nat := 1109097674485474380266531

theorem tailTrace_2159960 : CollatzResearch.WordTrace tailWord_2159960 prefixEnd_2159960 1109097674485474380266531 := by
  unfold tailWord_2159960
  simp only [CollatzResearch.WordTrace]
  refine ⟨39390106627420643322066667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52520142169894191096088889 39390106627420643322066667)
  ·
    refine ⟨59085159941130964983100001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39390106627420643322066667 59085159941130964983100001)
    ·
      refine ⟨44313869955848223737325001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59085159941130964983100001 44313869955848223737325001)
      ·
        refine ⟨33235402466886167802993751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44313869955848223737325001 33235402466886167802993751)
        ·
          refine ⟨49853103700329251704490627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33235402466886167802993751 49853103700329251704490627)
          ·
            refine ⟨74779655550493877556735941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49853103700329251704490627 74779655550493877556735941)
            ·
              refine ⟨14021185415717602041887989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74779655550493877556735941 14021185415717602041887989)
              ·
                refine ⟨1314486132723525191426999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14021185415717602041887989 1314486132723525191426999)
                ·
                  refine ⟨1971729199085287787140499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314486132723525191426999 1971729199085287787140499)
                  ·
                    refine ⟨2957593798627931680710749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1971729199085287787140499 2957593798627931680710749)
                    ·
                      refine ⟨1109097674485474380266531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957593798627931680710749 1109097674485474380266531)
                      ·
                        rfl

theorem cell23_2159960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_2159960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159960 prefixEnd_2159960 := by exact prefixLift 2159960
  have htrace : WordTrace (prefixWord ++ tailWord_2159960) baseStart_2159960 baseEnd_2159960 := by
    simpa [prefixWord, tailWord_2159960, baseEnd_2159960] using wordTrace_append hprefix tailTrace_2159960
  have hstable : (prefixWord ++ tailWord_2159960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159960).length < 2 ^ (prefixWord ++ tailWord_2159960).sum := by decide
  have hdescent : baseEnd_2159960 < baseStart_2159960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159970 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2159970 : Nat := 118140960795 + 2159970 * 2 ^ 59
def prefixEnd_2159970 : Nat := 4983230072969 + 3 ^ 40 * 2159970 * 2
def baseEnd_2159970 : Nat := 1109102809292019341141485

theorem tailTrace_2159970 : CollatzResearch.WordTrace tailWord_2159970 prefixEnd_2159970 1109102809292019341141485 := by
  unfold tailWord_2159970
  simp only [CollatzResearch.WordTrace]
  refine ⟨19695144496201264587999341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52520385323203372234664909 19695144496201264587999341)
  ·
    refine ⟨7385679186075474220499753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19695144496201264587999341 7385679186075474220499753)
    ·
      refine ⟨5539259389556605665374815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7385679186075474220499753 5539259389556605665374815)
      ·
        refine ⟨8308889084334908498062223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5539259389556605665374815 8308889084334908498062223)
        ·
          refine ⟨12463333626502362747093335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8308889084334908498062223 12463333626502362747093335)
          ·
            refine ⟨18695000439753544120640003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12463333626502362747093335 18695000439753544120640003)
            ·
              refine ⟨28042500659630316180960005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18695000439753544120640003 28042500659630316180960005)
              ·
                refine ⟨5257968873680684283930001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28042500659630316180960005 5257968873680684283930001)
                ·
                  refine ⟨3943476655260513212947501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257968873680684283930001 3943476655260513212947501)
                  ·
                    refine ⟨1478803745722692454855313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3943476655260513212947501 1478803745722692454855313)
                    ·
                      refine ⟨1109102809292019341141485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478803745722692454855313 1109102809292019341141485)
                      ·
                        rfl

theorem cell23_2159970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2159970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159970 prefixEnd_2159970 := by exact prefixLift 2159970
  have htrace : WordTrace (prefixWord ++ tailWord_2159970) baseStart_2159970 baseEnd_2159970 := by
    simpa [prefixWord, tailWord_2159970, baseEnd_2159970] using wordTrace_append hprefix tailTrace_2159970
  have hstable : (prefixWord ++ tailWord_2159970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159970).length < 2 ^ (prefixWord ++ tailWord_2159970).sum := by decide
  have hdescent : baseEnd_2159970 < baseStart_2159970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159986 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2159986 : Nat := 118140960795 + 2159986 * 2 ^ 59
def prefixEnd_2159986 : Nat := 4983230072969 + 3 ^ 40 * 2159986 * 2
def baseEnd_2159986 : Nat := 1109111024982491278541411

theorem tailTrace_2159986 : CollatzResearch.WordTrace tailWord_2159986 prefixEnd_2159986 1109111024982491278541411 := by
  unfold tailWord_2159986
  simp only [CollatzResearch.WordTrace]
  refine ⟨19695290388186773271144953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52520774368498062056386541 19695290388186773271144953)
  ·
    refine ⟨14771467791140079953358715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19695290388186773271144953 14771467791140079953358715)
    ·
      refine ⟨22157201686710119930038073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14771467791140079953358715 22157201686710119930038073)
      ·
        refine ⟨16617901265032589947528555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22157201686710119930038073 16617901265032589947528555)
        ·
          refine ⟨24926851897548884921292833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16617901265032589947528555 24926851897548884921292833)
          ·
            refine ⟨18695138923161663690969625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24926851897548884921292833 18695138923161663690969625)
            ·
              refine ⟨14021354192371247768227219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18695138923161663690969625 14021354192371247768227219)
              ·
                refine ⟨21032031288556871652340829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14021354192371247768227219 21032031288556871652340829)
                ·
                  refine ⟨7887011733208826869627811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21032031288556871652340829 7887011733208826869627811)
                  ·
                    refine ⟨11830517599813240304441717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7887011733208826869627811 11830517599813240304441717)
                    ·
                      refine ⟨1109111024982491278541411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11830517599813240304441717 1109111024982491278541411)
                      ·
                        rfl

theorem cell23_2159986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2159986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159986 prefixEnd_2159986 := by exact prefixLift 2159986
  have htrace : WordTrace (prefixWord ++ tailWord_2159986) baseStart_2159986 baseEnd_2159986 := by
    simpa [prefixWord, tailWord_2159986, baseEnd_2159986] using wordTrace_append hprefix tailTrace_2159986
  have hstable : (prefixWord ++ tailWord_2159986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159986).length < 2 ^ (prefixWord ++ tailWord_2159986).sum := by decide
  have hdescent : baseEnd_2159986 < baseStart_2159986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159993 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 2, 4]
def baseStart_2159993 : Nat := 118140960795 + 2159993 * 2 ^ 59
def prefixEnd_2159993 : Nat := 4983230072969 + 3 ^ 40 * 2159993 * 2
def baseEnd_2159993 : Nat := 369704873115690917051293

theorem tailTrace_2159993 : CollatzResearch.WordTrace tailWord_2159993 prefixEnd_2159993 369704873115690917051293 := by
  unfold tailWord_2159993
  simp only [CollatzResearch.WordTrace]
  refine ⟨78781416863721733280084633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52520944575814488853389755 78781416863721733280084633)
  ·
    refine ⟨59086062647791299960063475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78781416863721733280084633 59086062647791299960063475)
    ·
      refine ⟨88629093971686949940095213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59086062647791299960063475 88629093971686949940095213)
      ·
        refine ⟨33235910239382606227535705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88629093971686949940095213 33235910239382606227535705)
        ·
          refine ⟨24926932679536954670651779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33235910239382606227535705 24926932679536954670651779)
          ·
            refine ⟨37390399019305432005977669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24926932679536954670651779 37390399019305432005977669)
            ·
              refine ⟨7010699816119768501120813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37390399019305432005977669 7010699816119768501120813)
              ·
                refine ⟨2629012431044913187920305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7010699816119768501120813 2629012431044913187920305)
                ·
                  refine ⟨1971759323283684890940229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2629012431044913187920305 1971759323283684890940229)
                  ·
                    refine ⟨369704873115690917051293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971759323283684890940229 369704873115690917051293)
                    ·
                      rfl

theorem cell23_2159993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 4].length) (baseStart_2159993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2159993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2159993 prefixEnd_2159993 := by exact prefixLift 2159993
  have htrace : WordTrace (prefixWord ++ tailWord_2159993) baseStart_2159993 baseEnd_2159993 := by
    simpa [prefixWord, tailWord_2159993, baseEnd_2159993] using wordTrace_append hprefix tailTrace_2159993
  have hstable : (prefixWord ++ tailWord_2159993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159993).length < 2 ^ (prefixWord ++ tailWord_2159993).sum := by decide
  have hdescent : baseEnd_2159993 < baseStart_2159993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160003 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 3]
def baseStart_2160003 : Nat := 118140960795 + 2160003 * 2 ^ 59
def prefixEnd_2160003 : Nat := 4983230072969 + 3 ^ 40 * 2160003 * 2
def baseEnd_2160003 : Nat := 1109119754153617712028833

theorem tailTrace_2160003 : CollatzResearch.WordTrace tailWord_2160003 prefixEnd_2160003 1109119754153617712028833 := by
  unfold tailWord_2160003
  simp only [CollatzResearch.WordTrace]
  refine ⟨78781781593685504987948663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52521187729123669991965775 78781781593685504987948663)
  ·
    refine ⟨118172672390528257481922995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78781781593685504987948663 118172672390528257481922995)
    ·
      refine ⟨177259008585792386222884493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118172672390528257481922995 177259008585792386222884493)
      ·
        refine ⟨66472128219672144833581685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177259008585792386222884493 66472128219672144833581685)
        ·
          refine ⟨6231762020594263578148283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66472128219672144833581685 6231762020594263578148283)
          ·
            refine ⟨9347643030891395367222425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6231762020594263578148283 9347643030891395367222425)
            ·
              refine ⟨7010732273168546525416819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9347643030891395367222425 7010732273168546525416819)
              ·
                refine ⟨10516098409752819788125229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7010732273168546525416819 10516098409752819788125229)
                ·
                  refine ⟨3943536903657307420546961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10516098409752819788125229 3943536903657307420546961)
                  ·
                    refine ⟨2957652677742980565410221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3943536903657307420546961 2957652677742980565410221)
                    ·
                      refine ⟨1109119754153617712028833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2957652677742980565410221 1109119754153617712028833)
                      ·
                        rfl

theorem cell23_2160003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_2160003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160003 prefixEnd_2160003 := by exact prefixLift 2160003
  have htrace : WordTrace (prefixWord ++ tailWord_2160003) baseStart_2160003 baseEnd_2160003 := by
    simpa [prefixWord, tailWord_2160003, baseEnd_2160003] using wordTrace_append hprefix tailTrace_2160003
  have hstable : (prefixWord ++ tailWord_2160003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160003).length < 2 ^ (prefixWord ++ tailWord_2160003).sum := by decide
  have hdescent : baseEnd_2160003 < baseStart_2160003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160014 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_2160014 : Nat := 118140960795 + 2160014 * 2 ^ 59
def prefixEnd_2160014 : Nat := 4983230072969 + 3 ^ 40 * 2160014 * 2
def baseEnd_2160014 : Nat := 369708467480272389663761

theorem tailTrace_2160014 : CollatzResearch.WordTrace tailWord_2160014 prefixEnd_2160014 369708467480272389663761 := by
  unfold tailWord_2160014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9847772849580706733324887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52521455197763769244399397 9847772849580706733324887)
  ·
    refine ⟨14771659274371060099987331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9847772849580706733324887 14771659274371060099987331)
    ·
      refine ⟨22157488911556590149980997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14771659274371060099987331 22157488911556590149980997)
      ·
        refine ⟨4154529170916860653121437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22157488911556590149980997 4154529170916860653121437)
        ·
          refine ⟨1557948439093822744920539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4154529170916860653121437 1557948439093822744920539)
          ·
            refine ⟨2336922658640734117380809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557948439093822744920539 2336922658640734117380809)
            ·
              refine ⟨1752691993980550588035607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336922658640734117380809 1752691993980550588035607)
              ·
                refine ⟨2629037990970825882053411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752691993980550588035607 2629037990970825882053411)
                ·
                  refine ⟨3943556986456238823080117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629037990970825882053411 3943556986456238823080117)
                  ·
                    refine ⟨369708467480272389663761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3943556986456238823080117 369708467480272389663761)
                    ·
                      rfl

theorem cell23_2160014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_2160014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160014 prefixEnd_2160014 := by exact prefixLift 2160014
  have htrace : WordTrace (prefixWord ++ tailWord_2160014) baseStart_2160014 baseEnd_2160014 := by
    simpa [prefixWord, tailWord_2160014, baseEnd_2160014] using wordTrace_append hprefix tailTrace_2160014
  have hstable : (prefixWord ++ tailWord_2160014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160014).length < 2 ^ (prefixWord ++ tailWord_2160014).sum := by decide
  have hdescent : baseEnd_2160014 < baseStart_2160014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160034 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_2160034 : Nat := 118140960795 + 2160034 * 2 ^ 59
def prefixEnd_2160034 : Nat := 4983230072969 + 3 ^ 40 * 2160034 * 2
def baseEnd_2160034 : Nat := 1109135672053907090741191

theorem tailTrace_2160034 : CollatzResearch.WordTrace tailWord_2160034 prefixEnd_2160034 1109135672053907090741191 := by
  unfold tailWord_2160034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19695728064143299320581789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52521941504382131521551437 19695728064143299320581789)
  ·
    refine ⟨7385898024053737245218171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19695728064143299320581789 7385898024053737245218171)
    ·
      refine ⟨11078847036080605867827257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7385898024053737245218171 11078847036080605867827257)
      ·
        refine ⟨8309135277060454400870443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11078847036080605867827257 8309135277060454400870443)
        ·
          refine ⟨12463702915590681601305665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309135277060454400870443 12463702915590681601305665)
          ·
            refine ⟨9347777186693011200979249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12463702915590681601305665 9347777186693011200979249)
            ·
              refine ⟨7010832890019758400734437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9347777186693011200979249 7010832890019758400734437)
              ·
                refine ⟨1314531166878704700137707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7010832890019758400734437 1314531166878704700137707)
                ·
                  refine ⟨1971796750318057050206561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314531166878704700137707 1971796750318057050206561)
                  ·
                    refine ⟨1478847562738542787654921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1971796750318057050206561 1478847562738542787654921)
                    ·
                      refine ⟨1109135672053907090741191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478847562738542787654921 1109135672053907090741191)
                      ·
                        rfl

theorem cell23_2160034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_2160034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160034 prefixEnd_2160034 := by exact prefixLift 2160034
  have htrace : WordTrace (prefixWord ++ tailWord_2160034) baseStart_2160034 baseEnd_2160034 := by
    simpa [prefixWord, tailWord_2160034, baseEnd_2160034] using wordTrace_append hprefix tailTrace_2160034
  have hstable : (prefixWord ++ tailWord_2160034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160034).length < 2 ^ (prefixWord ++ tailWord_2160034).sum := by decide
  have hdescent : baseEnd_2160034 < baseStart_2160034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160056 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2160056 : Nat := 118140960795 + 2160056 * 2 ^ 59
def prefixEnd_2160056 : Nat := 4983230072969 + 3 ^ 40 * 2160056 * 2
def baseEnd_2160056 : Nat := 1109146968628306004666089

theorem tailTrace_2160056 : CollatzResearch.WordTrace tailWord_2160056 prefixEnd_2160056 1109146968628306004666089 := by
  unfold tailWord_2160056
  simp only [CollatzResearch.WordTrace]
  refine ⟨39391857331246747519814011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52522476441662330026418681 39391857331246747519814011)
  ·
    refine ⟨59087785996870121279721017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39391857331246747519814011 59087785996870121279721017)
    ·
      refine ⟨44315839497652590959790763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59087785996870121279721017 44315839497652590959790763)
      ·
        refine ⟨66473759246478886439686145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44315839497652590959790763 66473759246478886439686145)
        ·
          refine ⟨49855319434859164829764609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66473759246478886439686145 49855319434859164829764609)
          ·
            refine ⟨37391489576144373622323457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49855319434859164829764609 37391489576144373622323457)
            ·
              refine ⟨28043617182108280216742593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37391489576144373622323457 28043617182108280216742593)
              ·
                refine ⟨21032712886581210162556945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28043617182108280216742593 21032712886581210162556945)
                ·
                  refine ⟨15774534664935907621917709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21032712886581210162556945 15774534664935907621917709)
                  ·
                    refine ⟨5915450499350965358219141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15774534664935907621917709 5915450499350965358219141)
                    ·
                      refine ⟨1109146968628306004666089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5915450499350965358219141 1109146968628306004666089)
                      ·
                        rfl

theorem cell23_2160056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2160056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160056 prefixEnd_2160056 := by exact prefixLift 2160056
  have htrace : WordTrace (prefixWord ++ tailWord_2160056) baseStart_2160056 baseEnd_2160056 := by
    simpa [prefixWord, tailWord_2160056, baseEnd_2160056] using wordTrace_append hprefix tailTrace_2160056
  have hstable : (prefixWord ++ tailWord_2160056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160056).length < 2 ^ (prefixWord ++ tailWord_2160056).sum := by decide
  have hdescent : baseEnd_2160056 < baseStart_2160056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160073 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 3, 4, 2]
def baseStart_2160073 : Nat := 118140960795 + 2160073 * 2 ^ 59
def prefixEnd_2160073 : Nat := 4983230072969 + 3 ^ 40 * 2160073 * 2
def baseEnd_2160073 : Nat := 1109155697799432438153511

theorem tailTrace_2160073 : CollatzResearch.WordTrace tailWord_2160073 prefixEnd_2160073 1109155697799432438153511 := by
  unfold tailWord_2160073
  simp only [CollatzResearch.WordTrace]
  refine ⟨78784334703431906942996873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52522889802287937961997915 78784334703431906942996873)
  ·
    refine ⟨59088251027573930207247655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78784334703431906942996873 59088251027573930207247655)
    ·
      refine ⟨88632376541360895310871483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59088251027573930207247655 88632376541360895310871483)
      ·
        refine ⟨132948564812041342966307225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88632376541360895310871483 132948564812041342966307225)
        ·
          refine ⟨99711423609031007224730419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132948564812041342966307225 99711423609031007224730419)
          ·
            refine ⟨149567135413546510837095629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99711423609031007224730419 149567135413546510837095629)
            ·
              refine ⟨56087675780079941563910861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149567135413546510837095629 56087675780079941563910861)
              ·
                refine ⟨21032878417529978086466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56087675780079941563910861 21032878417529978086466573)
                ·
                  refine ⟨7887329406573741782424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21032878417529978086466573 7887329406573741782424965)
                  ·
                    refine ⟨1478874263732576584204681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7887329406573741782424965 1478874263732576584204681)
                    ·
                      refine ⟨1109155697799432438153511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478874263732576584204681 1109155697799432438153511)
                      ·
                        rfl

theorem cell23_2160073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 4, 2].length) (baseStart_2160073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160073 prefixEnd_2160073 := by exact prefixLift 2160073
  have htrace : WordTrace (prefixWord ++ tailWord_2160073) baseStart_2160073 baseEnd_2160073 := by
    simpa [prefixWord, tailWord_2160073, baseEnd_2160073] using wordTrace_append hprefix tailTrace_2160073
  have hstable : (prefixWord ++ tailWord_2160073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160073).length < 2 ^ (prefixWord ++ tailWord_2160073).sum := by decide
  have hdescent : baseEnd_2160073 < baseStart_2160073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160096 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 7]
def baseStart_2160096 : Nat := 118140960795 + 2160096 * 2 ^ 59
def prefixEnd_2160096 : Nat := 4983230072969 + 3 ^ 40 * 2160096 * 2
def baseEnd_2160096 : Nat := 123240834206053983129545

theorem tailTrace_2160096 : CollatzResearch.WordTrace tailWord_2160096 prefixEnd_2160096 123240834206053983129545 := by
  unfold tailWord_2160096
  simp only [CollatzResearch.WordTrace]
  refine ⟨39392586791174290935542071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52523449054899054580722761 39392586791174290935542071)
  ·
    refine ⟨59088880186761436403313107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39392586791174290935542071 59088880186761436403313107)
    ·
      refine ⟨88633320280142154604969661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59088880186761436403313107 88633320280142154604969661)
      ·
        refine ⟨33237495105053307976863623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88633320280142154604969661 33237495105053307976863623)
        ·
          refine ⟨49856242657579961965295435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33237495105053307976863623 49856242657579961965295435)
          ·
            refine ⟨74784363986369942947943153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49856242657579961965295435 74784363986369942947943153)
            ·
              refine ⟨56088272989777457210957365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74784363986369942947943153 56088272989777457210957365)
              ·
                refine ⟨5258275592791636613527253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56088272989777457210957365 5258275592791636613527253)
                ·
                  refine ⟨123240834206053983129545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5258275592791636613527253 123240834206053983129545)
                  ·
                    rfl

theorem cell23_2160096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_2160096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160096 prefixEnd_2160096 := by exact prefixLift 2160096
  have htrace : WordTrace (prefixWord ++ tailWord_2160096) baseStart_2160096 baseEnd_2160096 := by
    simpa [prefixWord, tailWord_2160096, baseEnd_2160096] using wordTrace_append hprefix tailTrace_2160096
  have hstable : (prefixWord ++ tailWord_2160096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160096).length < 2 ^ (prefixWord ++ tailWord_2160096).sum := by decide
  have hdescent : baseEnd_2160096 < baseStart_2160096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160147 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 5]
def baseStart_2160147 : Nat := 118140960795 + 2160147 * 2 ^ 59
def prefixEnd_2160147 : Nat := 4983230072969 + 3 ^ 40 * 2160147 * 2
def baseEnd_2160147 : Nat := 123243743929762794292019

theorem tailTrace_2160147 : CollatzResearch.WordTrace tailWord_2160147 prefixEnd_2160147 123243743929762794292019 := by
  unfold tailWord_2160147
  simp only [CollatzResearch.WordTrace]
  refine ⟨78787033705163817581190695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52524689136775878387460463 78787033705163817581190695)
  ·
    refine ⟨118180550557745726371786043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78787033705163817581190695 118180550557745726371786043)
    ·
      refine ⟨177270825836618589557679065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118180550557745726371786043 177270825836618589557679065)
      ·
        refine ⟨132953119377463942168259299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177270825836618589557679065 132953119377463942168259299)
        ·
          refine ⟨199429679066195913252388949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132953119377463942168259299 199429679066195913252388949)
          ·
            refine ⟨2337066551556983358426433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 199429679066195913252388949 2337066551556983358426433)
            ·
              refine ⟨1752799913667737518819825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337066551556983358426433 1752799913667737518819825)
              ·
                refine ⟨1314599935250803139114869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752799913667737518819825 1314599935250803139114869)
                ·
                  refine ⟨123243743929762794292019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1314599935250803139114869 123243743929762794292019)
                  ·
                    rfl

theorem cell23_2160147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 5].length) (baseStart_2160147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160147 prefixEnd_2160147 := by exact prefixLift 2160147
  have htrace : WordTrace (prefixWord ++ tailWord_2160147) baseStart_2160147 baseEnd_2160147 := by
    simpa [prefixWord, tailWord_2160147, baseEnd_2160147] using wordTrace_append hprefix tailTrace_2160147
  have hstable : (prefixWord ++ tailWord_2160147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160147).length < 2 ^ (prefixWord ++ tailWord_2160147).sum := by decide
  have hdescent : baseEnd_2160147 < baseStart_2160147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160158 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2160158 : Nat := 118140960795 + 2160158 * 2 ^ 59
def prefixEnd_2160158 : Nat := 4983230072969 + 3 ^ 40 * 2160158 * 2
def baseEnd_2160158 : Nat := 1109199343655064605590621

theorem tailTrace_2160158 : CollatzResearch.WordTrace tailWord_2160158 prefixEnd_2160158 1109199343655064605590621 := by
  unfold tailWord_2160158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9848429363515495807480141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52524956605415977639894085 9848429363515495807480141)
  ·
    refine ⟨3693161011318310927805053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9848429363515495807480141 3693161011318310927805053)
    ·
      refine ⟨1384935379244366597926895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3693161011318310927805053 1384935379244366597926895)
      ·
        refine ⟨2077403068866549896890343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384935379244366597926895 2077403068866549896890343)
        ·
          refine ⟨3116104603299824845335515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077403068866549896890343 3116104603299824845335515)
          ·
            refine ⟨4674156904949737268003273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116104603299824845335515 4674156904949737268003273)
            ·
              refine ⟨3505617678712302951002455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674156904949737268003273 3505617678712302951002455)
              ·
                refine ⟨5258426518068454426503683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3505617678712302951002455 5258426518068454426503683)
                ·
                  refine ⟨7887639777102681639755525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5258426518068454426503683 7887639777102681639755525)
                  ·
                    refine ⟨1478932458206752807454161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7887639777102681639755525 1478932458206752807454161)
                    ·
                      refine ⟨1109199343655064605590621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1478932458206752807454161 1109199343655064605590621)
                      ·
                        rfl

theorem cell23_2160158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2160158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160158 prefixEnd_2160158 := by exact prefixLift 2160158
  have htrace : WordTrace (prefixWord ++ tailWord_2160158) baseStart_2160158 baseEnd_2160158 := by
    simpa [prefixWord, tailWord_2160158, baseEnd_2160158] using wordTrace_append hprefix tailTrace_2160158
  have hstable : (prefixWord ++ tailWord_2160158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160158).length < 2 ^ (prefixWord ++ tailWord_2160158).sum := by decide
  have hdescent : baseEnd_2160158 < baseStart_2160158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160193 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2160193 : Nat := 118140960795 + 2160193 * 2 ^ 59
def prefixEnd_2160193 : Nat := 4983230072969 + 3 ^ 40 * 2160193 * 2
def baseEnd_2160193 : Nat := 1109217315477971968652959

theorem tailTrace_2160193 : CollatzResearch.WordTrace tailWord_2160193 prefixEnd_2160193 1109217315477971968652959 := by
  unfold tailWord_2160193
  simp only [CollatzResearch.WordTrace]
  refine ⟨78788711462997167437365233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52525807641998111624910155 78788711462997167437365233)
  ·
    refine ⟨59091533597247875578023925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78788711462997167437365233 59091533597247875578023925)
    ·
      refine ⟨5539831274741988335439743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59091533597247875578023925 5539831274741988335439743)
      ·
        refine ⟨8309746912112982503159615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5539831274741988335439743 8309746912112982503159615)
        ·
          refine ⟨12464620368169473754739423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309746912112982503159615 12464620368169473754739423)
          ·
            refine ⟨18696930552254210632109135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12464620368169473754739423 18696930552254210632109135)
            ·
              refine ⟨28045395828381315948163703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18696930552254210632109135 28045395828381315948163703)
              ·
                refine ⟨42068093742571973922245555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28045395828381315948163703 42068093742571973922245555)
                ·
                  refine ⟨63102140613857960883368333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42068093742571973922245555 63102140613857960883368333)
                  ·
                    refine ⟨23663302730196735331263125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63102140613857960883368333 23663302730196735331263125)
                    ·
                      refine ⟨1109217315477971968652959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23663302730196735331263125 1109217315477971968652959)
                      ·
                        rfl

theorem cell23_2160193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2160193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160193 prefixEnd_2160193 := by exact prefixLift 2160193
  have htrace : WordTrace (prefixWord ++ tailWord_2160193) baseStart_2160193 baseEnd_2160193 := by
    simpa [prefixWord, tailWord_2160193, baseEnd_2160193] using wordTrace_append hprefix tailTrace_2160193
  have hstable : (prefixWord ++ tailWord_2160193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160193).length < 2 ^ (prefixWord ++ tailWord_2160193).sum := by decide
  have hdescent : baseEnd_2160193 < baseStart_2160193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160233 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_2160233 : Nat := 118140960795 + 2160233 * 2 ^ 59
def prefixEnd_2160233 : Nat := 4983230072969 + 3 ^ 40 * 2160233 * 2
def baseEnd_2160233 : Nat := 369745951568050604050925

theorem tailTrace_2160233 : CollatzResearch.WordTrace tailWord_2160233 prefixEnd_2160233 369745951568050604050925 := by
  unfold tailWord_2160233
  simp only [CollatzResearch.WordTrace]
  refine ⟨78790170382852254268821353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52526780255234836179214235 78790170382852254268821353)
  ·
    refine ⟨59092627787139190701616015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78790170382852254268821353 59092627787139190701616015)
    ·
      refine ⟨88638941680708786052424023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59092627787139190701616015 88638941680708786052424023)
      ·
        refine ⟨132958412521063179078636035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88638941680708786052424023 132958412521063179078636035)
        ·
          refine ⟨199437618781594768617954053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132958412521063179078636035 199437618781594768617954053)
          ·
            refine ⟨37394553521549019115866385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199437618781594768617954053 37394553521549019115866385)
            ·
              refine ⟨28045915141161764336899789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37394553521549019115866385 28045915141161764336899789)
              ·
                refine ⟨10517218177935661626337421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28045915141161764336899789 10517218177935661626337421)
                ·
                  refine ⟨3943956816725873109876533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10517218177935661626337421 3943956816725873109876533)
                  ·
                    refine ⟨369745951568050604050925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3943956816725873109876533 369745951568050604050925)
                    ·
                      rfl

theorem cell23_2160233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_2160233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160233 prefixEnd_2160233 := by exact prefixLift 2160233
  have htrace : WordTrace (prefixWord ++ tailWord_2160233) baseStart_2160233 baseEnd_2160233 := by
    simpa [prefixWord, tailWord_2160233, baseEnd_2160233] using wordTrace_append hprefix tailTrace_2160233
  have hstable : (prefixWord ++ tailWord_2160233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160233).length < 2 ^ (prefixWord ++ tailWord_2160233).sum := by decide
  have hdescent : baseEnd_2160233 < baseStart_2160233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160257 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_2160257 : Nat := 118140960795 + 2160257 * 2 ^ 59
def prefixEnd_2160257 : Nat := 4983230072969 + 3 ^ 40 * 2160257 * 2
def baseEnd_2160257 : Nat := 1109250178239859718252665

theorem tailTrace_2160257 : CollatzResearch.WordTrace tailWord_2160257 prefixEnd_2160257 1109250178239859718252665 := by
  unfold tailWord_2160257
  simp only [CollatzResearch.WordTrace]
  refine ⟨78791045734765306367695025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52527363823176870911796683 78791045734765306367695025)
  ·
    refine ⟨59093284301073979775771269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78791045734765306367695025 59093284301073979775771269)
    ·
      refine ⟨11079990806451371207957113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59093284301073979775771269 11079990806451371207957113)
      ·
        refine ⟨8309993104838528405967835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11079990806451371207957113 8309993104838528405967835)
        ·
          refine ⟨12464989657257792608951753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309993104838528405967835 12464989657257792608951753)
          ·
            refine ⟨9348742242943344456713815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12464989657257792608951753 9348742242943344456713815)
            ·
              refine ⟨14023113364415016685070723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9348742242943344456713815 14023113364415016685070723)
              ·
                refine ⟨21034670046622525027606085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14023113364415016685070723 21034670046622525027606085)
                ·
                  refine ⟨3944000633741723442676141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21034670046622525027606085 3944000633741723442676141)
                  ·
                    refine ⟨1479000237653146291003553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3944000633741723442676141 1479000237653146291003553)
                    ·
                      refine ⟨1109250178239859718252665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479000237653146291003553 1109250178239859718252665)
                      ·
                        rfl

theorem cell23_2160257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_2160257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160257 prefixEnd_2160257 := by exact prefixLift 2160257
  have htrace : WordTrace (prefixWord ++ tailWord_2160257) baseStart_2160257 baseEnd_2160257 := by
    simpa [prefixWord, tailWord_2160257, baseEnd_2160257] using wordTrace_append hprefix tailTrace_2160257
  have hstable : (prefixWord ++ tailWord_2160257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160257).length < 2 ^ (prefixWord ++ tailWord_2160257).sum := by decide
  have hdescent : baseEnd_2160257 < baseStart_2160257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160273 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_2160273 : Nat := 118140960795 + 2160273 * 2 ^ 59
def prefixEnd_2160273 : Nat := 4983230072969 + 3 ^ 40 * 2160273 * 2
def baseEnd_2160273 : Nat := 1109258393930331655652591

theorem tailTrace_2160273 : CollatzResearch.WordTrace tailWord_2160273 prefixEnd_2160273 1109258393930331655652591 := by
  unfold tailWord_2160273
  simp only [CollatzResearch.WordTrace]
  refine ⟨78791629302707341100277473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52527752868471560733518315 78791629302707341100277473)
  ·
    refine ⟨59093721977030505825208105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78791629302707341100277473 59093721977030505825208105)
    ·
      refine ⟨44320291482772879368906079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59093721977030505825208105 44320291482772879368906079)
      ·
        refine ⟨66480437224159319053359119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44320291482772879368906079 66480437224159319053359119)
        ·
          refine ⟨99720655836238978580038679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66480437224159319053359119 99720655836238978580038679)
          ·
            refine ⟨149580983754358467870058019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99720655836238978580038679 149580983754358467870058019)
            ·
              refine ⟨224371475631537701805087029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149580983754358467870058019 224371475631537701805087029)
              ·
                refine ⟨21034825840456659544226909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224371475631537701805087029 21034825840456659544226909)
                ·
                  refine ⟨7888059690171247329085091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21034825840456659544226909 7888059690171247329085091)
                  ·
                    refine ⟨11832089535256870993627637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7888059690171247329085091 11832089535256870993627637)
                    ·
                      refine ⟨1109258393930331655652591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11832089535256870993627637 1109258393930331655652591)
                      ·
                        rfl

theorem cell23_2160273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_2160273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160273 prefixEnd_2160273 := by exact prefixLift 2160273
  have htrace : WordTrace (prefixWord ++ tailWord_2160273) baseStart_2160273 baseEnd_2160273 := by
    simpa [prefixWord, tailWord_2160273, baseEnd_2160273] using wordTrace_append hprefix tailTrace_2160273
  have hstable : (prefixWord ++ tailWord_2160273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160273).length < 2 ^ (prefixWord ++ tailWord_2160273).sum := by decide
  have hdescent : baseEnd_2160273 < baseStart_2160273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160284 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_2160284 : Nat := 118140960795 + 2160284 * 2 ^ 59
def prefixEnd_2160284 : Nat := 4983230072969 + 3 ^ 40 * 2160284 * 2
def baseEnd_2160284 : Nat := 369754680739177037538347

theorem tailTrace_2160284 : CollatzResearch.WordTrace tailWord_2160284 prefixEnd_2160284 369754680739177037538347 := by
  unfold tailWord_2160284
  simp only [CollatzResearch.WordTrace]
  refine ⟨39396015252833744989463953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52528020337111659985951937 39396015252833744989463953)
  ·
    refine ⟨29547011439625308742097965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39396015252833744989463953 29547011439625308742097965)
    ·
      refine ⟨11080129289859490778286737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29547011439625308742097965 11080129289859490778286737)
      ·
        refine ⟨8310096967394618083715053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11080129289859490778286737 8310096967394618083715053)
        ·
          refine ⟨3116286362772981781393145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8310096967394618083715053 3116286362772981781393145)
          ·
            refine ⟨2337214772079736336044859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116286362772981781393145 2337214772079736336044859)
            ·
              refine ⟨3505822158119604504067289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337214772079736336044859 3505822158119604504067289)
              ·
                refine ⟨2629366618589703378050467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3505822158119604504067289 2629366618589703378050467)
                ·
                  refine ⟨3944049927884555067075701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629366618589703378050467 3944049927884555067075701)
                  ·
                    refine ⟨369754680739177037538347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3944049927884555067075701 369754680739177037538347)
                    ·
                      rfl

theorem cell23_2160284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_2160284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160284 prefixEnd_2160284 := by exact prefixLift 2160284
  have htrace : WordTrace (prefixWord ++ tailWord_2160284) baseStart_2160284 baseEnd_2160284 := by
    simpa [prefixWord, tailWord_2160284, baseEnd_2160284] using wordTrace_append hprefix tailTrace_2160284
  have hstable : (prefixWord ++ tailWord_2160284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160284).length < 2 ^ (prefixWord ++ tailWord_2160284).sum := by decide
  have hdescent : baseEnd_2160284 < baseStart_2160284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160293 : List Nat := [1, 3, 1, 2, 1, 2, 4, 9]
def baseStart_2160293 : Nat := 118140960795 + 2160293 * 2 ^ 59
def prefixEnd_2160293 : Nat := 4983230072969 + 3 ^ 40 * 2160293 * 2
def baseEnd_2160293 : Nat := 41084024575682280644537

theorem tailTrace_2160293 : CollatzResearch.WordTrace tailWord_2160293 prefixEnd_2160293 41084024575682280644537 := by
  unfold tailWord_2160293
  simp only [CollatzResearch.WordTrace]
  refine ⟨78792358762634884516005533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52528239175089923010670355 78792358762634884516005533)
  ·
    refine ⟨29547134535988081693502075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78792358762634884516005533 29547134535988081693502075)
    ·
      refine ⟨44320701803982122540253113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29547134535988081693502075 44320701803982122540253113)
      ·
        refine ⟨33240526352986591905189835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44320701803982122540253113 33240526352986591905189835)
        ·
          refine ⟨49860789529479887857784753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33240526352986591905189835 49860789529479887857784753)
          ·
            refine ⟨37395592147109915893338565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49860789529479887857784753 37395592147109915893338565)
            ·
              refine ⟨7011673527583109230000981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37395592147109915893338565 7011673527583109230000981)
              ·
                refine ⟨41084024575682280644537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7011673527583109230000981 41084024575682280644537)
                ·
                  rfl

theorem cell23_2160293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 9].length) (baseStart_2160293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160293 prefixEnd_2160293 := by exact prefixLift 2160293
  have htrace : WordTrace (prefixWord ++ tailWord_2160293) baseStart_2160293 baseEnd_2160293 := by
    simpa [prefixWord, tailWord_2160293, baseEnd_2160293] using wordTrace_append hprefix tailTrace_2160293
  have hstable : (prefixWord ++ tailWord_2160293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160293).length < 2 ^ (prefixWord ++ tailWord_2160293).sum := by decide
  have hdescent : baseEnd_2160293 < baseStart_2160293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160320 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_2160320 : Nat := 118140960795 + 2160320 * 2 ^ 59
def prefixEnd_2160320 : Nat := 4983230072969 + 3 ^ 40 * 2160320 * 2
def baseEnd_2160320 : Nat := 1109282527521092971764875

theorem tailTrace_2160320 : CollatzResearch.WordTrace tailWord_2160320 prefixEnd_2160320 1109282527521092971764875 := by
  unfold tailWord_2160320
  simp only [CollatzResearch.WordTrace]
  refine ⟨39396671766768534063619207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52528895689024712084825609 39396671766768534063619207)
  ·
    refine ⟨59095007650152801095428811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39396671766768534063619207 59095007650152801095428811)
    ·
      refine ⟨88642511475229201643143217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59095007650152801095428811 88642511475229201643143217)
      ·
        refine ⟨66481883606421901232357413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88642511475229201643143217 66481883606421901232357413)
        ·
          refine ⟨12465353176204106481067015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66481883606421901232357413 12465353176204106481067015)
          ·
            refine ⟨18698029764306159721600523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12465353176204106481067015 18698029764306159721600523)
            ·
              refine ⟨28047044646459239582400785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18698029764306159721600523 28047044646459239582400785)
              ·
                refine ⟨21035283484844429686800589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28047044646459239582400785 21035283484844429686800589)
                ·
                  refine ⟨7888231306816661132550221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21035283484844429686800589 7888231306816661132550221)
                  ·
                    refine ⟨2958086740056247924706333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7888231306816661132550221 2958086740056247924706333)
                    ·
                      refine ⟨1109282527521092971764875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2958086740056247924706333 1109282527521092971764875)
                      ·
                        rfl

theorem cell23_2160320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_2160320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160320 prefixEnd_2160320 := by exact prefixLift 2160320
  have htrace : WordTrace (prefixWord ++ tailWord_2160320) baseStart_2160320 baseEnd_2160320 := by
    simpa [prefixWord, tailWord_2160320, baseEnd_2160320] using wordTrace_append hprefix tailTrace_2160320
  have hstable : (prefixWord ++ tailWord_2160320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160320).length < 2 ^ (prefixWord ++ tailWord_2160320).sum := by decide
  have hdescent : baseEnd_2160320 < baseStart_2160320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160337 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_2160337 : Nat := 118140960795 + 2160337 * 2 ^ 59
def prefixEnd_2160337 : Nat := 4983230072969 + 3 ^ 40 * 2160337 * 2
def baseEnd_2160337 : Nat := 1109291256692219405252297

theorem tailTrace_2160337 : CollatzResearch.WordTrace tailWord_2160337 prefixEnd_2160337 1109291256692219405252297 := by
  unfold tailWord_2160337
  simp only [CollatzResearch.WordTrace]
  refine ⟨78793963574475480030607265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52529309049650320020404843 78793963574475480030607265)
  ·
    refine ⟨59095472680856610022955449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78793963574475480030607265 59095472680856610022955449)
    ·
      refine ⟨44321604510642457517216587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59095472680856610022955449 44321604510642457517216587)
      ·
        refine ⟨66482406765963686275824881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44321604510642457517216587 66482406765963686275824881)
        ·
          refine ⟨49861805074472764706868661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66482406765963686275824881 49861805074472764706868661)
          ·
            refine ⟨4674544225731821691268937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49861805074472764706868661 4674544225731821691268937)
            ·
              refine ⟨3505908169298866268451703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4674544225731821691268937 3505908169298866268451703)
              ·
                refine ⟨5258862253948299402677555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3505908169298866268451703 5258862253948299402677555)
                ·
                  refine ⟨7888293380922449104016333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5258862253948299402677555 7888293380922449104016333)
                  ·
                    refine ⟨2958110017845918414006125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7888293380922449104016333 2958110017845918414006125)
                    ·
                      refine ⟨1109291256692219405252297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2958110017845918414006125 1109291256692219405252297)
                      ·
                        rfl

theorem cell23_2160337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_2160337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160337 prefixEnd_2160337 := by exact prefixLift 2160337
  have htrace : WordTrace (prefixWord ++ tailWord_2160337) baseStart_2160337 baseEnd_2160337 := by
    simpa [prefixWord, tailWord_2160337, baseEnd_2160337] using wordTrace_append hprefix tailTrace_2160337
  have hstable : (prefixWord ++ tailWord_2160337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160337).length < 2 ^ (prefixWord ++ tailWord_2160337).sum := by decide
  have hdescent : baseEnd_2160337 < baseStart_2160337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160370 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_2160370 : Nat := 118140960795 + 2160370 * 2 ^ 59
def prefixEnd_2160370 : Nat := 4983230072969 + 3 ^ 40 * 2160370 * 2
def baseEnd_2160370 : Nat := 369769400517939258713215

theorem tailTrace_2160370 : CollatzResearch.WordTrace tailWord_2160370 prefixEnd_2160370 369769400517939258713215 := by
  unfold tailWord_2160370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19698791795838981666639641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52530111455570617777705709 19698791795838981666639641)
  ·
    refine ⟨14774093846879236249979731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19698791795838981666639641 14774093846879236249979731)
    ·
      refine ⟨22161140770318854374969597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14774093846879236249979731 22161140770318854374969597)
      ·
        refine ⟨8310427788869570390613599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22161140770318854374969597 8310427788869570390613599)
        ·
          refine ⟨12465641683304355585920399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8310427788869570390613599 12465641683304355585920399)
          ·
            refine ⟨18698462524956533378880599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12465641683304355585920399 18698462524956533378880599)
            ·
              refine ⟨28047693787434800068320899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18698462524956533378880599 28047693787434800068320899)
              ·
                refine ⟨42071540681152200102481349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28047693787434800068320899 42071540681152200102481349)
                ·
                  refine ⟨7888413877716037519215253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42071540681152200102481349 7888413877716037519215253)
                  ·
                    refine ⟨369769400517939258713215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7888413877716037519215253 369769400517939258713215)
                    ·
                      rfl

theorem cell23_2160370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_2160370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160370 prefixEnd_2160370 := by exact prefixLift 2160370
  have htrace : WordTrace (prefixWord ++ tailWord_2160370) baseStart_2160370 baseEnd_2160370 := by
    simpa [prefixWord, tailWord_2160370, baseEnd_2160370] using wordTrace_append hprefix tailTrace_2160370
  have hstable : (prefixWord ++ tailWord_2160370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160370).length < 2 ^ (prefixWord ++ tailWord_2160370).sum := by decide
  have hdescent : baseEnd_2160370 < baseStart_2160370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160394 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_2160394 : Nat := 118140960795 + 2160394 * 2 ^ 59
def prefixEnd_2160394 : Nat := 4983230072969 + 3 ^ 40 * 2160394 * 2
def baseEnd_2160394 : Nat := 1109320525089525682239535

theorem tailTrace_2160394 : CollatzResearch.WordTrace tailWord_2160394 prefixEnd_2160394 1109320525089525682239535 := by
  unfold tailWord_2160394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19699010633817244691358059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52530695023512652510288157 19699010633817244691358059)
  ·
    refine ⟨29548515950725867037037089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19699010633817244691358059 29548515950725867037037089)
    ·
      refine ⟨22161386963044400277777817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29548515950725867037037089 22161386963044400277777817)
      ·
        refine ⟨16621040222283300208333363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22161386963044400277777817 16621040222283300208333363)
        ·
          refine ⟨24931560333424950312500045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16621040222283300208333363 24931560333424950312500045)
          ·
            refine ⟨9349335125034356367187517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24931560333424950312500045 9349335125034356367187517)
            ·
              refine ⟨3506000671887883637695319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9349335125034356367187517 3506000671887883637695319)
              ·
                refine ⟨5259001007831825456542979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3506000671887883637695319 5259001007831825456542979)
                ·
                  refine ⟨7888501511747738184814469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5259001007831825456542979 7888501511747738184814469)
                  ·
                    refine ⟨1479094033452700909652713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7888501511747738184814469 1479094033452700909652713)
                    ·
                      refine ⟨1109320525089525682239535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479094033452700909652713 1109320525089525682239535)
                      ·
                        rfl

theorem cell23_2160394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_2160394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160394 prefixEnd_2160394 := by exact prefixLift 2160394
  have htrace : WordTrace (prefixWord ++ tailWord_2160394) baseStart_2160394 baseEnd_2160394 := by
    simpa [prefixWord, tailWord_2160394, baseEnd_2160394] using wordTrace_append hprefix tailTrace_2160394
  have hstable : (prefixWord ++ tailWord_2160394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160394).length < 2 ^ (prefixWord ++ tailWord_2160394).sum := by decide
  have hdescent : baseEnd_2160394 < baseStart_2160394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160440 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2160440 : Nat := 118140960795 + 2160440 * 2 ^ 59
def prefixEnd_2160440 : Nat := 4983230072969 + 3 ^ 40 * 2160440 * 2
def baseEnd_2160440 : Nat := 1109344145199632502264323

theorem tailTrace_2160440 : CollatzResearch.WordTrace tailWord_2160440 prefixEnd_2160440 1109344145199632502264323 := by
  unfold tailWord_2160440
  simp only [CollatzResearch.WordTrace]
  refine ⟨39398860146551164310803387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52531813528734885747737849 39398860146551164310803387)
  ·
    refine ⟨59098290219826746466205081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39398860146551164310803387 59098290219826746466205081)
    ·
      refine ⟨44323717664870059849653811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59098290219826746466205081 44323717664870059849653811)
      ·
        refine ⟨66485576497305089774480717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44323717664870059849653811 66485576497305089774480717)
        ·
          refine ⟨24932091186489408665430269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66485576497305089774480717 24932091186489408665430269)
          ·
            refine ⟨9349534194933528249536351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24932091186489408665430269 9349534194933528249536351)
            ·
              refine ⟨14024301292400292374304527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9349534194933528249536351 14024301292400292374304527)
              ·
                refine ⟨21036451938600438561456791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14024301292400292374304527 21036451938600438561456791)
                ·
                  refine ⟨31554677907900657842185187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21036451938600438561456791 31554677907900657842185187)
                  ·
                    refine ⟨47332016861850986763277781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31554677907900657842185187 47332016861850986763277781)
                    ·
                      refine ⟨1109344145199632502264323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47332016861850986763277781 1109344145199632502264323)
                      ·
                        rfl

theorem cell23_2160440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2160440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160440 prefixEnd_2160440 := by exact prefixLift 2160440
  have htrace : WordTrace (prefixWord ++ tailWord_2160440) baseStart_2160440 baseEnd_2160440 := by
    simpa [prefixWord, tailWord_2160440, baseEnd_2160440] using wordTrace_append hprefix tailTrace_2160440
  have hstable : (prefixWord ++ tailWord_2160440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160440).length < 2 ^ (prefixWord ++ tailWord_2160440).sum := by decide
  have hdescent : baseEnd_2160440 < baseStart_2160440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160445 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2160445 : Nat := 118140960795 + 2160445 * 2 ^ 59
def prefixEnd_2160445 : Nat := 4983230072969 + 3 ^ 40 * 2160445 * 2
def baseEnd_2160445 : Nat := 1109346712602904982701801

theorem tailTrace_2160445 : CollatzResearch.WordTrace tailWord_2160445 prefixEnd_2160445 1109346712602904982701801 := by
  unfold tailWord_2160445
  simp only [CollatzResearch.WordTrace]
  refine ⟨78797902658084214475538789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52531935105389476317025859 78797902658084214475538789)
  ·
    refine ⟨14774606748390790214163523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78797902658084214475538789 14774606748390790214163523)
    ·
      refine ⟨22161910122586185321245285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14774606748390790214163523 22161910122586185321245285)
      ·
        refine ⟨4155358147984909747733491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22161910122586185321245285 4155358147984909747733491)
        ·
          refine ⟨6233037221977364621600237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4155358147984909747733491 6233037221977364621600237)
          ·
            refine ⟨2337388958241511733100089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6233037221977364621600237 2337388958241511733100089)
            ·
              refine ⟨1753041718681133799825067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337388958241511733100089 1753041718681133799825067)
              ·
                refine ⟨2629562578021700699737601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753041718681133799825067 2629562578021700699737601)
                ·
                  refine ⟨1972171933516275524803201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2629562578021700699737601 1972171933516275524803201)
                  ·
                    refine ⟨1479128950137206643602401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972171933516275524803201 1479128950137206643602401)
                    ·
                      refine ⟨1109346712602904982701801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479128950137206643602401 1109346712602904982701801)
                      ·
                        rfl

theorem cell23_2160445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2160445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160445 prefixEnd_2160445 := by exact prefixLift 2160445
  have htrace : WordTrace (prefixWord ++ tailWord_2160445) baseStart_2160445 baseEnd_2160445 := by
    simpa [prefixWord, tailWord_2160445, baseEnd_2160445] using wordTrace_append hprefix tailTrace_2160445
  have hstable : (prefixWord ++ tailWord_2160445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160445).length < 2 ^ (prefixWord ++ tailWord_2160445).sum := by decide
  have hdescent : baseEnd_2160445 < baseStart_2160445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160467 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 6, 4, 2]
def baseStart_2160467 : Nat := 118140960795 + 2160467 * 2 ^ 59
def prefixEnd_2160467 : Nat := 4983230072969 + 3 ^ 40 * 2160467 * 2
def baseEnd_2160467 : Nat := 1109358009177303896626699

theorem tailTrace_2160467 : CollatzResearch.WordTrace tailWord_2160467 prefixEnd_2160467 1109358009177303896626699 := by
  unfold tailWord_2160467
  simp only [CollatzResearch.WordTrace]
  refine ⟨78798705064004512232839655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52532470042669674821893103 78798705064004512232839655)
  ·
    refine ⟨118198057596006768349259483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78798705064004512232839655 118198057596006768349259483)
    ·
      refine ⟨177297086394010152523889225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118198057596006768349259483 177297086394010152523889225)
      ·
        refine ⟨132972814795507614392916919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177297086394010152523889225 132972814795507614392916919)
        ·
          refine ⟨199459222193261421589375379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132972814795507614392916919 199459222193261421589375379)
          ·
            refine ⟨299188833289892132384063069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199459222193261421589375379 299188833289892132384063069)
            ·
              refine ⟨112195812483709549644023651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299188833289892132384063069 112195812483709549644023651)
              ·
                refine ⟨168293718725564324466035477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112195812483709549644023651 168293718725564324466035477)
                ·
                  refine ⟨7888768065260827709345413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 168293718725564324466035477 7888768065260827709345413)
                  ·
                    refine ⟨1479144012236405195502265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7888768065260827709345413 1479144012236405195502265)
                    ·
                      refine ⟨1109358009177303896626699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479144012236405195502265 1109358009177303896626699)
                      ·
                        rfl

theorem cell23_2160467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4, 2].length) (baseStart_2160467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160467 prefixEnd_2160467 := by exact prefixLift 2160467
  have htrace : WordTrace (prefixWord ++ tailWord_2160467) baseStart_2160467 baseEnd_2160467 := by
    simpa [prefixWord, tailWord_2160467, baseEnd_2160467] using wordTrace_append hprefix tailTrace_2160467
  have hstable : (prefixWord ++ tailWord_2160467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160467).length < 2 ^ (prefixWord ++ tailWord_2160467).sum := by decide
  have hdescent : baseEnd_2160467 < baseStart_2160467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160544 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 4, 3, 2]
def baseStart_2160544 : Nat := 118140960795 + 2160544 * 2 ^ 59
def prefixEnd_2160544 : Nat := 4983230072969 + 3 ^ 40 * 2160544 * 2
def baseEnd_2160544 : Nat := 1109397547187700095363845

theorem tailTrace_2160544 : CollatzResearch.WordTrace tailWord_2160544 prefixEnd_2160544 1109397547187700095363845 := by
  unfold tailWord_2160544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39400756742362777191696343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52534342323150369588928457 39400756742362777191696343)
  ·
    refine ⟨59101135113544165787544515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39400756742362777191696343 59101135113544165787544515)
    ·
      refine ⟨88651702670316248681316773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59101135113544165787544515 88651702670316248681316773)
      ·
        refine ⟨16622194250684296627746895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88651702670316248681316773 16622194250684296627746895)
        ·
          refine ⟨24933291376026444941620343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16622194250684296627746895 24933291376026444941620343)
          ·
            refine ⟨37399937064039667412430515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24933291376026444941620343 37399937064039667412430515)
            ·
              refine ⟨56099905596059501118645773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37399937064039667412430515 56099905596059501118645773)
              ·
                refine ⟨21037464598522312919492165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56099905596059501118645773 21037464598522312919492165)
                ·
                  refine ⟨3944524612222933672404781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21037464598522312919492165 3944524612222933672404781)
                  ·
                    refine ⟨1479196729583600127151793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3944524612222933672404781 1479196729583600127151793)
                    ·
                      refine ⟨1109397547187700095363845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479196729583600127151793 1109397547187700095363845)
                      ·
                        rfl

theorem cell23_2160544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_2160544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160544 prefixEnd_2160544 := by exact prefixLift 2160544
  have htrace : WordTrace (prefixWord ++ tailWord_2160544) baseStart_2160544 baseEnd_2160544 := by
    simpa [prefixWord, tailWord_2160544, baseEnd_2160544] using wordTrace_append hprefix tailTrace_2160544
  have hstable : (prefixWord ++ tailWord_2160544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160544).length < 2 ^ (prefixWord ++ tailWord_2160544).sum := by decide
  have hdescent : baseEnd_2160544 < baseStart_2160544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160551 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2160551 : Nat := 118140960795 + 2160551 * 2 ^ 59
def prefixEnd_2160551 : Nat := 4983230072969 + 3 ^ 40 * 2160551 * 2
def baseEnd_2160551 : Nat := 1109401141552281567976313

theorem tailTrace_2160551 : CollatzResearch.WordTrace tailWord_2160551 prefixEnd_2160551 1109401141552281567976313 := by
  unfold tailWord_2160551
  simp only [CollatzResearch.WordTrace]
  refine ⟨78801768795700194578897507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52534512530466796385931671 78801768795700194578897507)
  ·
    refine ⟨118202653193550291868346261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78801768795700194578897507 118202653193550291868346261)
    ·
      refine ⟨5540749368447669931328731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118202653193550291868346261 5540749368447669931328731)
      ·
        refine ⟨8311124052671504896993097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5540749368447669931328731 8311124052671504896993097)
        ·
          refine ⟨6233343039503628672744823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8311124052671504896993097 6233343039503628672744823)
          ·
            refine ⟨9350014559255443009117235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6233343039503628672744823 9350014559255443009117235)
            ·
              refine ⟨14025021838883164513675853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9350014559255443009117235 14025021838883164513675853)
              ·
                refine ⟨5259383189581186692628445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14025021838883164513675853 5259383189581186692628445)
                ·
                  refine ⟨1972268696092945009735667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5259383189581186692628445 1972268696092945009735667)
                  ·
                    refine ⟨2958403044139417514603501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972268696092945009735667 2958403044139417514603501)
                    ·
                      refine ⟨1109401141552281567976313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2958403044139417514603501 1109401141552281567976313)
                      ·
                        rfl

theorem cell23_2160551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2160551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160551 prefixEnd_2160551 := by exact prefixLift 2160551
  have htrace : WordTrace (prefixWord ++ tailWord_2160551) baseStart_2160551 baseEnd_2160551 := by
    simpa [prefixWord, tailWord_2160551, baseEnd_2160551] using wordTrace_append hprefix tailTrace_2160551
  have hstable : (prefixWord ++ tailWord_2160551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160551).length < 2 ^ (prefixWord ++ tailWord_2160551).sum := by decide
  have hdescent : baseEnd_2160551 < baseStart_2160551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160584 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 4, 4]
def baseStart_2160584 : Nat := 118140960795 + 2160584 * 2 ^ 59
def prefixEnd_2160584 : Nat := 4983230072969 + 3 ^ 40 * 2160584 * 2
def baseEnd_2160584 : Nat := 369806028804626646287887

theorem tailTrace_2160584 : CollatzResearch.WordTrace tailWord_2160584 prefixEnd_2160584 369806028804626646287887 := by
  unfold tailWord_2160584
  simp only [CollatzResearch.WordTrace]
  refine ⟨39401486202290320607424403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52535314936387094143232537 39401486202290320607424403)
  ·
    refine ⟨59102229303435480911136605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39401486202290320607424403 59102229303435480911136605)
    ·
      refine ⟨22163335988788305341676227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59102229303435480911136605 22163335988788305341676227)
      ·
        refine ⟨33245003983182458012514341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22163335988788305341676227 33245003983182458012514341)
        ·
          refine ⟨6233438246846710877346439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33245003983182458012514341 6233438246846710877346439)
          ·
            refine ⟨9350157370270066316019659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6233438246846710877346439 9350157370270066316019659)
            ·
              refine ⟨14025236055405099474029489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9350157370270066316019659 14025236055405099474029489)
              ·
                refine ⟨10518927041553824605522117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14025236055405099474029489 10518927041553824605522117)
                ·
                  refine ⟨1972298820291342113535397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10518927041553824605522117 1972298820291342113535397)
                  ·
                    refine ⟨369806028804626646287887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1972298820291342113535397 369806028804626646287887)
                    ·
                      rfl

theorem cell23_2160584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_2160584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160584 prefixEnd_2160584 := by exact prefixLift 2160584
  have htrace : WordTrace (prefixWord ++ tailWord_2160584) baseStart_2160584 baseEnd_2160584 := by
    simpa [prefixWord, tailWord_2160584, baseEnd_2160584] using wordTrace_append hprefix tailTrace_2160584
  have hstable : (prefixWord ++ tailWord_2160584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160584).length < 2 ^ (prefixWord ++ tailWord_2160584).sum := by decide
  have hdescent : baseEnd_2160584 < baseStart_2160584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160587 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4]
def baseStart_2160587 : Nat := 118140960795 + 2160587 * 2 ^ 59
def prefixEnd_2160587 : Nat := 4983230072969 + 3 ^ 40 * 2160587 * 2
def baseEnd_2160587 : Nat := 1109419626855843427126147

theorem tailTrace_2160587 : CollatzResearch.WordTrace tailWord_2160587 prefixEnd_2160587 1109419626855843427126147 := by
  unfold tailWord_2160587
  simp only [CollatzResearch.WordTrace]
  refine ⟨78803081823569772727208015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52535387882379848484805343 78803081823569772727208015)
  ·
    refine ⟨118204622735354659090812023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78803081823569772727208015 118204622735354659090812023)
    ·
      refine ⟨177306934103031988636218035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118204622735354659090812023 177306934103031988636218035)
      ·
        refine ⟨265960401154547982954327053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177306934103031988636218035 265960401154547982954327053)
        ·
          refine ⟨99735150432955493607872645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265960401154547982954327053 99735150432955493607872645)
          ·
            refine ⟨18700340706179155051476121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99735150432955493607872645 18700340706179155051476121)
            ·
              refine ⟨14025255529634366288607091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18700340706179155051476121 14025255529634366288607091)
              ·
                refine ⟨21037883294451549432910637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14025255529634366288607091 21037883294451549432910637)
                ·
                  refine ⟨7889206235419331037341489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21037883294451549432910637 7889206235419331037341489)
                  ·
                    refine ⟨5916904676564498278006117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7889206235419331037341489 5916904676564498278006117)
                    ·
                      refine ⟨1109419626855843427126147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5916904676564498278006117 1109419626855843427126147)
                      ·
                        rfl

theorem cell23_2160587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_2160587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160587 prefixEnd_2160587 := by exact prefixLift 2160587
  have htrace : WordTrace (prefixWord ++ tailWord_2160587) baseStart_2160587 baseEnd_2160587 := by
    simpa [prefixWord, tailWord_2160587, baseEnd_2160587] using wordTrace_append hprefix tailTrace_2160587
  have hstable : (prefixWord ++ tailWord_2160587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160587).length < 2 ^ (prefixWord ++ tailWord_2160587).sum := by decide
  have hdescent : baseEnd_2160587 < baseStart_2160587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160597 : List Nat := [1, 3, 2, 3, 2, 1, 11]
def baseStart_2160597 : Nat := 118140960795 + 2160597 * 2 ^ 59
def prefixEnd_2160597 : Nat := 4983230072969 + 3 ^ 40 * 2160597 * 2
def baseEnd_2160597 : Nat := 13696601995831955407421

theorem tailTrace_2160597 : CollatzResearch.WordTrace tailWord_2160597 prefixEnd_2160597 13696601995831955407421 := by
  unfold tailWord_2160597
  simp only [CollatzResearch.WordTrace]
  refine ⟨78803446553533544435072045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52535631035689029623381363 78803446553533544435072045)
  ·
    refine ⟨29551292457575079163152017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78803446553533544435072045 29551292457575079163152017)
    ·
      refine ⟨22163469343181309372364013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29551292457575079163152017 22163469343181309372364013)
      ·
        refine ⟨8311301003692991014636505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22163469343181309372364013 8311301003692991014636505)
        ·
          refine ⟨6233475752769743260977379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8311301003692991014636505 6233475752769743260977379)
          ·
            refine ⟨9350213629154614891466069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6233475752769743260977379 9350213629154614891466069)
            ·
              refine ⟨13696601995831955407421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9350213629154614891466069 13696601995831955407421)
              ·
                rfl

theorem cell23_2160597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 11].length) (baseStart_2160597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160597 prefixEnd_2160597 := by exact prefixLift 2160597
  have htrace : WordTrace (prefixWord ++ tailWord_2160597) baseStart_2160597 baseEnd_2160597 := by
    simpa [prefixWord, tailWord_2160597, baseEnd_2160597] using wordTrace_append hprefix tailTrace_2160597
  have hstable : (prefixWord ++ tailWord_2160597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160597).length < 2 ^ (prefixWord ++ tailWord_2160597).sum := by decide
  have hdescent : baseEnd_2160597 < baseStart_2160597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160608 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 1, 2, 2]
def baseStart_2160608 : Nat := 118140960795 + 2160608 * 2 ^ 59
def prefixEnd_2160608 : Nat := 4983230072969 + 3 ^ 40 * 2160608 * 2
def baseEnd_2160608 : Nat := 1109430409949587844963551

theorem tailTrace_2160608 : CollatzResearch.WordTrace tailWord_2160608 prefixEnd_2160608 1109430409949587844963551 := by
  unfold tailWord_2160608
  simp only [CollatzResearch.WordTrace]
  refine ⟨39401923878246846656861239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52535898504329128875814985 39401923878246846656861239)
  ·
    refine ⟨59102885817370269985291859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39401923878246846656861239 59102885817370269985291859)
    ·
      refine ⟨88654328726055404977937789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59102885817370269985291859 88654328726055404977937789)
      ·
        refine ⟨33245373272270776866726671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88654328726055404977937789 33245373272270776866726671)
        ·
          refine ⟨49868059908406165300090007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33245373272270776866726671 49868059908406165300090007)
          ·
            refine ⟨74802089862609247950135011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49868059908406165300090007 74802089862609247950135011)
            ·
              refine ⟨112203134793913871925202517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74802089862609247950135011 112203134793913871925202517)
              ·
                refine ⟨1314880485866178186623467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 112203134793913871925202517 1314880485866178186623467)
                ·
                  refine ⟨1972320728799267279935201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314880485866178186623467 1972320728799267279935201)
                  ·
                    refine ⟨1479240546599450459951401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972320728799267279935201 1479240546599450459951401)
                    ·
                      refine ⟨1109430409949587844963551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479240546599450459951401 1109430409949587844963551)
                      ·
                        rfl

theorem cell23_2160608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_2160608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160608 prefixEnd_2160608 := by exact prefixLift 2160608
  have htrace : WordTrace (prefixWord ++ tailWord_2160608) baseStart_2160608 baseEnd_2160608 := by
    simpa [prefixWord, tailWord_2160608, baseEnd_2160608] using wordTrace_append hprefix tailTrace_2160608
  have hstable : (prefixWord ++ tailWord_2160608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160608).length < 2 ^ (prefixWord ++ tailWord_2160608).sum := by decide
  have hdescent : baseEnd_2160608 < baseStart_2160608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160637 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2160637 : Nat := 118140960795 + 2160637 * 2 ^ 59
def prefixEnd_2160637 : Nat := 4983230072969 + 3 ^ 40 * 2160637 * 2
def baseEnd_2160637 : Nat := 1109445300888568231500917

theorem tailTrace_2160637 : CollatzResearch.WordTrace tailWord_2160637 prefixEnd_2160637 1109445300888568231500917 := by
  unfold tailWord_2160637
  simp only [CollatzResearch.WordTrace]
  refine ⟨78804905473388631266528165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52536603648925754177685443 78804905473388631266528165)
  ·
    refine ⟨14775919776260368362474031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78804905473388631266528165 14775919776260368362474031)
    ·
      refine ⟨22163879664390552543711047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14775919776260368362474031 22163879664390552543711047)
      ·
        refine ⟨33245819496585828815566571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22163879664390552543711047 33245819496585828815566571)
        ·
          refine ⟨49868729244878743223349857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33245819496585828815566571 49868729244878743223349857)
          ·
            refine ⟨37401546933659057417512393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49868729244878743223349857 37401546933659057417512393)
            ·
              refine ⟨28051160200244293063134295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37401546933659057417512393 28051160200244293063134295)
              ·
                refine ⟨42076740300366439594701443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28051160200244293063134295 42076740300366439594701443)
                ·
                  refine ⟨63115110450549659392052165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42076740300366439594701443 63115110450549659392052165)
                  ·
                    refine ⟨11834083209478061136009781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63115110450549659392052165 11834083209478061136009781)
                    ·
                      refine ⟨1109445300888568231500917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11834083209478061136009781 1109445300888568231500917)
                      ·
                        rfl

theorem cell23_2160637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2160637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160637 prefixEnd_2160637 := by exact prefixLift 2160637
  have htrace : WordTrace (prefixWord ++ tailWord_2160637) baseStart_2160637 baseEnd_2160637 := by
    simpa [prefixWord, tailWord_2160637, baseEnd_2160637] using wordTrace_append hprefix tailTrace_2160637
  have hstable : (prefixWord ++ tailWord_2160637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160637).length < 2 ^ (prefixWord ++ tailWord_2160637).sum := by decide
  have hdescent : baseEnd_2160637 < baseStart_2160637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160653 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2160653 : Nat := 118140960795 + 2160653 * 2 ^ 59
def prefixEnd_2160653 : Nat := 4983230072969 + 3 ^ 40 * 2160653 * 2
def baseEnd_2160653 : Nat := 1109453516579040168900845

theorem tailTrace_2160653 : CollatzResearch.WordTrace tailWord_2160653 prefixEnd_2160653 1109453516579040168900845 := by
  unfold tailWord_2160653
  simp only [CollatzResearch.WordTrace]
  refine ⟨78805489041330665999110613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52536992694220443999407075 78805489041330665999110613)
  ·
    refine ⟨1847003649406187484354155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 78805489041330665999110613 1847003649406187484354155)
    ·
      refine ⟨2770505474109281226531233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1847003649406187484354155 2770505474109281226531233)
      ·
        refine ⟨2077879105581960919898425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770505474109281226531233 2077879105581960919898425)
        ·
          refine ⟨1558409329186470689923819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2077879105581960919898425 1558409329186470689923819)
          ·
            refine ⟨2337613993779706034885729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558409329186470689923819 2337613993779706034885729)
            ·
              refine ⟨1753210495334779526164297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337613993779706034885729 1753210495334779526164297)
              ·
                refine ⟨1314907871501084644623223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753210495334779526164297 1314907871501084644623223)
                ·
                  refine ⟨1972361807251626966934835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314907871501084644623223 1972361807251626966934835)
                  ·
                    refine ⟨2958542710877440450402253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972361807251626966934835 2958542710877440450402253)
                    ·
                      refine ⟨1109453516579040168900845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2958542710877440450402253 1109453516579040168900845)
                      ·
                        rfl

theorem cell23_2160653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2160653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160653 prefixEnd_2160653 := by exact prefixLift 2160653
  have htrace : WordTrace (prefixWord ++ tailWord_2160653) baseStart_2160653 baseEnd_2160653 := by
    simpa [prefixWord, tailWord_2160653, baseEnd_2160653] using wordTrace_append hprefix tailTrace_2160653
  have hstable : (prefixWord ++ tailWord_2160653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160653).length < 2 ^ (prefixWord ++ tailWord_2160653).sum := by decide
  have hdescent : baseEnd_2160653 < baseStart_2160653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160667 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5]
def baseStart_2160667 : Nat := 118140960795 + 2160667 * 2 ^ 59
def prefixEnd_2160667 : Nat := 4983230072969 + 3 ^ 40 * 2160667 * 2
def baseEnd_2160667 : Nat := 1109460705308203114125779

theorem tailTrace_2160667 : CollatzResearch.WordTrace tailWord_2160667 prefixEnd_2160667 1109460705308203114125779 := by
  unfold tailWord_2160667
  simp only [CollatzResearch.WordTrace]
  refine ⟨78805999663279946390120255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52537333108853297593413503 78805999663279946390120255)
  ·
    refine ⟨118208999494919919585180383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78805999663279946390120255 118208999494919919585180383)
    ·
      refine ⟨177313499242379879377770575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118208999494919919585180383 177313499242379879377770575)
      ·
        refine ⟨265970248863569819066655863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177313499242379879377770575 265970248863569819066655863)
        ·
          refine ⟨398955373295354728599983795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265970248863569819066655863 398955373295354728599983795)
          ·
            refine ⟨598433059943032092899975693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398955373295354728599983795 598433059943032092899975693)
            ·
              refine ⟨224412397478637034837490885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 598433059943032092899975693 224412397478637034837490885)
              ·
                refine ⟨42077324527244444032029541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224412397478637034837490885 42077324527244444032029541)
                ·
                  refine ⟨7889498348858333256005539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42077324527244444032029541 7889498348858333256005539)
                  ·
                    refine ⟨11834247523287499884008309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7889498348858333256005539 11834247523287499884008309)
                    ·
                      refine ⟨1109460705308203114125779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11834247523287499884008309 1109460705308203114125779)
                      ·
                        rfl

theorem cell23_2160667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_2160667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160667 prefixEnd_2160667 := by exact prefixLift 2160667
  have htrace : WordTrace (prefixWord ++ tailWord_2160667) baseStart_2160667 baseEnd_2160667 := by
    simpa [prefixWord, tailWord_2160667, baseEnd_2160667] using wordTrace_append hprefix tailTrace_2160667
  have hstable : (prefixWord ++ tailWord_2160667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160667).length < 2 ^ (prefixWord ++ tailWord_2160667).sum := by decide
  have hdescent : baseEnd_2160667 < baseStart_2160667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160674 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2160674 : Nat := 118140960795 + 2160674 * 2 ^ 59
def prefixEnd_2160674 : Nat := 4983230072969 + 3 ^ 40 * 2160674 * 2
def baseEnd_2160674 : Nat := 369821433224261528912749

theorem tailTrace_2160674 : CollatzResearch.WordTrace tailWord_2160674 prefixEnd_2160674 369821433224261528912749 := by
  unfold tailWord_2160674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19701563743563646646406269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52537503316169724390416717 19701563743563646646406269)
  ·
    refine ⟨7388086403836367492402351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19701563743563646646406269 7388086403836367492402351)
    ·
      refine ⟨11082129605754551238603527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388086403836367492402351 11082129605754551238603527)
      ·
        refine ⟨16623194408631826857905291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11082129605754551238603527 16623194408631826857905291)
        ·
          refine ⟨24934791612947740286857937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16623194408631826857905291 24934791612947740286857937)
          ·
            refine ⟨18701093709710805215143453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24934791612947740286857937 18701093709710805215143453)
            ·
              refine ⟨7012910141141551955678795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18701093709710805215143453 7012910141141551955678795)
              ·
                refine ⟨10519365211712327933518193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7012910141141551955678795 10519365211712327933518193)
                ·
                  refine ⟨7889523908784245950138645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10519365211712327933518193 7889523908784245950138645)
                  ·
                    refine ⟨369821433224261528912749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7889523908784245950138645 369821433224261528912749)
                    ·
                      rfl

theorem cell23_2160674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2160674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160674 prefixEnd_2160674 := by exact prefixLift 2160674
  have htrace : WordTrace (prefixWord ++ tailWord_2160674) baseStart_2160674 baseEnd_2160674 := by
    simpa [prefixWord, tailWord_2160674, baseEnd_2160674] using wordTrace_append hprefix tailTrace_2160674
  have hstable : (prefixWord ++ tailWord_2160674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160674).length < 2 ^ (prefixWord ++ tailWord_2160674).sum := by decide
  have hdescent : baseEnd_2160674 < baseStart_2160674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160732 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_2160732 : Nat := 118140960795 + 2160732 * 2 ^ 59
def prefixEnd_2160732 : Nat := 4983230072969 + 3 ^ 40 * 2160732 * 2
def baseEnd_2160732 : Nat := 1109494081550745359812981

theorem tailTrace_2160732 : CollatzResearch.WordTrace tailWord_2160732 prefixEnd_2160732 1109494081550745359812981 := by
  unfold tailWord_2160732
  simp only [CollatzResearch.WordTrace]
  refine ⟨39404185204022231245618225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52538913605362974994157633 39404185204022231245618225)
  ·
    refine ⟨29553138903016673434213669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39404185204022231245618225 29553138903016673434213669)
    ·
      refine ⟨5541213544315626268915063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29553138903016673434213669 5541213544315626268915063)
      ·
        refine ⟨8311820316473439403372595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5541213544315626268915063 8311820316473439403372595)
        ·
          refine ⟨12467730474710159105058893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311820316473439403372595 12467730474710159105058893)
          ·
            refine ⟨4675398928016309664397085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12467730474710159105058893 4675398928016309664397085)
            ·
              refine ⟨1753274598006116124148907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4675398928016309664397085 1753274598006116124148907)
              ·
                refine ⟨2629911897009174186223361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753274598006116124148907 2629911897009174186223361)
                ·
                  refine ⟨1972433922756880639667521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2629911897009174186223361 1972433922756880639667521)
                  ·
                    refine ⟨1479325442067660479750641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972433922756880639667521 1479325442067660479750641)
                    ·
                      refine ⟨1109494081550745359812981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479325442067660479750641 1109494081550745359812981)
                      ·
                        rfl

theorem cell23_2160732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_2160732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160732 prefixEnd_2160732 := by exact prefixLift 2160732
  have htrace : WordTrace (prefixWord ++ tailWord_2160732) baseStart_2160732 baseEnd_2160732 := by
    simpa [prefixWord, tailWord_2160732, baseEnd_2160732] using wordTrace_append hprefix tailTrace_2160732
  have hstable : (prefixWord ++ tailWord_2160732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160732).length < 2 ^ (prefixWord ++ tailWord_2160732).sum := by decide
  have hdescent : baseEnd_2160732 < baseStart_2160732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160771 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 4]
def baseStart_2160771 : Nat := 118140960795 + 2160771 * 2 ^ 59
def prefixEnd_2160771 : Nat := 4983230072969 + 3 ^ 40 * 2160771 * 2
def baseEnd_2160771 : Nat := 1109514107296270707225301

theorem tailTrace_2160771 : CollatzResearch.WordTrace tailWord_2160771 prefixEnd_2160771 1109514107296270707225301 := by
  unfold tailWord_2160771
  simp only [CollatzResearch.WordTrace]
  refine ⟨78809792854903172151906167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52539861903268781434604111 78809792854903172151906167)
  ·
    refine ⟨118214689282354758227859251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78809792854903172151906167 118214689282354758227859251)
    ·
      refine ⟨177322033923532137341788877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118214689282354758227859251 177322033923532137341788877)
      ·
        refine ⟨66495762721324551503170829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177322033923532137341788877 66495762721324551503170829)
        ·
          refine ⟨24935911020496706813689061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66495762721324551503170829 24935911020496706813689061)
          ·
            refine ⟨4675483316343132527566699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24935911020496706813689061 4675483316343132527566699)
            ·
              refine ⟨7013224974514698791350049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4675483316343132527566699 7013224974514698791350049)
              ·
                refine ⟨5259918730886024093512537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7013224974514698791350049 5259918730886024093512537)
                ·
                  refine ⟨3944939048164518070134403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5259918730886024093512537 3944939048164518070134403)
                  ·
                    refine ⟨5917408572246777105201605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3944939048164518070134403 5917408572246777105201605)
                    ·
                      refine ⟨1109514107296270707225301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5917408572246777105201605 1109514107296270707225301)
                      ·
                        rfl

theorem cell23_2160771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_2160771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160771 prefixEnd_2160771 := by exact prefixLift 2160771
  have htrace : WordTrace (prefixWord ++ tailWord_2160771) baseStart_2160771 baseEnd_2160771 := by
    simpa [prefixWord, tailWord_2160771, baseEnd_2160771] using wordTrace_append hprefix tailTrace_2160771
  have hstable : (prefixWord ++ tailWord_2160771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160771).length < 2 ^ (prefixWord ++ tailWord_2160771).sum := by decide
  have hdescent : baseEnd_2160771 < baseStart_2160771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160828 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 6]
def baseStart_2160828 : Nat := 118140960795 + 2160828 * 2 ^ 59
def prefixEnd_2160828 : Nat := 4983230072969 + 3 ^ 40 * 2160828 * 2
def baseEnd_2160828 : Nat := 123282597299286331579171

theorem tailTrace_2160828 : CollatzResearch.WordTrace tailWord_2160828 prefixEnd_2160828 123282597299286331579171 := by
  unfold tailWord_2160828
  simp only [CollatzResearch.WordTrace]
  refine ⟨39405935907848335443365569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52541247877131113924487425 39405935907848335443365569)
  ·
    refine ⟨29554451930886251582524177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39405935907848335443365569 29554451930886251582524177)
    ·
      refine ⟨22165838948164688686893133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29554451930886251582524177 22165838948164688686893133)
      ·
        refine ⟨8312189605561758257584925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22165838948164688686893133 8312189605561758257584925)
        ·
          refine ⟨3117071102085659346594347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8312189605561758257584925 3117071102085659346594347)
          ·
            refine ⟨4675606653128489019891521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117071102085659346594347 4675606653128489019891521)
            ·
              refine ⟨3506704989846366764918641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4675606653128489019891521 3506704989846366764918641)
              ·
                refine ⟨2630028742384775073688981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3506704989846366764918641 2630028742384775073688981)
                ·
                  refine ⟨123282597299286331579171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2630028742384775073688981 123282597299286331579171)
                  ·
                    rfl

theorem cell23_2160828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_2160828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160828 prefixEnd_2160828 := by exact prefixLift 2160828
  have htrace : WordTrace (prefixWord ++ tailWord_2160828) baseStart_2160828 baseEnd_2160828 := by
    simpa [prefixWord, tailWord_2160828, baseEnd_2160828] using wordTrace_append hprefix tailTrace_2160828
  have hstable : (prefixWord ++ tailWord_2160828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160828).length < 2 ^ (prefixWord ++ tailWord_2160828).sum := by decide
  have hdescent : baseEnd_2160828 < baseStart_2160828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160831 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 3, 5, 2]
def baseStart_2160831 : Nat := 118140960795 + 2160831 * 2 ^ 59
def prefixEnd_2160831 : Nat := 4983230072969 + 3 ^ 40 * 2160831 * 2
def baseEnd_2160831 : Nat := 1109544916135540472475025

theorem tailTrace_2160831 : CollatzResearch.WordTrace tailWord_2160831 prefixEnd_2160831 1109544916135540472475025 := by
  unfold tailWord_2160831
  simp only [CollatzResearch.WordTrace]
  refine ⟨78811981234685802399090347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52541320823123868266060231 78811981234685802399090347)
  ·
    refine ⟨118217971852028703598635521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78811981234685802399090347 118217971852028703598635521)
    ·
      refine ⟨88663478889021527698976641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118217971852028703598635521 88663478889021527698976641)
      ·
        refine ⟨66497609166766145774232481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88663478889021527698976641 66497609166766145774232481)
        ·
          refine ⟨49873206875074609330674361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66497609166766145774232481 49873206875074609330674361)
          ·
            refine ⟨37404905156305956998005771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49873206875074609330674361 37404905156305956998005771)
            ·
              refine ⟨56107357734458935497008657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37404905156305956998005771 56107357734458935497008657)
              ·
                refine ⟨42080518300844201622756493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56107357734458935497008657 42080518300844201622756493)
                ·
                  refine ⟨15780194362816575608533685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42080518300844201622756493 15780194362816575608533685)
                  ·
                    refine ⟨1479393221514053963300033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15780194362816575608533685 1479393221514053963300033)
                    ·
                      refine ⟨1109544916135540472475025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479393221514053963300033 1109544916135540472475025)
                      ·
                        rfl

theorem cell23_2160831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_2160831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160831 prefixEnd_2160831 := by exact prefixLift 2160831
  have htrace : WordTrace (prefixWord ++ tailWord_2160831) baseStart_2160831 baseEnd_2160831 := by
    simpa [prefixWord, tailWord_2160831, baseEnd_2160831] using wordTrace_append hprefix tailTrace_2160831
  have hstable : (prefixWord ++ tailWord_2160831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160831).length < 2 ^ (prefixWord ++ tailWord_2160831).sum := by decide
  have hdescent : baseEnd_2160831 < baseStart_2160831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160832 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 1, 4]
def baseStart_2160832 : Nat := 118140960795 + 2160832 * 2 ^ 59
def prefixEnd_2160832 : Nat := 4983230072969 + 3 ^ 40 * 2160832 * 2
def baseEnd_2160832 : Nat := 369848476538731656187507

theorem tailTrace_2160832 : CollatzResearch.WordTrace tailWord_2160832 prefixEnd_2160832 369848476538731656187507 := by
  unfold tailWord_2160832
  simp only [CollatzResearch.WordTrace]
  refine ⟨39406008853841089784938375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52541345138454786379917833 39406008853841089784938375)
  ·
    refine ⟨59109013280761634677407563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39406008853841089784938375 59109013280761634677407563)
    ·
      refine ⟨88663519921142452016111345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59109013280761634677407563 88663519921142452016111345)
      ·
        refine ⟨66497639940856839012083509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88663519921142452016111345 66497639940856839012083509)
        ·
          refine ⟨6234153744455328657382829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66497639940856839012083509 6234153744455328657382829)
          ·
            refine ⟨2337807654170748246518561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6234153744455328657382829 2337807654170748246518561)
            ·
              refine ⟨1753355740628061184888921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337807654170748246518561 1753355740628061184888921)
              ·
                refine ⟨1315016805471045888666691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753355740628061184888921 1315016805471045888666691)
                ·
                  refine ⟨1972525208206568833000037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315016805471045888666691 1972525208206568833000037)
                  ·
                    refine ⟨369848476538731656187507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1972525208206568833000037 369848476538731656187507)
                    ·
                      rfl

theorem cell23_2160832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 4].length) (baseStart_2160832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160832 prefixEnd_2160832 := by exact prefixLift 2160832
  have htrace : WordTrace (prefixWord ++ tailWord_2160832) baseStart_2160832 baseEnd_2160832 := by
    simpa [prefixWord, tailWord_2160832, baseEnd_2160832] using wordTrace_append hprefix tailTrace_2160832
  have hstable : (prefixWord ++ tailWord_2160832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160832).length < 2 ^ (prefixWord ++ tailWord_2160832).sum := by decide
  have hdescent : baseEnd_2160832 < baseStart_2160832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160866 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2160866 : Nat := 118140960795 + 2160866 * 2 ^ 59
def prefixEnd_2160866 : Nat := 4983230072969 + 3 ^ 40 * 2160866 * 2
def baseEnd_2160866 : Nat := 369854295986149278512455

theorem tailTrace_2160866 : CollatzResearch.WordTrace tailWord_2160866 prefixEnd_2160866 369854295986149278512455 := by
  unfold tailWord_2160866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19703314447389750844153613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52542171859706002251076301 19703314447389750844153613)
  ·
    refine ⟨7388742917771156566557605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19703314447389750844153613 7388742917771156566557605)
    ·
      refine ⟨1385389297082091856229551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7388742917771156566557605 1385389297082091856229551)
      ·
        refine ⟨2078083945623137784344327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385389297082091856229551 2078083945623137784344327)
        ·
          refine ⟨3117125918434706676516491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078083945623137784344327 3117125918434706676516491)
          ·
            refine ⟨4675688877652060014774737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117125918434706676516491 4675688877652060014774737)
            ·
              refine ⟨3506766658239045011081053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4675688877652060014774737 3506766658239045011081053)
              ·
                refine ⟨1315037496839641879155395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3506766658239045011081053 1315037496839641879155395)
                ·
                  refine ⟨1972556245259462818733093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315037496839641879155395 1972556245259462818733093)
                  ·
                    refine ⟨369854295986149278512455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1972556245259462818733093 369854295986149278512455)
                    ·
                      rfl

theorem cell23_2160866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2160866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160866 prefixEnd_2160866 := by exact prefixLift 2160866
  have htrace : WordTrace (prefixWord ++ tailWord_2160866) baseStart_2160866 baseEnd_2160866 := by
    simpa [prefixWord, tailWord_2160866, baseEnd_2160866] using wordTrace_append hprefix tailTrace_2160866
  have hstable : (prefixWord ++ tailWord_2160866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160866).length < 2 ^ (prefixWord ++ tailWord_2160866).sum := by decide
  have hdescent : baseEnd_2160866 < baseStart_2160866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160872 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_2160872 : Nat := 118140960795 + 2160872 * 2 ^ 59
def prefixEnd_2160872 : Nat := 4983230072969 + 3 ^ 40 * 2160872 * 2
def baseEnd_2160872 : Nat := 1109565968842374812062337

theorem tailTrace_2160872 : CollatzResearch.WordTrace tailWord_2160872 prefixEnd_2160872 1109565968842374812062337 := by
  unfold tailWord_2160872
  simp only [CollatzResearch.WordTrace]
  refine ⟨39406738313768633200666435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52542317751691510934221913 39406738313768633200666435)
  ·
    refine ⟨59110107470652949800999653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39406738313768633200666435 59110107470652949800999653)
    ·
      refine ⟨11083145150747428087687435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59110107470652949800999653 11083145150747428087687435)
      ·
        refine ⟨16624717726121142131531153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11083145150747428087687435 16624717726121142131531153)
        ·
          refine ⟨12468538294590856598648365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16624717726121142131531153 12468538294590856598648365)
          ·
            refine ⟨4675701860471571224493137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12468538294590856598648365 4675701860471571224493137)
            ·
              refine ⟨3506776395353678418369853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4675701860471571224493137 3506776395353678418369853)
              ·
                refine ⟨1315041148257629406888695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3506776395353678418369853 1315041148257629406888695)
                ·
                  refine ⟨1972561722386444110333043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315041148257629406888695 1972561722386444110333043)
                  ·
                    refine ⟨2958842583579666165499565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972561722386444110333043 2958842583579666165499565)
                    ·
                      refine ⟨1109565968842374812062337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2958842583579666165499565 1109565968842374812062337)
                      ·
                        rfl

theorem cell23_2160872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_2160872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160872 prefixEnd_2160872 := by exact prefixLift 2160872
  have htrace : WordTrace (prefixWord ++ tailWord_2160872) baseStart_2160872 baseEnd_2160872 := by
    simpa [prefixWord, tailWord_2160872, baseEnd_2160872] using wordTrace_append hprefix tailTrace_2160872
  have hstable : (prefixWord ++ tailWord_2160872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160872).length < 2 ^ (prefixWord ++ tailWord_2160872).sum := by decide
  have hdescent : baseEnd_2160872 < baseStart_2160872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160895 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 3, 2, 2]
def baseStart_2160895 : Nat := 118140960795 + 2160895 * 2 ^ 59
def prefixEnd_2160895 : Nat := 4983230072969 + 3 ^ 40 * 2160895 * 2
def baseEnd_2160895 : Nat := 1109577778897428222074731

theorem tailTrace_2160895 : CollatzResearch.WordTrace tailWord_2160895 prefixEnd_2160895 1109577778897428222074731 := by
  unfold tailWord_2160895
  simp only [CollatzResearch.WordTrace]
  refine ⟨78814315506453941329420139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52542877004302627552946759 78814315506453941329420139)
  ·
    refine ⟨118221473259680911994130209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78814315506453941329420139 118221473259680911994130209)
    ·
      refine ⟨88666104944760683995597657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118221473259680911994130209 88666104944760683995597657)
      ·
        refine ⟨66499578708570512996698243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88666104944760683995597657 66499578708570512996698243)
        ·
          refine ⟨99749368062855769495047365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66499578708570512996698243 99749368062855769495047365)
          ·
            refine ⟨18703006511785456780321381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99749368062855769495047365 18703006511785456780321381)
            ·
              refine ⟨3506813720959773146310259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18703006511785456780321381 3506813720959773146310259)
              ·
                refine ⟨5260220581439659719465389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3506813720959773146310259 5260220581439659719465389)
                ·
                  refine ⟨1972582718039872394799521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5260220581439659719465389 1972582718039872394799521)
                  ·
                    refine ⟨1479437038529904296099641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972582718039872394799521 1479437038529904296099641)
                    ·
                      refine ⟨1109577778897428222074731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479437038529904296099641 1109577778897428222074731)
                      ·
                        rfl

theorem cell23_2160895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_2160895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160895 prefixEnd_2160895 := by exact prefixLift 2160895
  have htrace : WordTrace (prefixWord ++ tailWord_2160895) baseStart_2160895 baseEnd_2160895 := by
    simpa [prefixWord, tailWord_2160895, baseEnd_2160895] using wordTrace_append hprefix tailTrace_2160895
  have hstable : (prefixWord ++ tailWord_2160895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160895).length < 2 ^ (prefixWord ++ tailWord_2160895).sum := by decide
  have hdescent : baseEnd_2160895 < baseStart_2160895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160898 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2160898 : Nat := 118140960795 + 2160898 * 2 ^ 59
def prefixEnd_2160898 : Nat := 4983230072969 + 3 ^ 40 * 2160898 * 2
def baseEnd_2160898 : Nat := 1109579319339391710337217

theorem tailTrace_2160898 : CollatzResearch.WordTrace tailWord_2160898 prefixEnd_2160898 1109579319339391710337217 := by
  unfold tailWord_2160898
  simp only [CollatzResearch.WordTrace]
  refine ⟨19703606231360768210444837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52542949950295381894519565 19703606231360768210444837)
  ·
    refine ⟨3694426168380144039458407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19703606231360768210444837 3694426168380144039458407)
    ·
      refine ⟨5541639252570216059187611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694426168380144039458407 5541639252570216059187611)
      ·
        refine ⟨8312458878855324088781417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5541639252570216059187611 8312458878855324088781417)
        ·
          refine ⟨6234344159141493066586063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8312458878855324088781417 6234344159141493066586063)
          ·
            refine ⟨9351516238712239599879095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6234344159141493066586063 9351516238712239599879095)
            ·
              refine ⟨14027274358068359399818643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9351516238712239599879095 14027274358068359399818643)
              ·
                refine ⟨21040911537102539099727965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14027274358068359399818643 21040911537102539099727965)
                ·
                  refine ⟨7890341826413452162397987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21040911537102539099727965 7890341826413452162397987)
                  ·
                    refine ⟨11835512739620178243596981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7890341826413452162397987 11835512739620178243596981)
                    ·
                      refine ⟨1109579319339391710337217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11835512739620178243596981 1109579319339391710337217)
                      ·
                        rfl

theorem cell23_2160898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2160898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160898 prefixEnd_2160898 := by exact prefixLift 2160898
  have htrace : WordTrace (prefixWord ++ tailWord_2160898) baseStart_2160898 baseEnd_2160898 := by
    simpa [prefixWord, tailWord_2160898, baseEnd_2160898] using wordTrace_append hprefix tailTrace_2160898
  have hstable : (prefixWord ++ tailWord_2160898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160898).length < 2 ^ (prefixWord ++ tailWord_2160898).sum := by decide
  have hdescent : baseEnd_2160898 < baseStart_2160898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160905 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 2, 4]
def baseStart_2160905 : Nat := 118140960795 + 2160905 * 2 ^ 59
def prefixEnd_2160905 : Nat := 4983230072969 + 3 ^ 40 * 2160905 * 2
def baseEnd_2160905 : Nat := 369860971234657727649895

theorem tailTrace_2160905 : CollatzResearch.WordTrace tailWord_2160905 prefixEnd_2160905 369860971234657727649895 := by
  unfold tailWord_2160905
  simp only [CollatzResearch.WordTrace]
  refine ⟨78814680236417713037284169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52543120157611808691522779 78814680236417713037284169)
  ·
    refine ⟨59111010177313284777963127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78814680236417713037284169 59111010177313284777963127)
    ·
      refine ⟨88666515265969927166944691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59111010177313284777963127 88666515265969927166944691)
      ·
        refine ⟨132999772898954890750417037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88666515265969927166944691 132999772898954890750417037)
        ·
          refine ⟨49874914837108084031406389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132999772898954890750417037 49874914837108084031406389)
          ·
            refine ⟨4675773265978882877944349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49874914837108084031406389 4675773265978882877944349)
            ·
              refine ⟨1753414974742081079229131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4675773265978882877944349 1753414974742081079229131)
              ·
                refine ⟨2630122462113121618843697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753414974742081079229131 2630122462113121618843697)
                ·
                  refine ⟨1972591846584841214132773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2630122462113121618843697 1972591846584841214132773)
                  ·
                    refine ⟨369860971234657727649895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1972591846584841214132773 369860971234657727649895)
                    ·
                      rfl

theorem cell23_2160905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 4].length) (baseStart_2160905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160905 prefixEnd_2160905 := by exact prefixLift 2160905
  have htrace : WordTrace (prefixWord ++ tailWord_2160905) baseStart_2160905 baseEnd_2160905 := by
    simpa [prefixWord, tailWord_2160905, baseEnd_2160905] using wordTrace_append hprefix tailTrace_2160905
  have hstable : (prefixWord ++ tailWord_2160905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160905).length < 2 ^ (prefixWord ++ tailWord_2160905).sum := by decide
  have hdescent : baseEnd_2160905 < baseStart_2160905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160946 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_2160946 : Nat := 118140960795 + 2160946 * 2 ^ 59
def prefixEnd_2160946 : Nat := 4983230072969 + 3 ^ 40 * 2160946 * 2
def baseEnd_2160946 : Nat := 1109603966410807522536997

theorem tailTrace_2160946 : CollatzResearch.WordTrace tailWord_2160946 prefixEnd_2160946 1109603966410807522536997 := by
  unfold tailWord_2160946
  simp only [CollatzResearch.WordTrace]
  refine ⟨19704043907317294259881673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52544117086179451359684461 19704043907317294259881673)
  ·
    refine ⟨14778032930487970694911255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19704043907317294259881673 14778032930487970694911255)
    ·
      refine ⟨22167049395731956042366883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14778032930487970694911255 22167049395731956042366883)
      ·
        refine ⟨33250574093597934063550325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22167049395731956042366883 33250574093597934063550325)
        ·
          refine ⟨3117241321274806318457843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33250574093597934063550325 3117241321274806318457843)
          ·
            refine ⟨4675861981912209477686765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117241321274806318457843 4675861981912209477686765)
            ·
              refine ⟨1753448243217078554132537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4675861981912209477686765 1753448243217078554132537)
              ·
                refine ⟨1315086182412808915599403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753448243217078554132537 1315086182412808915599403)
                ·
                  refine ⟨1972629273619213373399105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315086182412808915599403 1972629273619213373399105)
                  ·
                    refine ⟨1479471955214410030049329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972629273619213373399105 1479471955214410030049329)
                    ·
                      refine ⟨1109603966410807522536997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479471955214410030049329 1109603966410807522536997)
                      ·
                        rfl

theorem cell23_2160946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_2160946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160946 prefixEnd_2160946 := by exact prefixLift 2160946
  have htrace : WordTrace (prefixWord ++ tailWord_2160946) baseStart_2160946 baseEnd_2160946 := by
    simpa [prefixWord, tailWord_2160946, baseEnd_2160946] using wordTrace_append hprefix tailTrace_2160946
  have hstable : (prefixWord ++ tailWord_2160946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160946).length < 2 ^ (prefixWord ++ tailWord_2160946).sum := by decide
  have hdescent : baseEnd_2160946 < baseStart_2160946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160971 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 3]
def baseStart_2160971 : Nat := 118140960795 + 2160971 * 2 ^ 59
def prefixEnd_2160971 : Nat := 4983230072969 + 3 ^ 40 * 2160971 * 2
def baseEnd_2160971 : Nat := 1109616803427169924724381

theorem tailTrace_2160971 : CollatzResearch.WordTrace tailWord_2160971 prefixEnd_2160971 1109616803427169924724381 := by
  unfold tailWord_2160971
  simp only [CollatzResearch.WordTrace]
  refine ⟨78817087454178606309186767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52544724969452404206124511 78817087454178606309186767)
  ·
    refine ⟨118225631181267909463780151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78817087454178606309186767 118225631181267909463780151)
    ·
      refine ⟨177338446771901864195670227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118225631181267909463780151 177338446771901864195670227)
      ·
        refine ⟨266007670157852796293505341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177338446771901864195670227 266007670157852796293505341)
        ·
          refine ⟨99752876309194798610064503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266007670157852796293505341 99752876309194798610064503)
          ·
            refine ⟨149629314463792197915096755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99752876309194798610064503 149629314463792197915096755)
            ·
              refine ⟨224443971695688296872645133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149629314463792197915096755 224443971695688296872645133)
              ·
                refine ⟨84166489385883111327241925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224443971695688296872645133 84166489385883111327241925)
                ·
                  refine ⟨15781216759853083373857861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84166489385883111327241925 15781216759853083373857861)
                  ·
                    refine ⟨2958978142472453132598349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15781216759853083373857861 2958978142472453132598349)
                    ·
                      refine ⟨1109616803427169924724381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2958978142472453132598349 1109616803427169924724381)
                      ·
                        rfl

theorem cell23_2160971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 3].length) (baseStart_2160971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2160971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2160971 prefixEnd_2160971 := by exact prefixLift 2160971
  have htrace : WordTrace (prefixWord ++ tailWord_2160971) baseStart_2160971 baseEnd_2160971 := by
    simpa [prefixWord, tailWord_2160971, baseEnd_2160971] using wordTrace_append hprefix tailTrace_2160971
  have hstable : (prefixWord ++ tailWord_2160971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160971).length < 2 ^ (prefixWord ++ tailWord_2160971).sum := by decide
  have hdescent : baseEnd_2160971 < baseStart_2160971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161085 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2161085 : Nat := 118140960795 + 2161085 * 2 ^ 59
def prefixEnd_2161085 : Nat := 4983230072969 + 3 ^ 40 * 2161085 * 2
def baseEnd_2161085 : Nat := 369891780073927492899619

theorem tailTrace_2161085 : CollatzResearch.WordTrace tailWord_2161085 prefixEnd_2161085 369891780073927492899619 := by
  unfold tailWord_2161085
  simp only [CollatzResearch.WordTrace]
  refine ⟨78821245375765603778836709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52547496917177069185891139 78821245375765603778836709)
  ·
    refine ⟨14778983507956050708531883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78821245375765603778836709 14778983507956050708531883)
    ·
      refine ⟨22168475261934076062797825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14778983507956050708531883 22168475261934076062797825)
      ·
        refine ⟨16626356446450557047098369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22168475261934076062797825 16626356446450557047098369)
        ·
          refine ⟨12469767334837917785323777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16626356446450557047098369 12469767334837917785323777)
          ·
            refine ⟨9352325501128438338992833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12469767334837917785323777 9352325501128438338992833)
            ·
              refine ⟨7014244125846328754244625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9352325501128438338992833 7014244125846328754244625)
              ·
                refine ⟨5260683094384746565683469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7014244125846328754244625 5260683094384746565683469)
                ·
                  refine ⟨1972756160394279962131301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5260683094384746565683469 1972756160394279962131301)
                  ·
                    refine ⟨369891780073927492899619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1972756160394279962131301 369891780073927492899619)
                    ·
                      rfl

theorem cell23_2161085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2161085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161085 prefixEnd_2161085 := by exact prefixLift 2161085
  have htrace : WordTrace (prefixWord ++ tailWord_2161085) baseStart_2161085 baseEnd_2161085 := by
    simpa [prefixWord, tailWord_2161085, baseEnd_2161085] using wordTrace_append hprefix tailTrace_2161085
  have hstable : (prefixWord ++ tailWord_2161085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161085).length < 2 ^ (prefixWord ++ tailWord_2161085).sum := by decide
  have hdescent : baseEnd_2161085 < baseStart_2161085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161119 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 1, 4]
def baseStart_2161119 : Nat := 118140960795 + 2161119 * 2 ^ 59
def prefixEnd_2161119 : Nat := 4983230072969 + 3 ^ 40 * 2161119 * 2
def baseEnd_2161119 : Nat := 369897599521345115224567

theorem tailTrace_2161119 : CollatzResearch.WordTrace tailWord_2161119 prefixEnd_2161119 369897599521345115224567 := by
  unfold tailWord_2161119
  simp only [CollatzResearch.WordTrace]
  refine ⟨78822485457642427585574411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52548323638428285057049607 78822485457642427585574411)
  ·
    refine ⟨118233728186463641378361617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78822485457642427585574411 118233728186463641378361617)
    ·
      refine ⟨88675296139847731033771213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118233728186463641378361617 88675296139847731033771213)
      ·
        refine ⟨33253236052442899137664205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88675296139847731033771213 33253236052442899137664205)
        ·
          refine ⟨12469963519666087176624077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33253236052442899137664205 12469963519666087176624077)
          ·
            refine ⟨4676236319874782691234029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12469963519666087176624077 4676236319874782691234029)
            ·
              refine ⟨1753588619953043509212761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4676236319874782691234029 1753588619953043509212761)
              ·
                refine ⟨1315191464964782631909571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753588619953043509212761 1315191464964782631909571)
                ·
                  refine ⟨1972787197447173947864357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315191464964782631909571 1972787197447173947864357)
                  ·
                    refine ⟨369897599521345115224567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1972787197447173947864357 369897599521345115224567)
                    ·
                      rfl

theorem cell23_2161119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 4].length) (baseStart_2161119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161119 prefixEnd_2161119 := by exact prefixLift 2161119
  have htrace : WordTrace (prefixWord ++ tailWord_2161119) baseStart_2161119 baseEnd_2161119 := by
    simpa [prefixWord, tailWord_2161119, baseEnd_2161119] using wordTrace_append hprefix tailTrace_2161119
  have hstable : (prefixWord ++ tailWord_2161119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161119).length < 2 ^ (prefixWord ++ tailWord_2161119).sum := by decide
  have hdescent : baseEnd_2161119 < baseStart_2161119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161135 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 6, 3, 2]
def baseStart_2161135 : Nat := 118140960795 + 2161135 * 2 ^ 59
def prefixEnd_2161135 : Nat := 4983230072969 + 3 ^ 40 * 2161135 * 2
def baseEnd_2161135 : Nat := 1109701014254507283073627

theorem tailTrace_2161135 : CollatzResearch.WordTrace tailWord_2161135 prefixEnd_2161135 1109701014254507283073627 := by
  unfold tailWord_2161135
  simp only [CollatzResearch.WordTrace]
  refine ⟨78823069025584462318156859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52548712683722974878771239 78823069025584462318156859)
  ·
    refine ⟨118234603538376693477235289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78823069025584462318156859 118234603538376693477235289)
    ·
      refine ⟨88675952653782520107926467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118234603538376693477235289 88675952653782520107926467)
      ·
        refine ⟨133013928980673780161889701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88675952653782520107926467 133013928980673780161889701)
        ·
          refine ⟨24940111683876333780354319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133013928980673780161889701 24940111683876333780354319)
          ·
            refine ⟨37410167525814500670531479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24940111683876333780354319 37410167525814500670531479)
            ·
              refine ⟨56115251288721751005797219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37410167525814500670531479 56115251288721751005797219)
              ·
                refine ⟨84172876933082626508695829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56115251288721751005797219 84172876933082626508695829)
                ·
                  refine ⟨3945603606238248117595117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84172876933082626508695829 3945603606238248117595117)
                  ·
                    refine ⟨1479601352339343044098169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3945603606238248117595117 1479601352339343044098169)
                    ·
                      refine ⟨1109701014254507283073627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479601352339343044098169 1109701014254507283073627)
                      ·
                        rfl

theorem cell23_2161135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3, 2].length) (baseStart_2161135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161135 prefixEnd_2161135 := by exact prefixLift 2161135
  have htrace : WordTrace (prefixWord ++ tailWord_2161135) baseStart_2161135 baseEnd_2161135 := by
    simpa [prefixWord, tailWord_2161135, baseEnd_2161135] using wordTrace_append hprefix tailTrace_2161135
  have hstable : (prefixWord ++ tailWord_2161135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161135).length < 2 ^ (prefixWord ++ tailWord_2161135).sum := by decide
  have hdescent : baseEnd_2161135 < baseStart_2161135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161142 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2161142 : Nat := 118140960795 + 2161142 * 2 ^ 59
def prefixEnd_2161142 : Nat := 4983230072969 + 3 ^ 40 * 2161142 * 2
def baseEnd_2161142 : Nat := 1109704608619088755686095

theorem tailTrace_2161142 : CollatzResearch.WordTrace tailWord_2161142 prefixEnd_2161142 1109704608619088755686095 := by
  unfold tailWord_2161142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926457771034943907103855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52548882891039401675774453 4926457771034943907103855)
  ·
    refine ⟨7389686656552415860655783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4926457771034943907103855 7389686656552415860655783)
    ·
      refine ⟨11084529984828623790983675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7389686656552415860655783 11084529984828623790983675)
      ·
        refine ⟨16626794977242935686475513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11084529984828623790983675 16626794977242935686475513)
        ·
          refine ⟨12470096232932201764856635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16626794977242935686475513 12470096232932201764856635)
          ·
            refine ⟨18705144349398302647284953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12470096232932201764856635 18705144349398302647284953)
            ·
              refine ⟨14028858262048726985463715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18705144349398302647284953 14028858262048726985463715)
              ·
                refine ⟨21043287393073090478195573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14028858262048726985463715 21043287393073090478195573)
                ·
                  refine ⟨1972808193100602232330835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21043287393073090478195573 1972808193100602232330835)
                  ·
                    refine ⟨2959212289650903348496253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972808193100602232330835 2959212289650903348496253)
                    ·
                      refine ⟨1109704608619088755686095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959212289650903348496253 1109704608619088755686095)
                      ·
                        rfl

theorem cell23_2161142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2161142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161142 prefixEnd_2161142 := by exact prefixLift 2161142
  have htrace : WordTrace (prefixWord ++ tailWord_2161142) baseStart_2161142 baseEnd_2161142 := by
    simpa [prefixWord, tailWord_2161142, baseEnd_2161142] using wordTrace_append hprefix tailTrace_2161142
  have hstable : (prefixWord ++ tailWord_2161142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161142).length < 2 ^ (prefixWord ++ tailWord_2161142).sum := by decide
  have hdescent : baseEnd_2161142 < baseStart_2161142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161145 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 1, 5]
def baseStart_2161145 : Nat := 118140960795 + 2161145 * 2 ^ 59
def prefixEnd_2161145 : Nat := 4983230072969 + 3 ^ 40 * 2161145 * 2
def baseEnd_2161145 : Nat := 369902049687017414649527

theorem tailTrace_2161145 : CollatzResearch.WordTrace tailWord_2161145 prefixEnd_2161145 369902049687017414649527 := by
  unfold tailWord_2161145
  simp only [CollatzResearch.WordTrace]
  refine ⟨78823433755548234026020889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52548955837032156017347259 78823433755548234026020889)
  ·
    refine ⟨59117575316661175519515667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78823433755548234026020889 59117575316661175519515667)
    ·
      refine ⟨88676362974991763279273501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59117575316661175519515667 88676362974991763279273501)
      ·
        refine ⟨33253636115621911229727563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88676362974991763279273501 33253636115621911229727563)
        ·
          refine ⟨49880454173432866844591345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33253636115621911229727563 49880454173432866844591345)
          ·
            refine ⟨37410340630074650133443509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49880454173432866844591345 37410340630074650133443509)
            ·
              refine ⟨3507219434069498450010329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37410340630074650133443509 3507219434069498450010329)
              ·
                refine ⟨2630414575552123837507747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507219434069498450010329 2630414575552123837507747)
                ·
                  refine ⟨3945621863328185756261621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630414575552123837507747 3945621863328185756261621)
                  ·
                    refine ⟨369902049687017414649527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3945621863328185756261621 369902049687017414649527)
                    ·
                      rfl

theorem cell23_2161145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_2161145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161145 prefixEnd_2161145 := by exact prefixLift 2161145
  have htrace : WordTrace (prefixWord ++ tailWord_2161145) baseStart_2161145 baseEnd_2161145 := by
    simpa [prefixWord, tailWord_2161145, baseEnd_2161145] using wordTrace_append hprefix tailTrace_2161145
  have hstable : (prefixWord ++ tailWord_2161145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161145).length < 2 ^ (prefixWord ++ tailWord_2161145).sum := by decide
  have hdescent : baseEnd_2161145 < baseStart_2161145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161162 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_2161162 : Nat := 118140960795 + 2161162 * 2 ^ 59
def prefixEnd_2161162 : Nat := 4983230072969 + 3 ^ 40 * 2161162 * 2
def baseEnd_2161162 : Nat := 369904959410726225812001

theorem tailTrace_2161162 : CollatzResearch.WordTrace tailWord_2161162 prefixEnd_2161162 369904959410726225812001 := by
  unfold tailWord_2161162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19706013449121661482347435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52549369197657763952926493 19706013449121661482347435)
  ·
    refine ⟨29559020173682492223521153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19706013449121661482347435 29559020173682492223521153)
    ·
      refine ⟨22169265130261869167640865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29559020173682492223521153 22169265130261869167640865)
      ·
        refine ⟨16626948847696401875730649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22169265130261869167640865 16626948847696401875730649)
        ·
          refine ⟨12470211635772301406797987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16626948847696401875730649 12470211635772301406797987)
          ·
            refine ⟨18705317453658452110196981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12470211635772301406797987 18705317453658452110196981)
            ·
              refine ⟨1753623511280479885330967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18705317453658452110196981 1753623511280479885330967)
              ·
                refine ⟨2630435266920719827996451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753623511280479885330967 2630435266920719827996451)
                ·
                  refine ⟨3945652900381079741994677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630435266920719827996451 3945652900381079741994677)
                  ·
                    refine ⟨369904959410726225812001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3945652900381079741994677 369904959410726225812001)
                    ·
                      rfl

theorem cell23_2161162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_2161162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161162 prefixEnd_2161162 := by exact prefixLift 2161162
  have htrace : WordTrace (prefixWord ++ tailWord_2161162) baseStart_2161162 baseEnd_2161162 := by
    simpa [prefixWord, tailWord_2161162, baseEnd_2161162] using wordTrace_append hprefix tailTrace_2161162
  have hstable : (prefixWord ++ tailWord_2161162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161162).length < 2 ^ (prefixWord ++ tailWord_2161162).sum := by decide
  have hdescent : baseEnd_2161162 < baseStart_2161162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161168 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_2161168 : Nat := 118140960795 + 2161168 * 2 ^ 59
def prefixEnd_2161168 : Nat := 4983230072969 + 3 ^ 40 * 2161168 * 2
def baseEnd_2161168 : Nat := 1109717959116105653960975

theorem tailTrace_2161168 : CollatzResearch.WordTrace tailWord_2161168 prefixEnd_2161168 1109717959116105653960975 := by
  unfold tailWord_2161168
  simp only [CollatzResearch.WordTrace]
  refine ⟨39412136317232454477054079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52549515089643272636072105 39412136317232454477054079)
  ·
    refine ⟨59118204475848681715581119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39412136317232454477054079 59118204475848681715581119)
    ·
      refine ⟨88677306713773022573371679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59118204475848681715581119 88677306713773022573371679)
      ·
        refine ⟨133015960070659533860057519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88677306713773022573371679 133015960070659533860057519)
        ·
          refine ⟨199523940105989300790086279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133015960070659533860057519 199523940105989300790086279)
          ·
            refine ⟨299285910158983951185129419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199523940105989300790086279 299285910158983951185129419)
            ·
              refine ⟨448928865238475926777694129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299285910158983951185129419 448928865238475926777694129)
              ·
                refine ⟨336696648928856945083270597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448928865238475926777694129 336696648928856945083270597)
                ·
                  refine ⟨63130621674160677203113237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 336696648928856945083270597 63130621674160677203113237)
                  ·
                    refine ⟨2959247890976281743895933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63130621674160677203113237 2959247890976281743895933)
                    ·
                      refine ⟨1109717959116105653960975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959247890976281743895933 1109717959116105653960975)
                      ·
                        rfl

theorem cell23_2161168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_2161168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161168 prefixEnd_2161168 := by exact prefixLift 2161168
  have htrace : WordTrace (prefixWord ++ tailWord_2161168) baseStart_2161168 baseEnd_2161168 := by
    simpa [prefixWord, tailWord_2161168, baseEnd_2161168] using wordTrace_append hprefix tailTrace_2161168
  have hstable : (prefixWord ++ tailWord_2161168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161168).length < 2 ^ (prefixWord ++ tailWord_2161168).sum := by decide
  have hdescent : baseEnd_2161168 < baseStart_2161168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161176 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2161176 : Nat := 118140960795 + 2161176 * 2 ^ 59
def prefixEnd_2161176 : Nat := 4983230072969 + 3 ^ 40 * 2161176 * 2
def baseEnd_2161176 : Nat := 1109722066961341622660939

theorem tailTrace_2161176 : CollatzResearch.WordTrace tailWord_2161176 prefixEnd_2161176 1109722066961341622660939 := by
  unfold tailWord_2161176
  simp only [CollatzResearch.WordTrace]
  refine ⟨39412282209217963160199691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52549709612290617546932921 39412282209217963160199691)
  ·
    refine ⟨59118423313826944740299537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39412282209217963160199691 59118423313826944740299537)
    ·
      refine ⟨44338817485370208555224653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59118423313826944740299537 44338817485370208555224653)
      ·
        refine ⟨16627056557013828208209245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44338817485370208555224653 16627056557013828208209245)
        ·
          refine ⟨6235146208880185578078467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16627056557013828208209245 6235146208880185578078467)
          ·
            refine ⟨9352719313320278367117701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6235146208880185578078467 9352719313320278367117701)
            ·
              refine ⟨1753634871247552193834569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9352719313320278367117701 1753634871247552193834569)
              ·
                refine ⟨1315226153435664145375927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753634871247552193834569 1315226153435664145375927)
                ·
                  refine ⟨1972839230153496218063891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315226153435664145375927 1972839230153496218063891)
                  ·
                    refine ⟨2959258845230244327095837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972839230153496218063891 2959258845230244327095837)
                    ·
                      refine ⟨1109722066961341622660939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959258845230244327095837 1109722066961341622660939)
                      ·
                        rfl

theorem cell23_2161176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2161176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161176 prefixEnd_2161176 := by exact prefixLift 2161176
  have htrace : WordTrace (prefixWord ++ tailWord_2161176) baseStart_2161176 baseEnd_2161176 := by
    simpa [prefixWord, tailWord_2161176, baseEnd_2161176] using wordTrace_append hprefix tailTrace_2161176
  have hstable : (prefixWord ++ tailWord_2161176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161176).length < 2 ^ (prefixWord ++ tailWord_2161176).sum := by decide
  have hdescent : baseEnd_2161176 < baseStart_2161176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161178 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2161178 : Nat := 118140960795 + 2161178 * 2 ^ 59
def prefixEnd_2161178 : Nat := 4983230072969 + 3 ^ 40 * 2161178 * 2
def baseEnd_2161178 : Nat := 1109723093922650614835929

theorem tailTrace_2161178 : CollatzResearch.WordTrace tailWord_2161178 prefixEnd_2161178 1109723093922650614835929 := by
  unfold tailWord_2161178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19706159341107170165493047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52549758242952453774648125 19706159341107170165493047)
  ·
    refine ⟨29559239011660755248239571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19706159341107170165493047 29559239011660755248239571)
    ·
      refine ⟨44338858517491132872359357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29559239011660755248239571 44338858517491132872359357)
      ·
        refine ⟨16627071944059174827134759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44338858517491132872359357 16627071944059174827134759)
        ·
          refine ⟨24940607916088762240702139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16627071944059174827134759 24940607916088762240702139)
          ·
            refine ⟨37410911874133143361053209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24940607916088762240702139 37410911874133143361053209)
            ·
              refine ⟨28058183905599857520789907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37410911874133143361053209 28058183905599857520789907)
              ·
                refine ⟨42087275858399786281184861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28058183905599857520789907 42087275858399786281184861)
                ·
                  refine ⟨15782728446899919855444323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42087275858399786281184861 15782728446899919855444323)
                  ·
                    refine ⟨23674092670349879783166485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15782728446899919855444323 23674092670349879783166485)
                    ·
                      refine ⟨1109723093922650614835929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23674092670349879783166485 1109723093922650614835929)
                      ·
                        rfl

theorem cell23_2161178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2161178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161178 prefixEnd_2161178 := by exact prefixLift 2161178
  have htrace : WordTrace (prefixWord ++ tailWord_2161178) baseStart_2161178 baseEnd_2161178 := by
    simpa [prefixWord, tailWord_2161178, baseEnd_2161178] using wordTrace_append hprefix tailTrace_2161178
  have hstable : (prefixWord ++ tailWord_2161178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161178).length < 2 ^ (prefixWord ++ tailWord_2161178).sum := by decide
  have hdescent : baseEnd_2161178 < baseStart_2161178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161185 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2161185 : Nat := 118140960795 + 2161185 * 2 ^ 59
def prefixEnd_2161185 : Nat := 4983230072969 + 3 ^ 40 * 2161185 * 2
def baseEnd_2161185 : Nat := 1109726688287232087448397

theorem tailTrace_2161185 : CollatzResearch.WordTrace tailWord_2161185 prefixEnd_2161185 1109726688287232087448397 := by
  unfold tailWord_2161185
  simp only [CollatzResearch.WordTrace]
  refine ⟨78824892675403320857477009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52549928450268880571651339 78824892675403320857477009)
  ·
    refine ⟨59118669506552490643107757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78824892675403320857477009 59118669506552490643107757)
    ·
      refine ⟨22169501064957183991165409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59118669506552490643107757 22169501064957183991165409)
      ·
        refine ⟨16627125798717887993374057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22169501064957183991165409 16627125798717887993374057)
        ·
          refine ⟨12470344349038415995030543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16627125798717887993374057 12470344349038415995030543)
          ·
            refine ⟨18705516523557623992545815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12470344349038415995030543 18705516523557623992545815)
            ·
              refine ⟨28058274785336435988818723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18705516523557623992545815 28058274785336435988818723)
              ·
                refine ⟨42087412178004653983228085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28058274785336435988818723 42087412178004653983228085)
                ·
                  refine ⟨3945694891687936310927633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42087412178004653983228085 3945694891687936310927633)
                  ·
                    refine ⟨2959271168765952233195725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3945694891687936310927633 2959271168765952233195725)
                    ·
                      refine ⟨1109726688287232087448397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959271168765952233195725 1109726688287232087448397)
                      ·
                        rfl

theorem cell23_2161185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2161185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161185 prefixEnd_2161185 := by exact prefixLift 2161185
  have htrace : WordTrace (prefixWord ++ tailWord_2161185) baseStart_2161185 baseEnd_2161185 := by
    simpa [prefixWord, tailWord_2161185, baseEnd_2161185] using wordTrace_append hprefix tailTrace_2161185
  have hstable : (prefixWord ++ tailWord_2161185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161185).length < 2 ^ (prefixWord ++ tailWord_2161185).sum := by decide
  have hdescent : baseEnd_2161185 < baseStart_2161185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161192 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2161192 : Nat := 118140960795 + 2161192 * 2 ^ 59
def prefixEnd_2161192 : Nat := 4983230072969 + 3 ^ 40 * 2161192 * 2
def baseEnd_2161192 : Nat := 369910094217271186686955

theorem tailTrace_2161192 : CollatzResearch.WordTrace tailWord_2161192 prefixEnd_2161192 369910094217271186686955 := by
  unfold tailWord_2161192
  simp only [CollatzResearch.WordTrace]
  refine ⟨39412573993188980526490915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52550098657585307368654553 39412573993188980526490915)
  ·
    refine ⟨59118860989783470789736373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39412573993188980526490915 59118860989783470789736373)
    ·
      refine ⟨5542393217792200386537785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59118860989783470789736373 5542393217792200386537785)
      ·
        refine ⟨4156794913344150289903339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5542393217792200386537785 4156794913344150289903339)
        ·
          refine ⟨6235192370016225434855009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156794913344150289903339 6235192370016225434855009)
          ·
            refine ⟨4676394277512169076141257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6235192370016225434855009 4676394277512169076141257)
            ·
              refine ⟨3507295708134126807105943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4676394277512169076141257 3507295708134126807105943)
              ·
                refine ⟨5260943562201190210658915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507295708134126807105943 5260943562201190210658915)
                ·
                  refine ⟨7891415343301785315988373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5260943562201190210658915 7891415343301785315988373)
                  ·
                    refine ⟨369910094217271186686955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7891415343301785315988373 369910094217271186686955)
                    ·
                      rfl

theorem cell23_2161192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2161192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161192 prefixEnd_2161192 := by exact prefixLift 2161192
  have htrace : WordTrace (prefixWord ++ tailWord_2161192) baseStart_2161192 baseEnd_2161192 := by
    simpa [prefixWord, tailWord_2161192, baseEnd_2161192] using wordTrace_append hprefix tailTrace_2161192
  have hstable : (prefixWord ++ tailWord_2161192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161192).length < 2 ^ (prefixWord ++ tailWord_2161192).sum := by decide
  have hdescent : baseEnd_2161192 < baseStart_2161192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161205 : List Nat := [1, 3, 3, 1, 1, 2, 5, 7]
def baseStart_2161205 : Nat := 118140960795 + 2161205 * 2 ^ 59
def prefixEnd_2161205 : Nat := 4983230072969 + 3 ^ 40 * 2161205 * 2
def baseEnd_2161205 : Nat := 41101368811123037377715

theorem tailTrace_2161205 : CollatzResearch.WordTrace tailWord_2161205 prefixEnd_2161205 41101368811123037377715 := by
  unfold tailWord_2161205
  simp only [CollatzResearch.WordTrace]
  refine ⟨78825622135330864273205069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52550414756887242848803379 78825622135330864273205069)
  ·
    refine ⟨29559608300749074102451901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78825622135330864273205069 29559608300749074102451901)
    ·
      refine ⟨11084853112780902788419463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29559608300749074102451901 11084853112780902788419463)
      ·
        refine ⟨16627279669171354182629195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11084853112780902788419463 16627279669171354182629195)
        ·
          refine ⟨24940919503757031273943793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16627279669171354182629195 24940919503757031273943793)
          ·
            refine ⟨18705689627817773455457845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24940919503757031273943793 18705689627817773455457845)
            ·
              refine ⟨1753658402607916261449173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18705689627817773455457845 1753658402607916261449173)
              ·
                refine ⟨41101368811123037377715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1753658402607916261449173 41101368811123037377715)
                ·
                  rfl

theorem cell23_2161205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 7].length) (baseStart_2161205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161205 prefixEnd_2161205 := by exact prefixLift 2161205
  have htrace : WordTrace (prefixWord ++ tailWord_2161205) baseStart_2161205 baseEnd_2161205 := by
    simpa [prefixWord, tailWord_2161205, baseEnd_2161205] using wordTrace_append hprefix tailTrace_2161205
  have hstable : (prefixWord ++ tailWord_2161205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161205).length < 2 ^ (prefixWord ++ tailWord_2161205).sum := by decide
  have hdescent : baseEnd_2161205 < baseStart_2161205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161215 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_2161215 : Nat := 118140960795 + 2161215 * 2 ^ 59
def prefixEnd_2161215 : Nat := 4983230072969 + 3 ^ 40 * 2161215 * 2
def baseEnd_2161215 : Nat := 1109742092706866970073259

theorem tailTrace_2161215 : CollatzResearch.WordTrace tailWord_2161215 prefixEnd_2161215 1109742092706866970073259 := by
  unfold tailWord_2161215
  simp only [CollatzResearch.WordTrace]
  refine ⟨78825986865294635981069099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52550657910196423987379399 78825986865294635981069099)
  ·
    refine ⟨118238980297941953971603649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78825986865294635981069099 118238980297941953971603649)
    ·
      refine ⟨88679235223456465478702737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118238980297941953971603649 88679235223456465478702737)
      ·
        refine ⟨66509426417592349109027053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88679235223456465478702737 66509426417592349109027053)
        ·
          refine ⟨24941034906597130915885145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66509426417592349109027053 24941034906597130915885145)
          ·
            refine ⟨18705776179947848186913859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24941034906597130915885145 18705776179947848186913859)
            ·
              refine ⟨28058664269921772280370789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18705776179947848186913859 28058664269921772280370789)
              ·
                refine ⟨5260999550610332302569523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28058664269921772280370789 5260999550610332302569523)
                ·
                  refine ⟨7891499325915498453854285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5260999550610332302569523 7891499325915498453854285)
                  ·
                    refine ⟨2959312247218311920195357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7891499325915498453854285 2959312247218311920195357)
                    ·
                      refine ⟨1109742092706866970073259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959312247218311920195357 1109742092706866970073259)
                      ·
                        rfl

theorem cell23_2161215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_2161215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161215 prefixEnd_2161215 := by exact prefixLift 2161215
  have htrace : WordTrace (prefixWord ++ tailWord_2161215) baseStart_2161215 baseEnd_2161215 := by
    simpa [prefixWord, tailWord_2161215, baseEnd_2161215] using wordTrace_append hprefix tailTrace_2161215
  have hstable : (prefixWord ++ tailWord_2161215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161215).length < 2 ^ (prefixWord ++ tailWord_2161215).sum := by decide
  have hdescent : baseEnd_2161215 < baseStart_2161215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161222 : List Nat := [6, 1, 1, 1, 2, 2, 10]
def baseStart_2161222 : Nat := 118140960795 + 2161222 * 2 ^ 59
def prefixEnd_2161222 : Nat := 4983230072969 + 3 ^ 40 * 2161222 * 2
def baseEnd_2161222 : Nat := 13700564037919116576367

theorem tailTrace_2161222 : CollatzResearch.WordTrace tailWord_2161222 prefixEnd_2161222 13700564037919116576367 := by
  unfold tailWord_2161222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463320068008414880517935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52550828117512850784382613 2463320068008414880517935)
  ·
    refine ⟨3694980102012622320776903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2463320068008414880517935 3694980102012622320776903)
    ·
      refine ⟨5542470153018933481165355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694980102012622320776903 5542470153018933481165355)
      ·
        refine ⟨8313705229528400221748033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5542470153018933481165355 8313705229528400221748033)
        ·
          refine ⟨6235278922146300166311025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8313705229528400221748033 6235278922146300166311025)
          ·
            refine ⟨4676459191609725124733269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6235278922146300166311025 4676459191609725124733269)
            ·
              refine ⟨13700564037919116576367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4676459191609725124733269 13700564037919116576367)
              ·
                rfl

theorem cell23_2161222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 10].length) (baseStart_2161222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161222 prefixEnd_2161222 := by exact prefixLift 2161222
  have htrace : WordTrace (prefixWord ++ tailWord_2161222) baseStart_2161222 baseEnd_2161222 := by
    simpa [prefixWord, tailWord_2161222, baseEnd_2161222] using wordTrace_append hprefix tailTrace_2161222
  have hstable : (prefixWord ++ tailWord_2161222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161222).length < 2 ^ (prefixWord ++ tailWord_2161222).sum := by decide
  have hdescent : baseEnd_2161222 < baseStart_2161222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161232 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 2, 1, 3]
def baseStart_2161232 : Nat := 118140960795 + 2161232 * 2 ^ 59
def prefixEnd_2161232 : Nat := 4983230072969 + 3 ^ 40 * 2161232 * 2
def baseEnd_2161232 : Nat := 1109750821877993403560681

theorem tailTrace_2161232 : CollatzResearch.WordTrace tailWord_2161232 prefixEnd_2161232 1109750821877993403560681 := by
  unfold tailWord_2161232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39413303453116523942218975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52551071270822031922958633 39413303453116523942218975)
  ·
    refine ⟨59119955179674785913328463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39413303453116523942218975 59119955179674785913328463)
    ·
      refine ⟨88679932769512178869992695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59119955179674785913328463 88679932769512178869992695)
      ·
        refine ⟨133019899154268268304989043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88679932769512178869992695 133019899154268268304989043)
        ·
          refine ⟨199529848731402402457483565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133019899154268268304989043 199529848731402402457483565)
          ·
            refine ⟨74823693274275900921556337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199529848731402402457483565 74823693274275900921556337)
            ·
              refine ⟨56117769955706925691167253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74823693274275900921556337 56117769955706925691167253)
              ·
                refine ⟨2630520466673762141773465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56117769955706925691167253 2630520466673762141773465)
                ·
                  refine ⟨1972890350005321606330099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2630520466673762141773465 1972890350005321606330099)
                  ·
                    refine ⟨2959335525007982409495149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1972890350005321606330099 2959335525007982409495149)
                    ·
                      refine ⟨1109750821877993403560681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959335525007982409495149 1109750821877993403560681)
                      ·
                        rfl

theorem cell23_2161232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_2161232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161232 prefixEnd_2161232 := by exact prefixLift 2161232
  have htrace : WordTrace (prefixWord ++ tailWord_2161232) baseStart_2161232 baseEnd_2161232 := by
    simpa [prefixWord, tailWord_2161232, baseEnd_2161232] using wordTrace_append hprefix tailTrace_2161232
  have hstable : (prefixWord ++ tailWord_2161232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161232).length < 2 ^ (prefixWord ++ tailWord_2161232).sum := by decide
  have hdescent : baseEnd_2161232 < baseStart_2161232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161246 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2161246 : Nat := 118140960795 + 2161246 * 2 ^ 59
def prefixEnd_2161246 : Nat := 4983230072969 + 3 ^ 40 * 2161246 * 2
def baseEnd_2161246 : Nat := 1109758010607156348785617

theorem tailTrace_2161246 : CollatzResearch.WordTrace tailWord_2161246 prefixEnd_2161246 1109758010607156348785617 := by
  unfold tailWord_2161246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9853389691022791034430949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52551411685454885516965061 9853389691022791034430949)
  ·
    refine ⟨1847510567066773318955803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9853389691022791034430949 1847510567066773318955803)
    ·
      refine ⟨2771265850600159978433705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1847510567066773318955803 2771265850600159978433705)
      ·
        refine ⟨2078449387950119983825279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2771265850600159978433705 2078449387950119983825279)
        ·
          refine ⟨3117674081925179975737919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078449387950119983825279 3117674081925179975737919)
          ·
            refine ⟨4676511122887769963606879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3117674081925179975737919 4676511122887769963606879)
            ·
              refine ⟨7014766684331654945410319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676511122887769963606879 7014766684331654945410319)
              ·
                refine ⟨10522150026497482418115479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7014766684331654945410319 10522150026497482418115479)
                ·
                  refine ⟨15783225039746223627173219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10522150026497482418115479 15783225039746223627173219)
                  ·
                    refine ⟨23674837559619335440759829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15783225039746223627173219 23674837559619335440759829)
                    ·
                      refine ⟨1109758010607156348785617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23674837559619335440759829 1109758010607156348785617)
                      ·
                        rfl

theorem cell23_2161246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2161246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161246 prefixEnd_2161246 := by exact prefixLift 2161246
  have htrace : WordTrace (prefixWord ++ tailWord_2161246) baseStart_2161246 baseEnd_2161246 := by
    simpa [prefixWord, tailWord_2161246, baseEnd_2161246] using wordTrace_append hprefix tailTrace_2161246
  have hstable : (prefixWord ++ tailWord_2161246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161246).length < 2 ^ (prefixWord ++ tailWord_2161246).sum := by decide
  have hdescent : baseEnd_2161246 < baseStart_2161246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161289 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 2, 2, 2]
def baseStart_2161289 : Nat := 118140960795 + 2161289 * 2 ^ 59
def prefixEnd_2161289 : Nat := 4983230072969 + 3 ^ 40 * 2161289 * 2
def baseEnd_2161289 : Nat := 1109780090275299680547919

theorem tailTrace_2161289 : CollatzResearch.WordTrace tailWord_2161289 prefixEnd_2161289 1109780090275299680547919 := by
  unfold tailWord_2161289
  simp only [CollatzResearch.WordTrace]
  refine ⟨78828685867026546619262921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52552457244684364412841947 78828685867026546619262921)
  ·
    refine ⟨59121514400269909964447191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78828685867026546619262921 59121514400269909964447191)
    ·
      refine ⟨88682271600404864946670787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59121514400269909964447191 88682271600404864946670787)
      ·
        refine ⟨133023407400607297420006181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88682271600404864946670787 133023407400607297420006181)
        ·
          refine ⟨24941888887613868266251159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133023407400607297420006181 24941888887613868266251159)
          ·
            refine ⟨37412833331420802399376739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24941888887613868266251159 37412833331420802399376739)
            ·
              refine ⟨56119249997131203599065109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37412833331420802399376739 56119249997131203599065109)
              ·
                refine ⟨2630589843615525168706177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56119249997131203599065109 2630589843615525168706177)
                ·
                  refine ⟨1972942382711643876529633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2630589843615525168706177 1972942382711643876529633)
                  ·
                    refine ⟨1479706787033732907397225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1972942382711643876529633 1479706787033732907397225)
                    ·
                      refine ⟨1109780090275299680547919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479706787033732907397225 1109780090275299680547919)
                      ·
                        rfl

theorem cell23_2161289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 2, 2].length) (baseStart_2161289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161289 prefixEnd_2161289 := by exact prefixLift 2161289
  have htrace : WordTrace (prefixWord ++ tailWord_2161289) baseStart_2161289 baseEnd_2161289 := by
    simpa [prefixWord, tailWord_2161289, baseEnd_2161289] using wordTrace_append hprefix tailTrace_2161289
  have hstable : (prefixWord ++ tailWord_2161289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161289).length < 2 ^ (prefixWord ++ tailWord_2161289).sum := by decide
  have hdescent : baseEnd_2161289 < baseStart_2161289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161305 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_2161305 : Nat := 118140960795 + 2161305 * 2 ^ 59
def prefixEnd_2161305 : Nat := 4983230072969 + 3 ^ 40 * 2161305 * 2
def baseEnd_2161305 : Nat := 1109788305965771617947845

theorem tailTrace_2161305 : CollatzResearch.WordTrace tailWord_2161305 prefixEnd_2161305 1109788305965771617947845 := by
  unfold tailWord_2161305
  simp only [CollatzResearch.WordTrace]
  refine ⟨78829269434968581351845369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52552846289979054234563579 78829269434968581351845369)
  ·
    refine ⟨59121952076226436013884027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78829269434968581351845369 59121952076226436013884027)
    ·
      refine ⟨88682928114339654020826041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59121952076226436013884027 88682928114339654020826041)
      ·
        refine ⟨66512196085754740515619531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88682928114339654020826041 66512196085754740515619531)
        ·
          refine ⟨99768294128632110773429297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66512196085754740515619531 99768294128632110773429297)
          ·
            refine ⟨74826220596474083080071973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99768294128632110773429297 74826220596474083080071973)
            ·
              refine ⟨14029916361838890577513495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74826220596474083080071973 14029916361838890577513495)
              ·
                refine ⟨21044874542758335866270243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14029916361838890577513495 21044874542758335866270243)
                ·
                  refine ⟨31567311814137503799405365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21044874542758335866270243 31567311814137503799405365)
                  ·
                    refine ⟨2959435482575390981194253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31567311814137503799405365 2959435482575390981194253)
                    ·
                      refine ⟨1109788305965771617947845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959435482575390981194253 1109788305965771617947845)
                      ·
                        rfl

theorem cell23_2161305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_2161305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161305 prefixEnd_2161305 := by exact prefixLift 2161305
  have htrace : WordTrace (prefixWord ++ tailWord_2161305) baseStart_2161305 baseEnd_2161305 := by
    simpa [prefixWord, tailWord_2161305, baseEnd_2161305] using wordTrace_append hprefix tailTrace_2161305
  have hstable : (prefixWord ++ tailWord_2161305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161305).length < 2 ^ (prefixWord ++ tailWord_2161305).sum := by decide
  have hdescent : baseEnd_2161305 < baseStart_2161305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161342 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2161342 : Nat := 118140960795 + 2161342 * 2 ^ 59
def prefixEnd_2161342 : Nat := 4983230072969 + 3 ^ 40 * 2161342 * 2
def baseEnd_2161342 : Nat := 369935768249995991061725

theorem tailTrace_2161342 : CollatzResearch.WordTrace tailWord_2161342 prefixEnd_2161342 369935768249995991061725 := by
  unfold tailWord_2161342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9853827366979317083867785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52553745957223024447294853 9853827366979317083867785)
  ·
    refine ⟨7390370525234487812900839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9853827366979317083867785 7390370525234487812900839)
    ·
      refine ⟨11085555787851731719351259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7390370525234487812900839 11085555787851731719351259)
      ·
        refine ⟨16628333681777597579026889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11085555787851731719351259 16628333681777597579026889)
        ·
          refine ⟨12471250261333198184270167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16628333681777597579026889 12471250261333198184270167)
          ·
            refine ⟨18706875391999797276405251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12471250261333198184270167 18706875391999797276405251)
            ·
              refine ⟨28060313087999695914607877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18706875391999797276405251 28060313087999695914607877)
              ·
                refine ⟨5261308703999942983988977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28060313087999695914607877 5261308703999942983988977)
                ·
                  refine ⟨3945981527999957237991733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5261308703999942983988977 3945981527999957237991733)
                  ·
                    refine ⟨369935768249995991061725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3945981527999957237991733 369935768249995991061725)
                    ·
                      rfl

theorem cell23_2161342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2161342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161342 prefixEnd_2161342 := by exact prefixLift 2161342
  have htrace : WordTrace (prefixWord ++ tailWord_2161342) baseStart_2161342 baseEnd_2161342 := by
    simpa [prefixWord, tailWord_2161342, baseEnd_2161342] using wordTrace_append hprefix tailTrace_2161342
  have hstable : (prefixWord ++ tailWord_2161342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161342).length < 2 ^ (prefixWord ++ tailWord_2161342).sum := by decide
  have hdescent : baseEnd_2161342 < baseStart_2161342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161379 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2161379 : Nat := 118140960795 + 2161379 * 2 ^ 59
def prefixEnd_2161379 : Nat := 4983230072969 + 3 ^ 40 * 2161379 * 2
def baseEnd_2161379 : Nat := 1109826303534204328422505

theorem tailTrace_2161379 : CollatzResearch.WordTrace tailWord_2161379 prefixEnd_2161379 1109826303534204328422505 := by
  unfold tailWord_2161379
  simp only [CollatzResearch.WordTrace]
  refine ⟨78831968436700491990039191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52554645624466994660026127 78831968436700491990039191)
  ·
    refine ⟨118247952655050737985058787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78831968436700491990039191 118247952655050737985058787)
    ·
      refine ⟨177371928982576106977588181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118247952655050737985058787 177371928982576106977588181)
      ·
        refine ⟨4157154585529127507287223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 177371928982576106977588181 4157154585529127507287223)
        ·
          refine ⟨6235731878293691260930835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4157154585529127507287223 6235731878293691260930835)
          ·
            refine ⟨9353597817440536891396253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6235731878293691260930835 9353597817440536891396253)
            ·
              refine ⟨3507599181540201334273595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9353597817440536891396253 3507599181540201334273595)
              ·
                refine ⟨5261398772310302001410393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507599181540201334273595 5261398772310302001410393)
                ·
                  refine ⟨3946049079232726501057795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5261398772310302001410393 3946049079232726501057795)
                  ·
                    refine ⟨5919073618849089751586693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3946049079232726501057795 5919073618849089751586693)
                    ·
                      refine ⟨1109826303534204328422505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5919073618849089751586693 1109826303534204328422505)
                      ·
                        rfl

theorem cell23_2161379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2161379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161379 prefixEnd_2161379 := by exact prefixLift 2161379
  have htrace : WordTrace (prefixWord ++ tailWord_2161379) baseStart_2161379 baseEnd_2161379 := by
    simpa [prefixWord, tailWord_2161379, baseEnd_2161379] using wordTrace_append hprefix tailTrace_2161379
  have hstable : (prefixWord ++ tailWord_2161379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161379).length < 2 ^ (prefixWord ++ tailWord_2161379).sum := by decide
  have hdescent : baseEnd_2161379 < baseStart_2161379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161402 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_2161402 : Nat := 118140960795 + 2161402 * 2 ^ 59
def prefixEnd_2161402 : Nat := 4983230072969 + 3 ^ 40 * 2161402 * 2
def baseEnd_2161402 : Nat := 123315345954361970937211

theorem tailTrace_2161402 : CollatzResearch.WordTrace tailWord_2161402 prefixEnd_2161402 123315345954361970937211 := by
  unfold tailWord_2161402
  simp only [CollatzResearch.WordTrace]
  refine ⟨19708201828904291729531615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52555204877078111278750973 19708201828904291729531615)
  ·
    refine ⟨29562302743356437594297423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19708201828904291729531615 29562302743356437594297423)
    ·
      refine ⟨44343454115034656391446135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29562302743356437594297423 44343454115034656391446135)
      ·
        refine ⟨66515181172551984587169203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44343454115034656391446135 66515181172551984587169203)
        ·
          refine ⟨99772771758827976880753805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66515181172551984587169203 99772771758827976880753805)
          ·
            refine ⟨37414789409560491330282677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99772771758827976880753805 37414789409560491330282677)
            ·
              refine ⟨3507636507146296062214001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37414789409560491330282677 3507636507146296062214001)
              ·
                refine ⟨2630727380359722046660501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507636507146296062214001 2630727380359722046660501)
                ·
                  refine ⟨123315345954361970937211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2630727380359722046660501 123315345954361970937211)
                  ·
                    rfl

theorem cell23_2161402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_2161402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161402 prefixEnd_2161402 := by exact prefixLift 2161402
  have htrace : WordTrace (prefixWord ++ tailWord_2161402) baseStart_2161402 baseEnd_2161402 := by
    simpa [prefixWord, tailWord_2161402, baseEnd_2161402] using wordTrace_append hprefix tailTrace_2161402
  have hstable : (prefixWord ++ tailWord_2161402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161402).length < 2 ^ (prefixWord ++ tailWord_2161402).sum := by decide
  have hdescent : baseEnd_2161402 < baseStart_2161402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161405 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2161405 : Nat := 118140960795 + 2161405 * 2 ^ 59
def prefixEnd_2161405 : Nat := 4983230072969 + 3 ^ 40 * 2161405 * 2
def baseEnd_2161405 : Nat := 1109839654031221226697385

theorem tailTrace_2161405 : CollatzResearch.WordTrace tailWord_2161405 prefixEnd_2161405 1109839654031221226697385 := by
  unfold tailWord_2161405
  simp only [CollatzResearch.WordTrace]
  refine ⟨78832916734606298430485669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52555277823070865620323779 78832916734606298430485669)
  ·
    refine ⟨14781171887738680955716063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78832916734606298430485669 14781171887738680955716063)
    ·
      refine ⟨22171757831608021433574095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14781171887738680955716063 22171757831608021433574095)
      ·
        refine ⟨33257636747412032150361143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22171757831608021433574095 33257636747412032150361143)
        ·
          refine ⟨49886455121118048225541715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33257636747412032150361143 49886455121118048225541715)
          ·
            refine ⟨74829682681677072338312573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49886455121118048225541715 74829682681677072338312573)
            ·
              refine ⟨28061131005628902126867215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74829682681677072338312573 28061131005628902126867215)
              ·
                refine ⟨42091696508443353190300823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28061131005628902126867215 42091696508443353190300823)
                ·
                  refine ⟨63137544762665029785451235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42091696508443353190300823 63137544762665029785451235)
                  ·
                    refine ⟨94706317143997544678176853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63137544762665029785451235 94706317143997544678176853)
                    ·
                      refine ⟨1109839654031221226697385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94706317143997544678176853 1109839654031221226697385)
                      ·
                        rfl

theorem cell23_2161405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2161405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161405 prefixEnd_2161405 := by exact prefixLift 2161405
  have htrace : WordTrace (prefixWord ++ tailWord_2161405) baseStart_2161405 baseEnd_2161405 := by
    simpa [prefixWord, tailWord_2161405, baseEnd_2161405] using wordTrace_append hprefix tailTrace_2161405
  have hstable : (prefixWord ++ tailWord_2161405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161405).length < 2 ^ (prefixWord ++ tailWord_2161405).sum := by decide
  have hdescent : baseEnd_2161405 < baseStart_2161405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161406 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2161406 : Nat := 118140960795 + 2161406 * 2 ^ 59
def prefixEnd_2161406 : Nat := 4983230072969 + 3 ^ 40 * 2161406 * 2
def baseEnd_2161406 : Nat := 369946722503958574261627

theorem tailTrace_2161406 : CollatzResearch.WordTrace tailWord_2161406 prefixEnd_2161406 369946722503958574261627 := by
  unfold tailWord_2161406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854119150950334450159009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52555302138401783734181381 9854119150950334450159009)
  ·
    refine ⟨7390589363212750837619257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9854119150950334450159009 7390589363212750837619257)
    ·
      refine ⟨5542942022409563128214443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7390589363212750837619257 5542942022409563128214443)
      ·
        refine ⟨8314413033614344692321665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5542942022409563128214443 8314413033614344692321665)
        ·
          refine ⟨6235809775210758519241249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8314413033614344692321665 6235809775210758519241249)
          ·
            refine ⟨4676857331408068889430937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6235809775210758519241249 4676857331408068889430937)
            ·
              refine ⟨3507642998556051667073203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4676857331408068889430937 3507642998556051667073203)
              ·
                refine ⟨5261464497834077500609805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507642998556051667073203 5261464497834077500609805)
                ·
                  refine ⟨1973049186687779062728677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5261464497834077500609805 1973049186687779062728677)
                  ·
                    refine ⟨369946722503958574261627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1973049186687779062728677 369946722503958574261627)
                    ·
                      rfl

theorem cell23_2161406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2161406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161406 prefixEnd_2161406 := by exact prefixLift 2161406
  have htrace : WordTrace (prefixWord ++ tailWord_2161406) baseStart_2161406 baseEnd_2161406 := by
    simpa [prefixWord, tailWord_2161406, baseEnd_2161406] using wordTrace_append hprefix tailTrace_2161406
  have hstable : (prefixWord ++ tailWord_2161406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161406).length < 2 ^ (prefixWord ++ tailWord_2161406).sum := by decide
  have hdescent : baseEnd_2161406 < baseStart_2161406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161425 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2161425 : Nat := 118140960795 + 2161425 * 2 ^ 59
def prefixEnd_2161425 : Nat := 4983230072969 + 3 ^ 40 * 2161425 * 2
def baseEnd_2161425 : Nat := 1109849923644311148447293

theorem tailTrace_2161425 : CollatzResearch.WordTrace tailWord_2161425 prefixEnd_2161425 1109849923644311148447293 := by
  unfold tailWord_2161425
  simp only [CollatzResearch.WordTrace]
  refine ⟨78833646194533841846213729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52555764129689227897475819 78833646194533841846213729)
  ·
    refine ⟨59125234645900381384660297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78833646194533841846213729 59125234645900381384660297)
    ·
      refine ⟨44343925984425286038495223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59125234645900381384660297 44343925984425286038495223)
      ·
        refine ⟨66515888976637929057742835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44343925984425286038495223 66515888976637929057742835)
        ·
          refine ⟨99773833464956893586614253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66515888976637929057742835 99773833464956893586614253)
          ·
            refine ⟨37415187549358835094980345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99773833464956893586614253 37415187549358835094980345)
            ·
              refine ⟨28061390662019126321235259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37415187549358835094980345 28061390662019126321235259)
              ·
                refine ⟨42092085993028689481852889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28061390662019126321235259 42092085993028689481852889)
                ·
                  refine ⟨31569064494771517111389667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42092085993028689481852889 31569064494771517111389667)
                  ·
                    refine ⟨47353596742157275667084501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31569064494771517111389667 47353596742157275667084501)
                    ·
                      refine ⟨1109849923644311148447293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47353596742157275667084501 1109849923644311148447293)
                      ·
                        rfl

theorem cell23_2161425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2161425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161425 prefixEnd_2161425 := by exact prefixLift 2161425
  have htrace : WordTrace (prefixWord ++ tailWord_2161425) baseStart_2161425 baseEnd_2161425 := by
    simpa [prefixWord, tailWord_2161425, baseEnd_2161425] using wordTrace_append hprefix tailTrace_2161425
  have hstable : (prefixWord ++ tailWord_2161425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161425).length < 2 ^ (prefixWord ++ tailWord_2161425).sum := by decide
  have hdescent : baseEnd_2161425 < baseStart_2161425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161429 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_2161429 : Nat := 118140960795 + 2161429 * 2 ^ 59
def prefixEnd_2161429 : Nat := 4983230072969 + 3 ^ 40 * 2161429 * 2
def baseEnd_2161429 : Nat := 1109851977566929132797275

theorem tailTrace_2161429 : CollatzResearch.WordTrace tailWord_2161429 prefixEnd_2161429 1109851977566929132797275 := by
  unfold tailWord_2161429
  simp only [CollatzResearch.WordTrace]
  refine ⟨78833792086519350529359341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52555861391012900352906227 78833792086519350529359341)
  ·
    refine ⟨29562672032444756448509753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78833792086519350529359341 29562672032444756448509753)
    ·
      refine ⟨22172004024333567336382315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29562672032444756448509753 22172004024333567336382315)
      ·
        refine ⟨33258006036500351004573473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22172004024333567336382315 33258006036500351004573473)
        ·
          refine ⟨24943504527375263253430105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33258006036500351004573473 24943504527375263253430105)
          ·
            refine ⟨18707628395531447440072579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24943504527375263253430105 18707628395531447440072579)
            ·
              refine ⟨28061442593297171160108869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18707628395531447440072579 28061442593297171160108869)
              ·
                refine ⟨5261520486243219592520413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28061442593297171160108869 5261520486243219592520413)
                ·
                  refine ⟨1973070182341207347195155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5261520486243219592520413 1973070182341207347195155)
                  ·
                    refine ⟨2959605273511811020792733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973070182341207347195155 2959605273511811020792733)
                    ·
                      refine ⟨1109851977566929132797275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959605273511811020792733 1109851977566929132797275)
                      ·
                        rfl

theorem cell23_2161429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_2161429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161429 prefixEnd_2161429 := by exact prefixLift 2161429
  have htrace : WordTrace (prefixWord ++ tailWord_2161429) baseStart_2161429 baseEnd_2161429 := by
    simpa [prefixWord, tailWord_2161429, baseEnd_2161429] using wordTrace_append hprefix tailTrace_2161429
  have hstable : (prefixWord ++ tailWord_2161429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161429).length < 2 ^ (prefixWord ++ tailWord_2161429).sum := by decide
  have hdescent : baseEnd_2161429 < baseStart_2161429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161439 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 1, 5, 2]
def baseStart_2161439 : Nat := 118140960795 + 2161439 * 2 ^ 59
def prefixEnd_2161439 : Nat := 4983230072969 + 3 ^ 40 * 2161439 * 2
def baseEnd_2161439 : Nat := 1109857112373474093672229

theorem tailTrace_2161439 : CollatzResearch.WordTrace tailWord_2161439 prefixEnd_2161439 1109857112373474093672229 := by
  unfold tailWord_2161439
  simp only [CollatzResearch.WordTrace]
  refine ⟨78834156816483122237223371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52556104544322081491482247 78834156816483122237223371)
  ·
    refine ⟨118251235224724683355835057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78834156816483122237223371 118251235224724683355835057)
    ·
      refine ⟨88688426418543512516876293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118251235224724683355835057 88688426418543512516876293)
      ·
        refine ⟨16629079953476908596914305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88688426418543512516876293 16629079953476908596914305)
        ·
          refine ⟨12471809965107681447685729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16629079953476908596914305 12471809965107681447685729)
          ·
            refine ⟨9353857473830761085764297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12471809965107681447685729 9353857473830761085764297)
            ·
              refine ⟨7015393105373070814323223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9353857473830761085764297 7015393105373070814323223)
              ·
                refine ⟨10523089658059606221484835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7015393105373070814323223 10523089658059606221484835)
                ·
                  refine ⟨15784634487089409332227253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10523089658059606221484835 15784634487089409332227253)
                  ·
                    refine ⟨1479809483164632124896305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15784634487089409332227253 1479809483164632124896305)
                    ·
                      refine ⟨1109857112373474093672229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479809483164632124896305 1109857112373474093672229)
                      ·
                        rfl

theorem cell23_2161439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_2161439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161439 prefixEnd_2161439 := by exact prefixLift 2161439
  have htrace : WordTrace (prefixWord ++ tailWord_2161439) baseStart_2161439 baseEnd_2161439 := by
    simpa [prefixWord, tailWord_2161439, baseEnd_2161439] using wordTrace_append hprefix tailTrace_2161439
  have hstable : (prefixWord ++ tailWord_2161439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161439).length < 2 ^ (prefixWord ++ tailWord_2161439).sum := by decide
  have hdescent : baseEnd_2161439 < baseStart_2161439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161463 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 1, 1, 3]
def baseStart_2161463 : Nat := 118140960795 + 2161463 * 2 ^ 59
def prefixEnd_2161463 : Nat := 4983230072969 + 3 ^ 40 * 2161463 * 2
def baseEnd_2161463 : Nat := 1109869435909181999772119

theorem tailTrace_2161463 : CollatzResearch.WordTrace tailWord_2161463 prefixEnd_2161463 1109869435909181999772119 := by
  unfold tailWord_2161463
  simp only [CollatzResearch.WordTrace]
  refine ⟨78835032168396174336097043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52556688112264116224064695 78835032168396174336097043)
  ·
    refine ⟨118252548252594261504145565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78835032168396174336097043 118252548252594261504145565)
    ·
      refine ⟨44344705594722848064054587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118252548252594261504145565 44344705594722848064054587)
      ·
        refine ⟨66517058392084272096081881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44344705594722848064054587 66517058392084272096081881)
        ·
          refine ⟨49887793794063204072061411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66517058392084272096081881 49887793794063204072061411)
          ·
            refine ⟨74831690691094806108092117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49887793794063204072061411 74831690691094806108092117)
            ·
              refine ⟨1753867750572534518158409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74831690691094806108092117 1753867750572534518158409)
              ·
                refine ⟨1315400812929400888618807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753867750572534518158409 1315400812929400888618807)
                ·
                  refine ⟨1973101219394101332928211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315400812929400888618807 1973101219394101332928211)
                  ·
                    refine ⟨2959651829091151999392317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973101219394101332928211 2959651829091151999392317)
                    ·
                      refine ⟨1109869435909181999772119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959651829091151999392317 1109869435909181999772119)
                      ·
                        rfl

theorem cell23_2161463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_2161463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161463 prefixEnd_2161463 := by exact prefixLift 2161463
  have htrace : WordTrace (prefixWord ++ tailWord_2161463) baseStart_2161463 baseEnd_2161463 := by
    simpa [prefixWord, tailWord_2161463, baseEnd_2161463] using wordTrace_append hprefix tailTrace_2161463
  have hstable : (prefixWord ++ tailWord_2161463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161463).length < 2 ^ (prefixWord ++ tailWord_2161463).sum := by decide
  have hdescent : baseEnd_2161463 < baseStart_2161463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161486 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_2161486 : Nat := 118140960795 + 2161486 * 2 ^ 59
def prefixEnd_2161486 : Nat := 4983230072969 + 3 ^ 40 * 2161486 * 2
def baseEnd_2161486 : Nat := 1109881245964235409784513

theorem tailTrace_2161486 : CollatzResearch.WordTrace tailWord_2161486 prefixEnd_2161486 1109881245964235409784513 := by
  unfold tailWord_2161486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854483880914106158023039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52557247364875232842789541 9854483880914106158023039)
  ·
    refine ⟨14781725821371159237034559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9854483880914106158023039 14781725821371159237034559)
    ·
      refine ⟨22172588732056738855551839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14781725821371159237034559 22172588732056738855551839)
      ·
        refine ⟨33258883098085108283327759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22172588732056738855551839 33258883098085108283327759)
        ·
          refine ⟨49888324647127662424991639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33258883098085108283327759 49888324647127662424991639)
          ·
            refine ⟨74832486970691493637487459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49888324647127662424991639 74832486970691493637487459)
            ·
              refine ⟨112248730456037240456231189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74832486970691493637487459 112248730456037240456231189)
              ·
                refine ⟨5261659240126745646385837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112248730456037240456231189 5261659240126745646385837)
                ·
                  refine ⟨1973122215047529617394689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5261659240126745646385837 1973122215047529617394689)
                  ·
                    refine ⟨1479841661285647213046017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1973122215047529617394689 1479841661285647213046017)
                    ·
                      refine ⟨1109881245964235409784513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479841661285647213046017 1109881245964235409784513)
                      ·
                        rfl

theorem cell23_2161486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_2161486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161486 prefixEnd_2161486 := by exact prefixLift 2161486
  have htrace : WordTrace (prefixWord ++ tailWord_2161486) baseStart_2161486 baseEnd_2161486 := by
    simpa [prefixWord, tailWord_2161486, baseEnd_2161486] using wordTrace_append hprefix tailTrace_2161486
  have hstable : (prefixWord ++ tailWord_2161486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161486).length < 2 ^ (prefixWord ++ tailWord_2161486).sum := by decide
  have hdescent : baseEnd_2161486 < baseStart_2161486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161503 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 1, 2, 2]
def baseStart_2161503 : Nat := 118140960795 + 2161503 * 2 ^ 59
def prefixEnd_2161503 : Nat := 4983230072969 + 3 ^ 40 * 2161503 * 2
def baseEnd_2161503 : Nat := 1109889975135361843271935

theorem tailTrace_2161503 : CollatzResearch.WordTrace tailWord_2161503 prefixEnd_2161503 1109889975135361843271935 := by
  unfold tailWord_2161503
  simp only [CollatzResearch.WordTrace]
  refine ⟨78836491088251261167553163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52557660725500840778368775 78836491088251261167553163)
  ·
    refine ⟨118254736632376891751329745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78836491088251261167553163 118254736632376891751329745)
    ·
      refine ⟨88691052474282668813497309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118254736632376891751329745 88691052474282668813497309)
      ·
        refine ⟨33259144677856000805061491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88691052474282668813497309 33259144677856000805061491)
        ·
          refine ⟨49888717016784001207592237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33259144677856000805061491 49888717016784001207592237)
          ·
            refine ⟨18708268881294000452847089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49888717016784001207592237 18708268881294000452847089)
            ·
              refine ⟨14031201660970500339635317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18708268881294000452847089 14031201660970500339635317)
              ·
                refine ⟨1315425155715984406840811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14031201660970500339635317 1315425155715984406840811)
                ·
                  refine ⟨1973137733573976610261217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315425155715984406840811 1973137733573976610261217)
                  ·
                    refine ⟨1479853300180482457695913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1973137733573976610261217 1479853300180482457695913)
                    ·
                      refine ⟨1109889975135361843271935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479853300180482457695913 1109889975135361843271935)
                      ·
                        rfl

theorem cell23_2161503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_2161503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161503 prefixEnd_2161503 := by exact prefixLift 2161503
  have htrace : WordTrace (prefixWord ++ tailWord_2161503) baseStart_2161503 baseEnd_2161503 := by
    simpa [prefixWord, tailWord_2161503, baseEnd_2161503] using wordTrace_append hprefix tailTrace_2161503
  have hstable : (prefixWord ++ tailWord_2161503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161503).length < 2 ^ (prefixWord ++ tailWord_2161503).sum := by decide
  have hdescent : baseEnd_2161503 < baseStart_2161503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161519 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 3]
def baseStart_2161519 : Nat := 118140960795 + 2161519 * 2 ^ 59
def prefixEnd_2161519 : Nat := 4983230072969 + 3 ^ 40 * 2161519 * 2
def baseEnd_2161519 : Nat := 1109898190825833780671861

theorem tailTrace_2161519 : CollatzResearch.WordTrace tailWord_2161519 prefixEnd_2161519 1109898190825833780671861 := by
  unfold tailWord_2161519
  simp only [CollatzResearch.WordTrace]
  refine ⟨78837074656193295900135611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52558049770795530600090407 78837074656193295900135611)
  ·
    refine ⟨118255611984289943850203417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78837074656193295900135611 118255611984289943850203417)
    ·
      refine ⟨88691708988217457887652563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118255611984289943850203417 88691708988217457887652563)
      ·
        refine ⟨133037563482326186831478845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88691708988217457887652563 133037563482326186831478845)
        ·
          refine ⟨49889086305872320061804567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133037563482326186831478845 49889086305872320061804567)
          ·
            refine ⟨74833629458808480092706851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49889086305872320061804567 74833629458808480092706851)
            ·
              refine ⟨112250444188212720139060277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74833629458808480092706851 112250444188212720139060277)
              ·
                refine ⟨10523479142644942513036901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112250444188212720139060277 10523479142644942513036901)
                ·
                  refine ⟨1973152339245926721194419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10523479142644942513036901 1973152339245926721194419)
                  ·
                    refine ⟨2959728508868890081791629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973152339245926721194419 2959728508868890081791629)
                    ·
                      refine ⟨1109898190825833780671861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959728508868890081791629 1109898190825833780671861)
                      ·
                        rfl

theorem cell23_2161519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_2161519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161519 prefixEnd_2161519 := by exact prefixLift 2161519
  have htrace : WordTrace (prefixWord ++ tailWord_2161519) baseStart_2161519 baseEnd_2161519 := by
    simpa [prefixWord, tailWord_2161519, baseEnd_2161519] using wordTrace_append hprefix tailTrace_2161519
  have hstable : (prefixWord ++ tailWord_2161519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161519).length < 2 ^ (prefixWord ++ tailWord_2161519).sum := by decide
  have hdescent : baseEnd_2161519 < baseStart_2161519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161520 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 1, 2, 2]
def baseStart_2161520 : Nat := 118140960795 + 2161520 * 2 ^ 59
def prefixEnd_2161520 : Nat := 4983230072969 + 3 ^ 40 * 2161520 * 2
def baseEnd_2161520 : Nat := 1109898704306488276759357

theorem tailTrace_2161520 : CollatzResearch.WordTrace tailWord_2161520 prefixEnd_2161520 1109898704306488276759357 := by
  unfold tailWord_2161520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39418555564594836535461007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52558074086126448713948009 39418555564594836535461007)
  ·
    refine ⟨59127833346892254803191511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39418555564594836535461007 59127833346892254803191511)
    ·
      refine ⟨88691750020338382204787267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59127833346892254803191511 88691750020338382204787267)
      ·
        refine ⟨133037625030507573307180901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88691750020338382204787267 133037625030507573307180901)
        ·
          refine ⟨24944554693220169995096419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133037625030507573307180901 24944554693220169995096419)
          ·
            refine ⟨37416832039830254992644629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24944554693220169995096419 37416832039830254992644629)
            ·
              refine ⟨1753914001867043202780217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37416832039830254992644629 1753914001867043202780217)
              ·
                refine ⟨1315435501400282402085163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753914001867043202780217 1315435501400282402085163)
                ·
                  refine ⟨1973153252100423603127745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315435501400282402085163 1973153252100423603127745)
                  ·
                    refine ⟨1479864939075317702345809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1973153252100423603127745 1479864939075317702345809)
                    ·
                      refine ⟨1109898704306488276759357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479864939075317702345809 1109898704306488276759357)
                      ·
                        rfl

theorem cell23_2161520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 2, 2].length) (baseStart_2161520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161520 prefixEnd_2161520 := by exact prefixLift 2161520
  have htrace : WordTrace (prefixWord ++ tailWord_2161520) baseStart_2161520 baseEnd_2161520 := by
    simpa [prefixWord, tailWord_2161520, baseEnd_2161520] using wordTrace_append hprefix tailTrace_2161520
  have hstable : (prefixWord ++ tailWord_2161520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161520).length < 2 ^ (prefixWord ++ tailWord_2161520).sum := by decide
  have hdescent : baseEnd_2161520 < baseStart_2161520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161522 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_2161522 : Nat := 118140960795 + 2161522 * 2 ^ 59
def prefixEnd_2161522 : Nat := 4983230072969 + 3 ^ 40 * 2161522 * 2
def baseEnd_2161522 : Nat := 369966577089265756311449

theorem tailTrace_2161522 : CollatzResearch.WordTrace tailWord_2161522 prefixEnd_2161522 369966577089265756311449 := by
  unfold tailWord_2161522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19709296018795606853123705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52558122716788284941663213 19709296018795606853123705)
  ·
    refine ⟨14781972014096705139842779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19709296018795606853123705 14781972014096705139842779)
    ·
      refine ⟨22172958021145057709764169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14781972014096705139842779 22172958021145057709764169)
      ·
        refine ⟨16629718515858793282323127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22172958021145057709764169 16629718515858793282323127)
        ·
          refine ⟨24944577773788189923484691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16629718515858793282323127 24944577773788189923484691)
          ·
            refine ⟨37416866660682284885227037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24944577773788189923484691 37416866660682284885227037)
            ·
              refine ⟨14031324997755856831960139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37416866660682284885227037 14031324997755856831960139)
              ·
                refine ⟨21046987496633785247940209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14031324997755856831960139 21046987496633785247940209)
                ·
                  refine ⟨15785240622475338935955157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21046987496633785247940209 15785240622475338935955157)
                  ·
                    refine ⟨369966577089265756311449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15785240622475338935955157 369966577089265756311449)
                    ·
                      rfl

theorem cell23_2161522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_2161522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161522 prefixEnd_2161522 := by exact prefixLift 2161522
  have htrace : WordTrace (prefixWord ++ tailWord_2161522) baseStart_2161522 baseEnd_2161522 := by
    simpa [prefixWord, tailWord_2161522, baseEnd_2161522] using wordTrace_append hprefix tailTrace_2161522
  have hstable : (prefixWord ++ tailWord_2161522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161522).length < 2 ^ (prefixWord ++ tailWord_2161522).sum := by decide
  have hdescent : baseEnd_2161522 < baseStart_2161522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161526 : List Nat := [5, 1, 1, 3, 1, 3, 1, 8]
def baseStart_2161526 : Nat := 118140960795 + 2161526 * 2 ^ 59
def prefixEnd_2161526 : Nat := 4983230072969 + 3 ^ 40 * 2161526 * 2
def baseEnd_2161526 : Nat := 41107473525570935306827

theorem tailTrace_2161526 : CollatzResearch.WordTrace tailWord_2161526 prefixEnd_2161526 41107473525570935306827 := by
  unfold tailWord_2161526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927333122947996005977527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52558219978111957397093621 4927333122947996005977527)
  ·
    refine ⟨7390999684421994008966291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4927333122947996005977527 7390999684421994008966291)
    ·
      refine ⟨11086499526632991013449437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7390999684421994008966291 11086499526632991013449437)
      ·
        refine ⟨4157437322487371630043539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11086499526632991013449437 4157437322487371630043539)
        ·
          refine ⟨6236155983731057445065309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4157437322487371630043539 6236155983731057445065309)
          ·
            refine ⟨2338558493899146541899491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6236155983731057445065309 2338558493899146541899491)
            ·
              refine ⟨3507837740848719812849237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338558493899146541899491 3507837740848719812849237)
              ·
                refine ⟨41107473525570935306827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3507837740848719812849237 41107473525570935306827)
                ·
                  rfl

theorem cell23_2161526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_2161526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161526 prefixEnd_2161526 := by exact prefixLift 2161526
  have htrace : WordTrace (prefixWord ++ tailWord_2161526) baseStart_2161526 baseEnd_2161526 := by
    simpa [prefixWord, tailWord_2161526, baseEnd_2161526] using wordTrace_append hprefix tailTrace_2161526
  have hstable : (prefixWord ++ tailWord_2161526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161526).length < 2 ^ (prefixWord ++ tailWord_2161526).sum := by decide
  have hdescent : baseEnd_2161526 < baseStart_2161526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161569 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2161569 : Nat := 118140960795 + 2161569 * 2 ^ 59
def prefixEnd_2161569 : Nat := 4983230072969 + 3 ^ 40 * 2161569 * 2
def baseEnd_2161569 : Nat := 369974621619519528348877

theorem tailTrace_2161569 : CollatzResearch.WordTrace tailWord_2161569 prefixEnd_2161569 369974621619519528348877 := by
  unfold tailWord_2161569
  simp only [CollatzResearch.WordTrace]
  refine ⟨78838898306012154439455761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52559265537341436292970507 78838898306012154439455761)
  ·
    refine ⟨59129173729509115829591821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78838898306012154439455761 59129173729509115829591821)
    ·
      refine ⟨22173440148565918436096933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59129173729509115829591821 22173440148565918436096933)
      ·
        refine ⟨4157520027856109706768175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22173440148565918436096933 4157520027856109706768175)
        ·
          refine ⟨6236280041784164560152263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4157520027856109706768175 6236280041784164560152263)
          ·
            refine ⟨9354420062676246840228395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6236280041784164560152263 9354420062676246840228395)
            ·
              refine ⟨14031630094014370260342593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9354420062676246840228395 14031630094014370260342593)
              ·
                refine ⟨10523722570510777695256945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14031630094014370260342593 10523722570510777695256945)
                ·
                  refine ⟨7892791927883083271442709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10523722570510777695256945 7892791927883083271442709)
                  ·
                    refine ⟨369974621619519528348877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7892791927883083271442709 369974621619519528348877)
                    ·
                      rfl

theorem cell23_2161569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2161569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161569 prefixEnd_2161569 := by exact prefixLift 2161569
  have htrace : WordTrace (prefixWord ++ tailWord_2161569) baseStart_2161569 baseEnd_2161569 := by
    simpa [prefixWord, tailWord_2161569, baseEnd_2161569] using wordTrace_append hprefix tailTrace_2161569
  have hstable : (prefixWord ++ tailWord_2161569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161569).length < 2 ^ (prefixWord ++ tailWord_2161569).sum := by decide
  have hdescent : baseEnd_2161569 < baseStart_2161569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161570 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2161570 : Nat := 118140960795 + 2161570 * 2 ^ 59
def prefixEnd_2161570 : Nat := 4983230072969 + 3 ^ 40 * 2161570 * 2
def baseEnd_2161570 : Nat := 1109924378339213081134127

theorem tailTrace_2161570 : CollatzResearch.WordTrace tailWord_2161570 prefixEnd_2161570 1109924378339213081134127 := by
  unfold tailWord_2161570
  simp only [CollatzResearch.WordTrace]
  refine ⟨19709733694752132902560541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52559289852672354406828109 19709733694752132902560541)
  ·
    refine ⟨7391150135532049838460203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19709733694752132902560541 7391150135532049838460203)
    ·
      refine ⟨11086725203298074757690305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7391150135532049838460203 11086725203298074757690305)
      ·
        refine ⟨8315043902473556068267729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11086725203298074757690305 8315043902473556068267729)
        ·
          refine ⟨6236282926855167051200797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8315043902473556068267729 6236282926855167051200797)
          ·
            refine ⟨2338606097570687644200299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6236282926855167051200797 2338606097570687644200299)
            ·
              refine ⟨3507909146356031466300449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338606097570687644200299 3507909146356031466300449)
              ·
                refine ⟨2630931859767023599725337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507909146356031466300449 2630931859767023599725337)
                ·
                  refine ⟨1973198894825267699794003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2630931859767023599725337 1973198894825267699794003)
                  ·
                    refine ⟨2959798342237901549691005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973198894825267699794003 2959798342237901549691005)
                    ·
                      refine ⟨1109924378339213081134127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2959798342237901549691005 1109924378339213081134127)
                      ·
                        rfl

theorem cell23_2161570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2161570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161570 prefixEnd_2161570 := by exact prefixLift 2161570
  have htrace : WordTrace (prefixWord ++ tailWord_2161570) baseStart_2161570 baseEnd_2161570 := by
    simpa [prefixWord, tailWord_2161570, baseEnd_2161570] using wordTrace_append hprefix tailTrace_2161570
  have hstable : (prefixWord ++ tailWord_2161570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161570).length < 2 ^ (prefixWord ++ tailWord_2161570).sum := by decide
  have hdescent : baseEnd_2161570 < baseStart_2161570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161589 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2161589 : Nat := 118140960795 + 2161589 * 2 ^ 59
def prefixEnd_2161589 : Nat := 4983230072969 + 3 ^ 40 * 2161589 * 2
def baseEnd_2161589 : Nat := 1109934134471648506796539

theorem tailTrace_2161589 : CollatzResearch.WordTrace tailWord_2161589 prefixEnd_2161589 1109934134471648506796539 := by
  unfold tailWord_2161589
  simp only [CollatzResearch.WordTrace]
  refine ⟨78839627765939697855183821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52559751843959798570122547 78839627765939697855183821)
  ·
    refine ⟨29564860412227386695693933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78839627765939697855183821 29564860412227386695693933)
    ·
      refine ⟨11086822654585270010885225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29564860412227386695693933 11086822654585270010885225)
      ·
        refine ⟨8315116990938952508163919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11086822654585270010885225 8315116990938952508163919)
        ·
          refine ⟨12472675486408428762245879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8315116990938952508163919 12472675486408428762245879)
          ·
            refine ⟨18709013229612643143368819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12472675486408428762245879 18709013229612643143368819)
            ·
              refine ⟨28063519844418964715053229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18709013229612643143368819 28063519844418964715053229)
              ·
                refine ⟨10523819941657111768144961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28063519844418964715053229 10523819941657111768144961)
                ·
                  refine ⟨7892864956242833826108721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10523819941657111768144961 7892864956242833826108721)
                  ·
                    refine ⟨5919648717182125369581541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7892864956242833826108721 5919648717182125369581541)
                    ·
                      refine ⟨1109934134471648506796539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5919648717182125369581541 1109934134471648506796539)
                      ·
                        rfl

theorem cell23_2161589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2161589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161589 prefixEnd_2161589 := by exact prefixLift 2161589
  have htrace : WordTrace (prefixWord ++ tailWord_2161589) baseStart_2161589 baseEnd_2161589 := by
    simpa [prefixWord, tailWord_2161589, baseEnd_2161589] using wordTrace_append hprefix tailTrace_2161589
  have hstable : (prefixWord ++ tailWord_2161589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161589).length < 2 ^ (prefixWord ++ tailWord_2161589).sum := by decide
  have hdescent : baseEnd_2161589 < baseStart_2161589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161593 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 1, 4, 2]
def baseStart_2161593 : Nat := 118140960795 + 2161593 * 2 ^ 59
def prefixEnd_2161593 : Nat := 4983230072969 + 3 ^ 40 * 2161593 * 2
def baseEnd_2161593 : Nat := 1109936188394266491146521

theorem tailTrace_2161593 : CollatzResearch.WordTrace tailWord_2161593 prefixEnd_2161593 1109936188394266491146521 := by
  unfold tailWord_2161593
  simp only [CollatzResearch.WordTrace]
  refine ⟨78839773657925206538329433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52559849105283471025552955 78839773657925206538329433)
  ·
    refine ⟨59129830243443904903747075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78839773657925206538329433 59129830243443904903747075)
    ·
      refine ⟨88694745365165857355620613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59129830243443904903747075 88694745365165857355620613)
      ·
        refine ⟨16630264755968598254178865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88694745365165857355620613 16630264755968598254178865)
        ·
          refine ⟨12472698566976448690634149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16630264755968598254178865 12472698566976448690634149)
          ·
            refine ⟨2338630981308084129493903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12472698566976448690634149 2338630981308084129493903)
            ·
              refine ⟨3507946471962126194240855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338630981308084129493903 3507946471962126194240855)
              ·
                refine ⟨5261919707943189291361283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507946471962126194240855 5261919707943189291361283)
                ·
                  refine ⟨7892879561914783937041925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5261919707943189291361283 7892879561914783937041925)
                  ·
                    refine ⟨1479914917859021988195361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7892879561914783937041925 1479914917859021988195361)
                    ·
                      refine ⟨1109936188394266491146521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1479914917859021988195361 1109936188394266491146521)
                      ·
                        rfl

theorem cell23_2161593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_2161593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161593 prefixEnd_2161593 := by exact prefixLift 2161593
  have htrace : WordTrace (prefixWord ++ tailWord_2161593) baseStart_2161593 baseEnd_2161593 := by
    simpa [prefixWord, tailWord_2161593, baseEnd_2161593] using wordTrace_append hprefix tailTrace_2161593
  have hstable : (prefixWord ++ tailWord_2161593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161593).length < 2 ^ (prefixWord ++ tailWord_2161593).sum := by decide
  have hdescent : baseEnd_2161593 < baseStart_2161593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161632 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2161632 : Nat := 118140960795 + 2161632 * 2 ^ 59
def prefixEnd_2161632 : Nat := 4983230072969 + 3 ^ 40 * 2161632 * 2
def baseEnd_2161632 : Nat := 1109956214139791838558841

theorem tailTrace_2161632 : CollatzResearch.WordTrace tailWord_2161632 prefixEnd_2161632 1109956214139791838558841 := by
  unfold tailWord_2161632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39420598052391958099499575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52560797403189277465999433 39420598052391958099499575)
  ·
    refine ⟨59130897078587937149249363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39420598052391958099499575 59130897078587937149249363)
    ·
      refine ⟨88696345617881905723874045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59130897078587937149249363 88696345617881905723874045)
      ·
        refine ⟨33261129606705714646452767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88696345617881905723874045 33261129606705714646452767)
        ·
          refine ⟨49891694410058571969679151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33261129606705714646452767 49891694410058571969679151)
          ·
            refine ⟨74837541615087857954518727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49891694410058571969679151 74837541615087857954518727)
            ·
              refine ⟨112256312422631786931778091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74837541615087857954518727 112256312422631786931778091)
              ·
                refine ⟨168384468633947680397667137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112256312422631786931778091 168384468633947680397667137)
                ·
                  refine ⟨126288351475460760298250353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168384468633947680397667137 126288351475460760298250353)
                  ·
                    refine ⟨94716263606595570223687765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126288351475460760298250353 94716263606595570223687765)
                    ·
                      refine ⟨1109956214139791838558841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94716263606595570223687765 1109956214139791838558841)
                      ·
                        rfl

theorem cell23_2161632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2161632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161632 prefixEnd_2161632 := by exact prefixLift 2161632
  have htrace : WordTrace (prefixWord ++ tailWord_2161632) baseStart_2161632 baseEnd_2161632 := by
    simpa [prefixWord, tailWord_2161632, baseEnd_2161632] using wordTrace_append hprefix tailTrace_2161632
  have hstable : (prefixWord ++ tailWord_2161632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161632).length < 2 ^ (prefixWord ++ tailWord_2161632).sum := by decide
  have hdescent : baseEnd_2161632 < baseStart_2161632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161639 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2161639 : Nat := 118140960795 + 2161639 * 2 ^ 59
def prefixEnd_2161639 : Nat := 4983230072969 + 3 ^ 40 * 2161639 * 2
def baseEnd_2161639 : Nat := 1109959808504373311171309

theorem tailTrace_2161639 : CollatzResearch.WordTrace tailWord_2161639 prefixEnd_2161639 1109959808504373311171309 := by
  unfold tailWord_2161639
  simp only [CollatzResearch.WordTrace]
  refine ⟨78841451415758556394503971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52560967610505704263002647 78841451415758556394503971)
  ·
    refine ⟨118262177123637834591755957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78841451415758556394503971 118262177123637834591755957)
    ·
      refine ⟨11087079105341046992977121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118262177123637834591755957 11087079105341046992977121)
      ·
        refine ⟨8315309329005785244732841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11087079105341046992977121 8315309329005785244732841)
        ·
          refine ⟨6236481996754338933549631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8315309329005785244732841 6236481996754338933549631)
          ·
            refine ⟨9354722995131508400324447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6236481996754338933549631 9354722995131508400324447)
            ·
              refine ⟨14032084492697262600486671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9354722995131508400324447 14032084492697262600486671)
              ·
                refine ⟨21048126739045893900730007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14032084492697262600486671 21048126739045893900730007)
                ·
                  refine ⟨31572190108568840851095011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21048126739045893900730007 31572190108568840851095011)
                  ·
                    refine ⟨47358285162853261276642517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31572190108568840851095011 47358285162853261276642517)
                    ·
                      refine ⟨1109959808504373311171309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47358285162853261276642517 1109959808504373311171309)
                      ·
                        rfl

theorem cell23_2161639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2161639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161639 prefixEnd_2161639 := by exact prefixLift 2161639
  have htrace : WordTrace (prefixWord ++ tailWord_2161639) baseStart_2161639 baseEnd_2161639 := by
    simpa [prefixWord, tailWord_2161639, baseEnd_2161639] using wordTrace_append hprefix tailTrace_2161639
  have hstable : (prefixWord ++ tailWord_2161639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161639).length < 2 ^ (prefixWord ++ tailWord_2161639).sum := by decide
  have hdescent : baseEnd_2161639 < baseStart_2161639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161659 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 5, 4]
def baseStart_2161659 : Nat := 118140960795 + 2161659 * 2 ^ 59
def prefixEnd_2161659 : Nat := 4983230072969 + 3 ^ 40 * 2161659 * 2
def baseEnd_2161659 : Nat := 369990026039154410973739

theorem tailTrace_2161659 : CollatzResearch.WordTrace tailWord_2161659 prefixEnd_2161659 369990026039154410973739 := by
  unfold tailWord_2161659
  simp only [CollatzResearch.WordTrace]
  refine ⟨78842180875686099810232031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52561453917124066540154687 78842180875686099810232031)
  ·
    refine ⟨118263271313529149715348047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78842180875686099810232031 118263271313529149715348047)
    ·
      refine ⟨177394906970293724573022071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118263271313529149715348047 177394906970293724573022071)
      ·
        refine ⟨266092360455440586859533107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177394906970293724573022071 266092360455440586859533107)
        ·
          refine ⟨399138540683160880289299661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266092360455440586859533107 399138540683160880289299661)
          ·
            refine ⟨149676952756185330108487373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 399138540683160880289299661 149676952756185330108487373)
            ·
              refine ⟨56128857283569498790682765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149676952756185330108487373 56128857283569498790682765)
              ·
                refine ⟨21048321481338562046506037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56128857283569498790682765 21048321481338562046506037)
                ·
                  refine ⟨1973280138875490191859941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21048321481338562046506037 1973280138875490191859941)
                  ·
                    refine ⟨369990026039154410973739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1973280138875490191859941 369990026039154410973739)
                    ·
                      rfl

theorem cell23_2161659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 4].length) (baseStart_2161659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161659 prefixEnd_2161659 := by exact prefixLift 2161659
  have htrace : WordTrace (prefixWord ++ tailWord_2161659) baseStart_2161659 baseEnd_2161659 := by
    simpa [prefixWord, tailWord_2161659, baseEnd_2161659] using wordTrace_append hprefix tailTrace_2161659
  have hstable : (prefixWord ++ tailWord_2161659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161659).length < 2 ^ (prefixWord ++ tailWord_2161659).sum := by decide
  have hdescent : baseEnd_2161659 < baseStart_2161659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161689 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 6]
def baseStart_2161689 : Nat := 118140960795 + 2161689 * 2 ^ 59
def prefixEnd_2161689 : Nat := 4983230072969 + 3 ^ 40 * 2161689 * 2
def baseEnd_2161689 : Nat := 123331720281899790616231

theorem tailTrace_2161689 : CollatzResearch.WordTrace tailWord_2161689 prefixEnd_2161689 123331720281899790616231 := by
  unfold tailWord_2161689
  simp only [CollatzResearch.WordTrace]
  refine ⟨78843275065577414933824121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52562183377051609955882747 78843275065577414933824121)
  ·
    refine ⟨59132456299183061200368091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78843275065577414933824121 59132456299183061200368091)
    ·
      refine ⟨88698684448774591800552137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59132456299183061200368091 88698684448774591800552137)
      ·
        refine ⟨66524013336580943850414103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88698684448774591800552137 66524013336580943850414103)
        ·
          refine ⟨99786020004871415775621155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66524013336580943850414103 99786020004871415775621155)
          ·
            refine ⟨149679030007307123663431733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99786020004871415775621155 149679030007307123663431733)
            ·
              refine ⟨14032409063185042843446725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149679030007307123663431733 14032409063185042843446725)
              ·
                refine ⟨2631076699347195533146261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14032409063185042843446725 2631076699347195533146261)
                ·
                  refine ⟨123331720281899790616231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2631076699347195533146261 123331720281899790616231)
                  ·
                    rfl

theorem cell23_2161689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_2161689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161689 prefixEnd_2161689 := by exact prefixLift 2161689
  have htrace : WordTrace (prefixWord ++ tailWord_2161689) baseStart_2161689 baseEnd_2161689 := by
    simpa [prefixWord, tailWord_2161689, baseEnd_2161689] using wordTrace_append hprefix tailTrace_2161689
  have hstable : (prefixWord ++ tailWord_2161689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161689).length < 2 ^ (prefixWord ++ tailWord_2161689).sum := by decide
  have hdescent : baseEnd_2161689 < baseStart_2161689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161736 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 1, 5]
def baseStart_2161736 : Nat := 118140960795 + 2161736 * 2 ^ 59
def prefixEnd_2161736 : Nat := 4983230072969 + 3 ^ 40 * 2161736 * 2
def baseEnd_2161736 : Nat := 370003205375953143886121

theorem tailTrace_2161736 : CollatzResearch.WordTrace tailWord_2161736 prefixEnd_2161736 370003205375953143886121 := by
  unfold tailWord_2161736
  simp only [CollatzResearch.WordTrace]
  refine ⟨39422494648203570980392531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52563326197604761307190041 39422494648203570980392531)
  ·
    refine ⟨59133741972305356470588797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39422494648203570980392531 59133741972305356470588797)
    ·
      refine ⟨22175153239614508676470799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59133741972305356470588797 22175153239614508676470799)
      ·
        refine ⟨33262729859421763014706199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22175153239614508676470799 33262729859421763014706199)
        ·
          refine ⟨49894094789132644522059299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33262729859421763014706199 49894094789132644522059299)
          ·
            refine ⟨74841142183698966783088949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49894094789132644522059299 74841142183698966783088949)
            ·
              refine ⟨7016357079721778135914589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74841142183698966783088949 7016357079721778135914589)
              ·
                refine ⟨2631133904895666800967971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7016357079721778135914589 2631133904895666800967971)
                ·
                  refine ⟨3946700857343500201451957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631133904895666800967971 3946700857343500201451957)
                  ·
                    refine ⟨370003205375953143886121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3946700857343500201451957 370003205375953143886121)
                    ·
                      rfl

theorem cell23_2161736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_2161736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161736 prefixEnd_2161736 := by exact prefixLift 2161736
  have htrace : WordTrace (prefixWord ++ tailWord_2161736) baseStart_2161736 baseEnd_2161736 := by
    simpa [prefixWord, tailWord_2161736, baseEnd_2161736] using wordTrace_append hprefix tailTrace_2161736
  have hstable : (prefixWord ++ tailWord_2161736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161736).length < 2 ^ (prefixWord ++ tailWord_2161736).sum := by decide
  have hdescent : baseEnd_2161736 < baseStart_2161736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161773 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2161773 : Nat := 118140960795 + 2161773 * 2 ^ 59
def prefixEnd_2161773 : Nat := 4983230072969 + 3 ^ 40 * 2161773 * 2
def baseEnd_2161773 : Nat := 1110028614912075786895693

theorem tailTrace_2161773 : CollatzResearch.WordTrace tailWord_2161773 prefixEnd_2161773 1110028614912075786895693 := by
  unfold tailWord_2161773
  simp only [CollatzResearch.WordTrace]
  refine ⟨78846338797273097279881973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52564225864848731519921315 78846338797273097279881973)
  ·
    refine ⟨7391844262244352869988935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78846338797273097279881973 7391844262244352869988935)
    ·
      refine ⟨11087766393366529304983403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7391844262244352869988935 11087766393366529304983403)
      ·
        refine ⟨16631649590049793957475105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11087766393366529304983403 16631649590049793957475105)
        ·
          refine ⟨12473737192537345468106329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16631649590049793957475105 12473737192537345468106329)
          ·
            refine ⟨9355302894403009101079747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12473737192537345468106329 9355302894403009101079747)
            ·
              refine ⟨14032954341604513651619621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9355302894403009101079747 14032954341604513651619621)
              ·
                refine ⟨2631178939050846309678679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14032954341604513651619621 2631178939050846309678679)
                ·
                  refine ⟨3946768408576269464518019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631178939050846309678679 3946768408576269464518019)
                  ·
                    refine ⟨5920152612864404196777029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3946768408576269464518019 5920152612864404196777029)
                    ·
                      refine ⟨1110028614912075786895693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5920152612864404196777029 1110028614912075786895693)
                      ·
                        rfl

theorem cell23_2161773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2161773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161773 prefixEnd_2161773 := by exact prefixLift 2161773
  have htrace : WordTrace (prefixWord ++ tailWord_2161773) baseStart_2161773 baseEnd_2161773 := by
    simpa [prefixWord, tailWord_2161773, baseEnd_2161773] using wordTrace_append hprefix tailTrace_2161773
  have hstable : (prefixWord ++ tailWord_2161773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161773).length < 2 ^ (prefixWord ++ tailWord_2161773).sum := by decide
  have hdescent : baseEnd_2161773 < baseStart_2161773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161793 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2161793 : Nat := 118140960795 + 2161793 * 2 ^ 59
def prefixEnd_2161793 : Nat := 4983230072969 + 3 ^ 40 * 2161793 * 2
def baseEnd_2161793 : Nat := 1110038884525165708645601

theorem tailTrace_2161793 : CollatzResearch.WordTrace tailWord_2161793 prefixEnd_2161793 1110038884525165708645601 := by
  unfold tailWord_2161793
  simp only [CollatzResearch.WordTrace]
  refine ⟨78847068257200640695610033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52564712171467093797073355 78847068257200640695610033)
  ·
    refine ⟨59135301192900480521707525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78847068257200640695610033 59135301192900480521707525)
    ·
      refine ⟨11087868973668840097820161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59135301192900480521707525 11087868973668840097820161)
      ·
        refine ⟨8315901730251630073365121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11087868973668840097820161 8315901730251630073365121)
        ·
          refine ⟨6236926297688722555023841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8315901730251630073365121 6236926297688722555023841)
          ·
            refine ⟨4677694723266541916267881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6236926297688722555023841 4677694723266541916267881)
            ·
              refine ⟨3508271042449906437200911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4677694723266541916267881 3508271042449906437200911)
              ·
                refine ⟨5262406563674859655801367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508271042449906437200911 5262406563674859655801367)
                ·
                  refine ⟨7893609845512289483702051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5262406563674859655801367 7893609845512289483702051)
                  ·
                    refine ⟨11840414768268434225553077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7893609845512289483702051 11840414768268434225553077)
                    ·
                      refine ⟨1110038884525165708645601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11840414768268434225553077 1110038884525165708645601)
                      ·
                        rfl

theorem cell23_2161793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2161793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161793 prefixEnd_2161793 := by exact prefixLift 2161793
  have htrace : WordTrace (prefixWord ++ tailWord_2161793) baseStart_2161793 baseEnd_2161793 := by
    simpa [prefixWord, tailWord_2161793, baseEnd_2161793] using wordTrace_append hprefix tailTrace_2161793
  have hstable : (prefixWord ++ tailWord_2161793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161793).length < 2 ^ (prefixWord ++ tailWord_2161793).sum := by decide
  have hdescent : baseEnd_2161793 < baseStart_2161793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161796 : List Nat := [2, 3, 2, 1, 2, 4, 9]
def baseStart_2161796 : Nat := 118140960795 + 2161796 * 2 ^ 59
def prefixEnd_2161796 : Nat := 4983230072969 + 3 ^ 40 * 2161796 * 2
def baseEnd_2161796 : Nat := 13704202777371965393927

theorem tailTrace_2161796 : CollatzResearch.WordTrace tailWord_2161796 prefixEnd_2161796 13704202777371965393927 := by
  unfold tailWord_2161796
  simp only [CollatzResearch.WordTrace]
  refine ⟨39423588838094886103984621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52564785117459848138646161 39423588838094886103984621)
  ·
    refine ⟨14783845814285582288994233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39423588838094886103984621 14783845814285582288994233)
    ·
      refine ⟨11087884360714186716745675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14783845814285582288994233 11087884360714186716745675)
      ·
        refine ⟨16631826541071280075118513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11087884360714186716745675 16631826541071280075118513)
        ·
          refine ⟨12473869905803460056338885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16631826541071280075118513 12473869905803460056338885)
          ·
            refine ⟨2338850607338148760563541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12473869905803460056338885 2338850607338148760563541)
            ·
              refine ⟨13704202777371965393927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2338850607338148760563541 13704202777371965393927)
              ·
                rfl

theorem cell23_2161796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 9].length) (baseStart_2161796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161796 prefixEnd_2161796 := by exact prefixLift 2161796
  have htrace : WordTrace (prefixWord ++ tailWord_2161796) baseStart_2161796 baseEnd_2161796 := by
    simpa [prefixWord, tailWord_2161796, baseEnd_2161796] using wordTrace_append hprefix tailTrace_2161796
  have hstable : (prefixWord ++ tailWord_2161796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161796).length < 2 ^ (prefixWord ++ tailWord_2161796).sum := by decide
  have hdescent : baseEnd_2161796 < baseStart_2161796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161819 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_2161819 : Nat := 118140960795 + 2161819 * 2 ^ 59
def prefixEnd_2161819 : Nat := 4983230072969 + 3 ^ 40 * 2161819 * 2
def baseEnd_2161819 : Nat := 1110052235022182606920481

theorem tailTrace_2161819 : CollatzResearch.WordTrace tailWord_2161819 prefixEnd_2161819 1110052235022182606920481 := by
  unfold tailWord_2161819
  simp only [CollatzResearch.WordTrace]
  refine ⟨78848016555106447136056511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52565344370070964757371007 78848016555106447136056511)
  ·
    refine ⟨118272024832659670704084767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78848016555106447136056511 118272024832659670704084767)
    ·
      refine ⟨177408037248989506056127151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118272024832659670704084767 177408037248989506056127151)
      ·
        refine ⟨266112055873484259084190727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177408037248989506056127151 266112055873484259084190727)
        ·
          refine ⟨399168083810226388626286091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266112055873484259084190727 399168083810226388626286091)
          ·
            refine ⟨598752125715339582939429137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399168083810226388626286091 598752125715339582939429137)
            ·
              refine ⟨449064094286504687204571853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598752125715339582939429137 449064094286504687204571853)
              ·
                refine ⟨168399035357439257701714445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449064094286504687204571853 168399035357439257701714445)
                ·
                  refine ⟨63149638259039721638142917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168399035357439257701714445 63149638259039721638142917)
                  ·
                    refine ⟨11840557173569947807151797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63149638259039721638142917 11840557173569947807151797)
                    ·
                      refine ⟨1110052235022182606920481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11840557173569947807151797 1110052235022182606920481)
                      ·
                        rfl

theorem cell23_2161819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_2161819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161819 prefixEnd_2161819 := by exact prefixLift 2161819
  have htrace : WordTrace (prefixWord ++ tailWord_2161819) baseStart_2161819 baseEnd_2161819 := by
    simpa [prefixWord, tailWord_2161819, baseEnd_2161819] using wordTrace_append hprefix tailTrace_2161819
  have hstable : (prefixWord ++ tailWord_2161819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161819).length < 2 ^ (prefixWord ++ tailWord_2161819).sum := by decide
  have hdescent : baseEnd_2161819 < baseStart_2161819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161857 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2161857 : Nat := 118140960795 + 2161857 * 2 ^ 59
def prefixEnd_2161857 : Nat := 4983230072969 + 3 ^ 40 * 2161857 * 2
def baseEnd_2161857 : Nat := 1110071747287053458245307

theorem tailTrace_2161857 : CollatzResearch.WordTrace tailWord_2161857 prefixEnd_2161857 1110071747287053458245307 := by
  unfold tailWord_2161857
  simp only [CollatzResearch.WordTrace]
  refine ⟨78849402528968779625939825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52566268352645853083959883 78849402528968779625939825)
  ·
    refine ⟨59137051896726584719454869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78849402528968779625939825 59137051896726584719454869)
    ·
      refine ⟨2772049307659058658724447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59137051896726584719454869 2772049307659058658724447)
      ·
        refine ⟨4158073961488587988086671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772049307659058658724447 4158073961488587988086671)
        ·
          refine ⟨6237110942232881982130007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158073961488587988086671 6237110942232881982130007)
          ·
            refine ⟨9355666413349322973195011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237110942232881982130007 9355666413349322973195011)
            ·
              refine ⟨14033499620023984459792517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9355666413349322973195011 14033499620023984459792517)
              ·
                refine ⟨2631281178754497086211097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14033499620023984459792517 2631281178754497086211097)
                ·
                  refine ⟨1973460884065872814658323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631281178754497086211097 1973460884065872814658323)
                  ·
                    refine ⟨2960191326098809221987485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973460884065872814658323 2960191326098809221987485)
                    ·
                      refine ⟨1110071747287053458245307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2960191326098809221987485 1110071747287053458245307)
                      ·
                        rfl

theorem cell23_2161857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2161857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161857 prefixEnd_2161857 := by exact prefixLift 2161857
  have htrace : WordTrace (prefixWord ++ tailWord_2161857) baseStart_2161857 baseEnd_2161857 := by
    simpa [prefixWord, tailWord_2161857, baseEnd_2161857] using wordTrace_append hprefix tailTrace_2161857
  have hstable : (prefixWord ++ tailWord_2161857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161857).length < 2 ^ (prefixWord ++ tailWord_2161857).sum := by decide
  have hdescent : baseEnd_2161857 < baseStart_2161857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161858 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_2161858 : Nat := 118140960795 + 2161858 * 2 ^ 59
def prefixEnd_2161858 : Nat := 4983230072969 + 3 ^ 40 * 2161858 * 2
def baseEnd_2161858 : Nat := 1110072260767707954332803

theorem tailTrace_2161858 : CollatzResearch.WordTrace tailWord_2161858 prefixEnd_2161858 1110072260767707954332803 := by
  unfold tailWord_2161858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19712359750491289199181557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52566292667976771197817485 19712359750491289199181557)
  ·
    refine ⟨1848033726608558362423271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19712359750491289199181557 1848033726608558362423271)
    ·
      refine ⟨2772050589912837543634907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848033726608558362423271 2772050589912837543634907)
      ·
        refine ⟨4158075884869256315452361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772050589912837543634907 4158075884869256315452361)
        ·
          refine ⟨3118556913651942236589271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4158075884869256315452361 3118556913651942236589271)
          ·
            refine ⟨4677835370477913354883907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118556913651942236589271 4677835370477913354883907)
            ·
              refine ⟨7016753055716870032325861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677835370477913354883907 7016753055716870032325861)
              ·
                refine ⟨1315641197946913131061099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7016753055716870032325861 1315641197946913131061099)
                ·
                  refine ⟨1973461796920369696591649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315641197946913131061099 1973461796920369696591649)
                  ·
                    refine ⟨1480096347690277272443737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1973461796920369696591649 1480096347690277272443737)
                    ·
                      refine ⟨1110072260767707954332803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480096347690277272443737 1110072260767707954332803)
                      ·
                        rfl

theorem cell23_2161858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_2161858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161858 prefixEnd_2161858 := by exact prefixLift 2161858
  have htrace : WordTrace (prefixWord ++ tailWord_2161858) baseStart_2161858 baseEnd_2161858 := by
    simpa [prefixWord, tailWord_2161858, baseEnd_2161858] using wordTrace_append hprefix tailTrace_2161858
  have hstable : (prefixWord ++ tailWord_2161858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161858).length < 2 ^ (prefixWord ++ tailWord_2161858).sum := by decide
  have hdescent : baseEnd_2161858 < baseStart_2161858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161908 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2161908 : Nat := 118140960795 + 2161908 * 2 ^ 59
def prefixEnd_2161908 : Nat := 4983230072969 + 3 ^ 40 * 2161908 * 2
def baseEnd_2161908 : Nat := 1110097934800432758707573

theorem tailTrace_2161908 : CollatzResearch.WordTrace tailWord_2161908 prefixEnd_2161908 1110097934800432758707573 := by
  unfold tailWord_2161908
  simp only [CollatzResearch.WordTrace]
  refine ⟨39425631325892007668023189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52567508434522676890697585 39425631325892007668023189)
  ·
    refine ⟨1848076468401187859438587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39425631325892007668023189 1848076468401187859438587)
    ·
      refine ⟨2772114702601781789157881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848076468401187859438587 2772114702601781789157881)
      ·
        refine ⟨2079086026951336341868411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2772114702601781789157881 2079086026951336341868411)
        ·
          refine ⟨3118629040427004512802617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079086026951336341868411 3118629040427004512802617)
          ·
            refine ⟨2338971780320253384601963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3118629040427004512802617 2338971780320253384601963)
            ·
              refine ⟨3508457670480380076902945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338971780320253384601963 3508457670480380076902945)
              ·
                refine ⟨2631343252860285057677209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3508457670480380076902945 2631343252860285057677209)
                ·
                  refine ⟨1973507439645213793257907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631343252860285057677209 1973507439645213793257907)
                  ·
                    refine ⟨2960261159467820689886861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973507439645213793257907 2960261159467820689886861)
                    ·
                      refine ⟨1110097934800432758707573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2960261159467820689886861 1110097934800432758707573)
                      ·
                        rfl

theorem cell23_2161908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2161908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161908 prefixEnd_2161908 := by exact prefixLift 2161908
  have htrace : WordTrace (prefixWord ++ tailWord_2161908) baseStart_2161908 baseEnd_2161908 := by
    simpa [prefixWord, tailWord_2161908, baseEnd_2161908] using wordTrace_append hprefix tailTrace_2161908
  have hstable : (prefixWord ++ tailWord_2161908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161908).length < 2 ^ (prefixWord ++ tailWord_2161908).sum := by decide
  have hdescent : baseEnd_2161908 < baseStart_2161908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161953 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2161953 : Nat := 118140960795 + 2161953 * 2 ^ 59
def prefixEnd_2161953 : Nat := 4983230072969 + 3 ^ 40 * 2161953 * 2
def baseEnd_2161953 : Nat := 1110121041429885082644865

theorem tailTrace_2161953 : CollatzResearch.WordTrace tailWord_2161953 prefixEnd_2161953 1110121041429885082644865 := by
  unfold tailWord_2161953
  simp only [CollatzResearch.WordTrace]
  refine ⟨78852903936620988021434513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52568602624413992014289675 78852903936620988021434513)
  ·
    refine ⟨59139677952465741016075885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78852903936620988021434513 59139677952465741016075885)
    ·
      refine ⟨22177379232174652881028457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59139677952465741016075885 22177379232174652881028457)
      ·
        refine ⟨16633034424130989660771343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22177379232174652881028457 16633034424130989660771343)
        ·
          refine ⟨24949551636196484491157015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16633034424130989660771343 24949551636196484491157015)
          ·
            refine ⟨37424327454294726736735523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24949551636196484491157015 37424327454294726736735523)
            ·
              refine ⟨56136491181442090105103285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37424327454294726736735523 56136491181442090105103285)
              ·
                refine ⟨5262796048260195947353433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56136491181442090105103285 5262796048260195947353433)
                ·
                  refine ⟨3947097036195146960515075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5262796048260195947353433 3947097036195146960515075)
                  ·
                    refine ⟨5920645554292720440772613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947097036195146960515075 5920645554292720440772613)
                    ·
                      refine ⟨1110121041429885082644865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5920645554292720440772613 1110121041429885082644865)
                      ·
                        rfl

theorem cell23_2161953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2161953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161953 prefixEnd_2161953 := by exact prefixLift 2161953
  have htrace : WordTrace (prefixWord ++ tailWord_2161953) baseStart_2161953 baseEnd_2161953 := by
    simpa [prefixWord, tailWord_2161953, baseEnd_2161953] using wordTrace_append hprefix tailTrace_2161953
  have hstable : (prefixWord ++ tailWord_2161953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161953).length < 2 ^ (prefixWord ++ tailWord_2161953).sum := by decide
  have hdescent : baseEnd_2161953 < baseStart_2161953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161954 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_2161954 : Nat := 118140960795 + 2161954 * 2 ^ 59
def prefixEnd_2161954 : Nat := 4983230072969 + 3 ^ 40 * 2161954 * 2
def baseEnd_2161954 : Nat := 123346839434504397636929

theorem tailTrace_2161954 : CollatzResearch.WordTrace tailWord_2161954 prefixEnd_2161954 123346839434504397636929 := by
  unfold tailWord_2161954
  simp only [CollatzResearch.WordTrace]
  refine ⟨19713235102404341298055229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52568626939744910128147277 19713235102404341298055229)
  ·
    refine ⟨7392463163401627986770711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19713235102404341298055229 7392463163401627986770711)
    ·
      refine ⟨11088694745102441980156067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7392463163401627986770711 11088694745102441980156067)
      ·
        refine ⟨16633042117653662970234101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11088694745102441980156067 16633042117653662970234101)
        ·
          refine ⟨1559347698530030903459447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16633042117653662970234101 1559347698530030903459447)
          ·
            refine ⟨2339021547795046355189171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559347698530030903459447 2339021547795046355189171)
            ·
              refine ⟨3508532321692569532783757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339021547795046355189171 3508532321692569532783757)
              ·
                refine ⟨1315699620634713574793909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3508532321692569532783757 1315699620634713574793909)
                ·
                  refine ⟨123346839434504397636929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315699620634713574793909 123346839434504397636929)
                  ·
                    rfl

theorem cell23_2161954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_2161954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161954 prefixEnd_2161954 := by exact prefixLift 2161954
  have htrace : WordTrace (prefixWord ++ tailWord_2161954) baseStart_2161954 baseEnd_2161954 := by
    simpa [prefixWord, tailWord_2161954, baseEnd_2161954] using wordTrace_append hprefix tailTrace_2161954
  have hstable : (prefixWord ++ tailWord_2161954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161954).length < 2 ^ (prefixWord ++ tailWord_2161954).sum := by decide
  have hdescent : baseEnd_2161954 < baseStart_2161954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161970 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2161970 : Nat := 118140960795 + 2161970 * 2 ^ 59
def prefixEnd_2161970 : Nat := 4983230072969 + 3 ^ 40 * 2161970 * 2
def baseEnd_2161970 : Nat := 1110129770601011516132287

theorem tailTrace_2161970 : CollatzResearch.WordTrace tailWord_2161970 prefixEnd_2161970 1110129770601011516132287 := by
  unfold tailWord_2161970
  simp only [CollatzResearch.WordTrace]
  refine ⟨19713380994389849981200841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52569015985039599949868909 19713380994389849981200841)
  ·
    refine ⟨14785035745792387485900631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19713380994389849981200841 14785035745792387485900631)
    ·
      refine ⟨22177553618688581228850947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14785035745792387485900631 22177553618688581228850947)
      ·
        refine ⟨33266330428032871843276421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22177553618688581228850947 33266330428032871843276421)
        ·
          refine ⟨6237436955256163470614329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33266330428032871843276421 6237436955256163470614329)
          ·
            refine ⟨4678077716442122602960747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237436955256163470614329 4678077716442122602960747)
            ·
              refine ⟨7017116574663183904441121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678077716442122602960747 7017116574663183904441121)
              ·
                refine ⟨5262837430997387928330841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7017116574663183904441121 5262837430997387928330841)
                ·
                  refine ⟨3947128073248040946248131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5262837430997387928330841 3947128073248040946248131)
                  ·
                    refine ⟨5920692109872061419372197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947128073248040946248131 5920692109872061419372197)
                    ·
                      refine ⟨1110129770601011516132287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5920692109872061419372197 1110129770601011516132287)
                      ·
                        rfl

theorem cell23_2161970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2161970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161970 prefixEnd_2161970 := by exact prefixLift 2161970
  have htrace : WordTrace (prefixWord ++ tailWord_2161970) baseStart_2161970 baseEnd_2161970 := by
    simpa [prefixWord, tailWord_2161970, baseEnd_2161970] using wordTrace_append hprefix tailTrace_2161970
  have hstable : (prefixWord ++ tailWord_2161970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161970).length < 2 ^ (prefixWord ++ tailWord_2161970).sum := by decide
  have hdescent : baseEnd_2161970 < baseStart_2161970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161980 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_2161980 : Nat := 118140960795 + 2161980 * 2 ^ 59
def prefixEnd_2161980 : Nat := 4983230072969 + 3 ^ 40 * 2161980 * 2
def baseEnd_2161980 : Nat := 370044968469185492335747

theorem tailTrace_2161980 : CollatzResearch.WordTrace tailWord_2161980 prefixEnd_2161980 370044968469185492335747 := by
  unfold tailWord_2161980
  simp only [CollatzResearch.WordTrace]
  refine ⟨39426944353761585816333697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52569259138348781088444929 39426944353761585816333697)
  ·
    refine ⟨29570208265321189362250273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39426944353761585816333697 29570208265321189362250273)
    ·
      refine ⟨22177656198990892021687705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29570208265321189362250273 22177656198990892021687705)
      ·
        refine ⟨16633242149243169016265779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22177656198990892021687705 16633242149243169016265779)
        ·
          refine ⟨24949863223864753524398669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16633242149243169016265779 24949863223864753524398669)
          ·
            refine ⟨9356198708949282571649501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24949863223864753524398669 9356198708949282571649501)
            ·
              refine ⟨3508574515855980964368563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9356198708949282571649501 3508574515855980964368563)
              ·
                refine ⟨5262861773783971446552845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508574515855980964368563 5262861773783971446552845)
                ·
                  refine ⟨1973573165168989292457317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5262861773783971446552845 1973573165168989292457317)
                  ·
                    refine ⟨370044968469185492335747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1973573165168989292457317 370044968469185492335747)
                    ·
                      rfl

theorem cell23_2161980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_2161980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2161980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2161980 prefixEnd_2161980 := by exact prefixLift 2161980
  have htrace : WordTrace (prefixWord ++ tailWord_2161980) baseStart_2161980 baseEnd_2161980 := by
    simpa [prefixWord, tailWord_2161980, baseEnd_2161980] using wordTrace_append hprefix tailTrace_2161980
  have hstable : (prefixWord ++ tailWord_2161980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161980).length < 2 ^ (prefixWord ++ tailWord_2161980).sum := by decide
  have hdescent : baseEnd_2161980 < baseStart_2161980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162043 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 4]
def baseStart_2162043 : Nat := 118140960795 + 2162043 * 2 ^ 59
def prefixEnd_2162043 : Nat := 4983230072969 + 3 ^ 40 * 2162043 * 2
def baseEnd_2162043 : Nat := 1110167254688789730519451

theorem tailTrace_2162043 : CollatzResearch.WordTrace tailWord_2162043 prefixEnd_2162043 1110167254688789730519451 := by
  unfold tailWord_2162043
  simp only [CollatzResearch.WordTrace]
  refine ⟨78856186506294933392210783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52570791004196622261473855 78856186506294933392210783)
  ·
    refine ⟨118284279759442400088316175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78856186506294933392210783 118284279759442400088316175)
    ·
      refine ⟨177426419639163600132474263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118284279759442400088316175 177426419639163600132474263)
      ·
        refine ⟨266139629458745400198711395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177426419639163600132474263 266139629458745400198711395)
        ·
          refine ⟨399209444188118100298067093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266139629458745400198711395 399209444188118100298067093)
          ·
            refine ⟨18712942696318035951471895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 399209444188118100298067093 18712942696318035951471895)
            ·
              refine ⟨28069414044477053927207843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18712942696318035951471895 28069414044477053927207843)
              ·
                refine ⟨42104121066715580890811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28069414044477053927207843 42104121066715580890811765)
                ·
                  refine ⟨3947261350004585708513603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42104121066715580890811765 3947261350004585708513603)
                  ·
                    refine ⟨5920892025006878562770405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947261350004585708513603 5920892025006878562770405)
                    ·
                      refine ⟨1110167254688789730519451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5920892025006878562770405 1110167254688789730519451)
                      ·
                        rfl

theorem cell23_2162043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 4].length) (baseStart_2162043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162043 prefixEnd_2162043 := by exact prefixLift 2162043
  have htrace : WordTrace (prefixWord ++ tailWord_2162043) baseStart_2162043 baseEnd_2162043 := by
    simpa [prefixWord, tailWord_2162043, baseEnd_2162043] using wordTrace_append hprefix tailTrace_2162043
  have hstable : (prefixWord ++ tailWord_2162043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162043).length < 2 ^ (prefixWord ++ tailWord_2162043).sum := by decide
  have hdescent : baseEnd_2162043 < baseStart_2162043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162053 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_2162053 : Nat := 118140960795 + 2162053 * 2 ^ 59
def prefixEnd_2162053 : Nat := 4983230072969 + 3 ^ 40 * 2162053 * 2
def baseEnd_2162053 : Nat := 370057463165111563798135

theorem tailTrace_2162053 : CollatzResearch.WordTrace tailWord_2162053 prefixEnd_2162053 370057463165111563798135 := by
  unfold tailWord_2162053
  simp only [CollatzResearch.WordTrace]
  refine ⟨78856551236258705100074813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52571034157505803400049875 78856551236258705100074813)
  ·
    refine ⟨29571206713597014412528055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78856551236258705100074813 29571206713597014412528055)
    ·
      refine ⟨44356810070395521618792083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29571206713597014412528055 44356810070395521618792083)
      ·
        refine ⟨66535215105593282428188125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44356810070395521618792083 66535215105593282428188125)
        ·
          refine ⟨24950705664597480910570547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66535215105593282428188125 24950705664597480910570547)
          ·
            refine ⟨37426058496896221365855821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24950705664597480910570547 37426058496896221365855821)
            ·
              refine ⟨14034771936336083012195933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37426058496896221365855821 14034771936336083012195933)
              ·
                refine ⟨5263039476126031129573475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14034771936336083012195933 5263039476126031129573475)
                ·
                  refine ⟨7894559214189046694360213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263039476126031129573475 7894559214189046694360213)
                  ·
                    refine ⟨370057463165111563798135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7894559214189046694360213 370057463165111563798135)
                    ·
                      rfl

theorem cell23_2162053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_2162053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162053 prefixEnd_2162053 := by exact prefixLift 2162053
  have htrace : WordTrace (prefixWord ++ tailWord_2162053) baseStart_2162053 baseEnd_2162053 := by
    simpa [prefixWord, tailWord_2162053, baseEnd_2162053] using wordTrace_append hprefix tailTrace_2162053
  have hstable : (prefixWord ++ tailWord_2162053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162053).length < 2 ^ (prefixWord ++ tailWord_2162053).sum := by decide
  have hdescent : baseEnd_2162053 < baseStart_2162053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162060 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_2162060 : Nat := 118140960795 + 2162060 * 2 ^ 59
def prefixEnd_2162060 : Nat := 4983230072969 + 3 ^ 40 * 2162060 * 2
def baseEnd_2162060 : Nat := 1110175983859916164006873

theorem tailTrace_2162060 : CollatzResearch.WordTrace tailWord_2162060 prefixEnd_2162060 1110175983859916164006873 := by
  unfold tailWord_2162060
  simp only [CollatzResearch.WordTrace]
  refine ⟨39428403273616672647789817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52571204364822230197053089 39428403273616672647789817)
  ·
    refine ⟨29571302455212504485842363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39428403273616672647789817 29571302455212504485842363)
    ·
      refine ⟨44356953682818756728763545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29571302455212504485842363 44356953682818756728763545)
      ·
        refine ⟨33267715262114067546572659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44356953682818756728763545 33267715262114067546572659)
        ·
          refine ⟨49901572893171101319858989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33267715262114067546572659 49901572893171101319858989)
          ·
            refine ⟨18713089834939162994947121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49901572893171101319858989 18713089834939162994947121)
            ·
              refine ⟨14034817376204372246210341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18713089834939162994947121 14034817376204372246210341)
              ·
                refine ⟨2631528258038319796164439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14034817376204372246210341 2631528258038319796164439)
                ·
                  refine ⟨3947292387057479694246659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631528258038319796164439 3947292387057479694246659)
                  ·
                    refine ⟨5920938580586219541369989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947292387057479694246659 5920938580586219541369989)
                    ·
                      refine ⟨1110175983859916164006873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5920938580586219541369989 1110175983859916164006873)
                      ·
                        rfl

theorem cell23_2162060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_2162060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162060 prefixEnd_2162060 := by exact prefixLift 2162060
  have htrace : WordTrace (prefixWord ++ tailWord_2162060) baseStart_2162060 baseEnd_2162060 := by
    simpa [prefixWord, tailWord_2162060, baseEnd_2162060] using wordTrace_append hprefix tailTrace_2162060
  have hstable : (prefixWord ++ tailWord_2162060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162060).length < 2 ^ (prefixWord ++ tailWord_2162060).sum := by decide
  have hdescent : baseEnd_2162060 < baseStart_2162060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162077 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2162077 : Nat := 118140960795 + 2162077 * 2 ^ 59
def prefixEnd_2162077 : Nat := 4983230072969 + 3 ^ 40 * 2162077 * 2
def baseEnd_2162077 : Nat := 1110184713031042597494295

theorem tailTrace_2162077 : CollatzResearch.WordTrace tailWord_2162077 prefixEnd_2162077 1110184713031042597494295 := by
  unfold tailWord_2162077
  simp only [CollatzResearch.WordTrace]
  refine ⟨78857426588171757198948485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52571617725447838132632323 78857426588171757198948485)
  ·
    refine ⟨14785767485282204474802841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78857426588171757198948485 14785767485282204474802841)
    ·
      refine ⟨11089325613961653356102131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14785767485282204474802841 11089325613961653356102131)
      ·
        refine ⟨16633988420942480034153197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11089325613961653356102131 16633988420942480034153197)
        ·
          refine ⟨6237745657853430012807449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16633988420942480034153197 6237745657853430012807449)
          ·
            refine ⟨4678309243390072509605587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237745657853430012807449 4678309243390072509605587)
            ·
              refine ⟨7017463865085108764408381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678309243390072509605587 7017463865085108764408381)
              ·
                refine ⟨2631548949406915786653143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7017463865085108764408381 2631548949406915786653143)
                ·
                  refine ⟨3947323424110373679979715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631548949406915786653143 3947323424110373679979715)
                  ·
                    refine ⟨5920985136165560519969573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947323424110373679979715 5920985136165560519969573)
                    ·
                      refine ⟨1110184713031042597494295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5920985136165560519969573 1110184713031042597494295)
                      ·
                        rfl

theorem cell23_2162077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2162077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162077 prefixEnd_2162077 := by exact prefixLift 2162077
  have htrace : WordTrace (prefixWord ++ tailWord_2162077) baseStart_2162077 baseEnd_2162077 := by
    simpa [prefixWord, tailWord_2162077, baseEnd_2162077] using wordTrace_append hprefix tailTrace_2162077
  have hstable : (prefixWord ++ tailWord_2162077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162077).length < 2 ^ (prefixWord ++ tailWord_2162077).sum := by decide
  have hdescent : baseEnd_2162077 < baseStart_2162077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162123 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_2162123 : Nat := 118140960795 + 2162123 * 2 ^ 59
def prefixEnd_2162123 : Nat := 4983230072969 + 3 ^ 40 * 2162123 * 2
def baseEnd_2162123 : Nat := 1110208333141149417519083

theorem tailTrace_2162123 : CollatzResearch.WordTrace tailWord_2162123 prefixEnd_2162123 1110208333141149417519083 := by
  unfold tailWord_2162123
  simp only [CollatzResearch.WordTrace]
  refine ⟨78859104346005107055123023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52572736230670071370082015 78859104346005107055123023)
  ·
    refine ⟨118288656519007660582684535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78859104346005107055123023 118288656519007660582684535)
    ·
      refine ⟨177432984778511490874026803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118288656519007660582684535 177432984778511490874026803)
      ·
        refine ⟨266149477167767236311040205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177432984778511490874026803 266149477167767236311040205)
        ·
          refine ⟨99806053937912713616640077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266149477167767236311040205 99806053937912713616640077)
          ·
            refine ⟨37427270226717267606240029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99806053937912713616640077 37427270226717267606240029)
            ·
              refine ⟨14035226335018975352340011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37427270226717267606240029 14035226335018975352340011)
              ·
                refine ⟨21052839502528463028510017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14035226335018975352340011 21052839502528463028510017)
                ·
                  refine ⟨15789629626896347271382513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21052839502528463028510017 15789629626896347271382513)
                  ·
                    refine ⟨11842222220172260453536885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15789629626896347271382513 11842222220172260453536885)
                    ·
                      refine ⟨1110208333141149417519083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11842222220172260453536885 1110208333141149417519083)
                      ·
                        rfl

theorem cell23_2162123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_2162123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162123 prefixEnd_2162123 := by exact prefixLift 2162123
  have htrace : WordTrace (prefixWord ++ tailWord_2162123) baseStart_2162123 baseEnd_2162123 := by
    simpa [prefixWord, tailWord_2162123, baseEnd_2162123] using wordTrace_append hprefix tailTrace_2162123
  have hstable : (prefixWord ++ tailWord_2162123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162123).length < 2 ^ (prefixWord ++ tailWord_2162123).sum := by decide
  have hdescent : baseEnd_2162123 < baseStart_2162123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162161 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 2, 1, 3]
def baseStart_2162161 : Nat := 118140960795 + 2162161 * 2 ^ 59
def prefixEnd_2162161 : Nat := 4983230072969 + 3 ^ 40 * 2162161 * 2
def baseEnd_2162161 : Nat := 1110227845406020268843909

theorem tailTrace_2162161 : CollatzResearch.WordTrace tailWord_2162161 prefixEnd_2162161 1110227845406020268843909 := by
  unfold tailWord_2162161
  simp only [CollatzResearch.WordTrace]
  refine ⟨78860490319867439545006337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52573660213244959696670891 78860490319867439545006337)
  ·
    refine ⟨59145367739900579658754753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78860490319867439545006337 59145367739900579658754753)
    ·
      refine ⟨44359025804925434744066065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59145367739900579658754753 44359025804925434744066065)
      ·
        refine ⟨33269269353694076058049549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44359025804925434744066065 33269269353694076058049549)
        ·
          refine ⟨12475976007635278521768581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33269269353694076058049549 12475976007635278521768581)
          ·
            refine ⟨2339245501431614722831609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12475976007635278521768581 2339245501431614722831609)
            ·
              refine ⟨1754434126073711042123707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2339245501431614722831609 1754434126073711042123707)
              ·
                refine ⟨2631651189110566563185561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754434126073711042123707 2631651189110566563185561)
                ·
                  refine ⟨1973738391832924922389171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631651189110566563185561 1973738391832924922389171)
                  ·
                    refine ⟨2960607587749387383583757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973738391832924922389171 2960607587749387383583757)
                    ·
                      refine ⟨1110227845406020268843909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2960607587749387383583757 1110227845406020268843909)
                      ·
                        rfl

theorem cell23_2162161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_2162161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162161 prefixEnd_2162161 := by exact prefixLift 2162161
  have htrace : WordTrace (prefixWord ++ tailWord_2162161) baseStart_2162161 baseEnd_2162161 := by
    simpa [prefixWord, tailWord_2162161, baseEnd_2162161] using wordTrace_append hprefix tailTrace_2162161
  have hstable : (prefixWord ++ tailWord_2162161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162161).length < 2 ^ (prefixWord ++ tailWord_2162161).sum := by decide
  have hdescent : baseEnd_2162161 < baseStart_2162161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162167 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 6, 2, 2]
def baseStart_2162167 : Nat := 118140960795 + 2162167 * 2 ^ 59
def prefixEnd_2162167 : Nat := 4983230072969 + 3 ^ 40 * 2162167 * 2
def baseEnd_2162167 : Nat := 1110230926289947245368881

theorem tailTrace_2162167 : CollatzResearch.WordTrace tailWord_2162167 prefixEnd_2162167 1110230926289947245368881 := by
  unfold tailWord_2162167
  simp only [CollatzResearch.WordTrace]
  refine ⟨78860709157845702569724755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52573806105230468379816503 78860709157845702569724755)
  ·
    refine ⟨118291063736768553854587133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78860709157845702569724755 118291063736768553854587133)
    ·
      refine ⟨44359148901288207695470175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118291063736768553854587133 44359148901288207695470175)
      ·
        refine ⟨66538723351932311543205263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44359148901288207695470175 66538723351932311543205263)
        ·
          refine ⟨99808085027898467314807895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66538723351932311543205263 99808085027898467314807895)
          ·
            refine ⟨149712127541847700972211843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99808085027898467314807895 149712127541847700972211843)
            ·
              refine ⟨224568191312771551458317765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149712127541847700972211843 224568191312771551458317765)
              ·
                refine ⟨42106535871144665898434581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224568191312771551458317765 42106535871144665898434581)
                ·
                  refine ⟨1973743868959906213989121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42106535871144665898434581 1973743868959906213989121)
                  ·
                    refine ⟨1480307901719929660491841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1973743868959906213989121 1480307901719929660491841)
                    ·
                      refine ⟨1110230926289947245368881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480307901719929660491841 1110230926289947245368881)
                      ·
                        rfl

theorem cell23_2162167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_2162167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162167 prefixEnd_2162167 := by exact prefixLift 2162167
  have htrace : WordTrace (prefixWord ++ tailWord_2162167) baseStart_2162167 baseEnd_2162167 := by
    simpa [prefixWord, tailWord_2162167, baseEnd_2162167] using wordTrace_append hprefix tailTrace_2162167
  have hstable : (prefixWord ++ tailWord_2162167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162167).length < 2 ^ (prefixWord ++ tailWord_2162167).sum := by decide
  have hdescent : baseEnd_2162167 < baseStart_2162167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162237 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2162237 : Nat := 118140960795 + 2162237 * 2 ^ 59
def prefixEnd_2162237 : Nat := 4983230072969 + 3 ^ 40 * 2162237 * 2
def baseEnd_2162237 : Nat := 370088956645253990497853

theorem tailTrace_2162237 : CollatzResearch.WordTrace tailWord_2162237 prefixEnd_2162237 370088956645253990497853 := by
  unfold tailWord_2162237
  simp only [CollatzResearch.WordTrace]
  refine ⟨78863262267592104524772965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52575508178394736349848643 78863262267592104524772965)
  ·
    refine ⟨14786861675173519598394931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78863262267592104524772965 14786861675173519598394931)
    ·
      refine ⟨22180292512760279397592397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14786861675173519598394931 22180292512760279397592397)
      ·
        refine ⟨8317609692285104774097149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22180292512760279397592397 8317609692285104774097149)
        ·
          refine ⟨3119103634606914290286431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8317609692285104774097149 3119103634606914290286431)
          ·
            refine ⟨4678655451910371435429647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119103634606914290286431 4678655451910371435429647)
            ·
              refine ⟨7017983177865557153144471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678655451910371435429647 7017983177865557153144471)
              ·
                refine ⟨10526974766798335729716707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7017983177865557153144471 10526974766798335729716707)
                ·
                  refine ⟨15790462150197503594575061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10526974766798335729716707 15790462150197503594575061)
                  ·
                    refine ⟨370088956645253990497853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15790462150197503594575061 370088956645253990497853)
                    ·
                      rfl

theorem cell23_2162237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2162237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162237 prefixEnd_2162237 := by exact prefixLift 2162237
  have htrace : WordTrace (prefixWord ++ tailWord_2162237) baseStart_2162237 baseEnd_2162237 := by
    simpa [prefixWord, tailWord_2162237, baseEnd_2162237] using wordTrace_append hprefix tailTrace_2162237
  have hstable : (prefixWord ++ tailWord_2162237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162237).length < 2 ^ (prefixWord ++ tailWord_2162237).sum := by decide
  have hdescent : baseEnd_2162237 < baseStart_2162237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162257 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 4, 4, 2]
def baseStart_2162257 : Nat := 118140960795 + 2162257 * 2 ^ 59
def prefixEnd_2162257 : Nat := 4983230072969 + 3 ^ 40 * 2162257 * 2
def baseEnd_2162257 : Nat := 1110277139548851893243467

theorem tailTrace_2162257 : CollatzResearch.WordTrace tailWord_2162257 prefixEnd_2162257 1110277139548851893243467 := by
  unfold tailWord_2162257
  simp only [CollatzResearch.WordTrace]
  refine ⟨78863991727519647940501025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52575994485013098627000683 78863991727519647940501025)
  ·
    refine ⟨59147993795639735955375769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78863991727519647940501025 59147993795639735955375769)
    ·
      refine ⟨44360995346729801966531827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59147993795639735955375769 44360995346729801966531827)
      ·
        refine ⟨66541493020094702949797741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44360995346729801966531827 66541493020094702949797741)
        ·
          refine ⟨24953059882535513606174153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66541493020094702949797741 24953059882535513606174153)
          ·
            refine ⟨18714794911901635204630615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24953059882535513606174153 18714794911901635204630615)
            ·
              refine ⟨28072192367852452806945923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18714794911901635204630615 28072192367852452806945923)
              ·
                refine ⟨42108288551778679210418885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28072192367852452806945923 42108288551778679210418885)
                ·
                  refine ⟨7895304103458502351953541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42108288551778679210418885 7895304103458502351953541)
                  ·
                    refine ⟨1480369519398469190991289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7895304103458502351953541 1480369519398469190991289)
                    ·
                      refine ⟨1110277139548851893243467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480369519398469190991289 1110277139548851893243467)
                      ·
                        rfl

theorem cell23_2162257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_2162257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162257 prefixEnd_2162257 := by exact prefixLift 2162257
  have htrace : WordTrace (prefixWord ++ tailWord_2162257) baseStart_2162257 baseEnd_2162257 := by
    simpa [prefixWord, tailWord_2162257, baseEnd_2162257] using wordTrace_append hprefix tailTrace_2162257
  have hstable : (prefixWord ++ tailWord_2162257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162257).length < 2 ^ (prefixWord ++ tailWord_2162257).sum := by decide
  have hdescent : baseEnd_2162257 < baseStart_2162257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162277 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_2162277 : Nat := 118140960795 + 2162277 * 2 ^ 59
def prefixEnd_2162277 : Nat := 4983230072969 + 3 ^ 40 * 2162277 * 2
def baseEnd_2162277 : Nat := 1110287409161941814993375

theorem tailTrace_2162277 : CollatzResearch.WordTrace tailWord_2162277 prefixEnd_2162277 1110287409161941814993375 := by
  unfold tailWord_2162277
  simp only [CollatzResearch.WordTrace]
  refine ⟨78864721187447191356229085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52576480791631460904152723 78864721187447191356229085)
  ·
    refine ⟨29574270445292696758585907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78864721187447191356229085 29574270445292696758585907)
    ·
      refine ⟨44361405667939045137878861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29574270445292696758585907 44361405667939045137878861)
      ·
        refine ⟨16635527125477141926704573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44361405667939045137878861 16635527125477141926704573)
        ·
          refine ⟨6238322672053928222514215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16635527125477141926704573 6238322672053928222514215)
          ·
            refine ⟨9357484008080892333771323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238322672053928222514215 9357484008080892333771323)
            ·
              refine ⟨14036226012121338500656985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9357484008080892333771323 14036226012121338500656985)
              ·
                refine ⟨10527169509091003875492739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14036226012121338500656985 10527169509091003875492739)
                ·
                  refine ⟨15790754263636505813239109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10527169509091003875492739 15790754263636505813239109)
                  ·
                    refine ⟨2960766424431844839982333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15790754263636505813239109 2960766424431844839982333)
                    ·
                      refine ⟨1110287409161941814993375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2960766424431844839982333 1110287409161941814993375)
                      ·
                        rfl

theorem cell23_2162277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_2162277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162277 prefixEnd_2162277 := by exact prefixLift 2162277
  have htrace : WordTrace (prefixWord ++ tailWord_2162277) baseStart_2162277 baseEnd_2162277 := by
    simpa [prefixWord, tailWord_2162277, baseEnd_2162277] using wordTrace_append hprefix tailTrace_2162277
  have hstable : (prefixWord ++ tailWord_2162277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162277).length < 2 ^ (prefixWord ++ tailWord_2162277).sum := by decide
  have hdescent : baseEnd_2162277 < baseStart_2162277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162294 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2162294 : Nat := 118140960795 + 2162294 * 2 ^ 59
def prefixEnd_2162294 : Nat := 4983230072969 + 3 ^ 40 * 2162294 * 2
def baseEnd_2162294 : Nat := 1110296138333068248480797

theorem tailTrace_2162294 : CollatzResearch.WordTrace tailWord_2162294 prefixEnd_2162294 1110296138333068248480797 := by
  unfold tailWord_2162294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929083826774100203724871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52576894152257068839731957 4929083826774100203724871)
  ·
    refine ⟨7393625740161150305587307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4929083826774100203724871 7393625740161150305587307)
    ·
      refine ⟨11090438610241725458380961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7393625740161150305587307 11090438610241725458380961)
      ·
        refine ⟨8317828957681294093785721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11090438610241725458380961 8317828957681294093785721)
        ·
          refine ⟨6238371718260970570339291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8317828957681294093785721 6238371718260970570339291)
          ·
            refine ⟨9357557577391455855508937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238371718260970570339291 9357557577391455855508937)
            ·
              refine ⟨7018168183043591891631703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9357557577391455855508937 7018168183043591891631703)
              ·
                refine ⟨10527252274565387837447555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7018168183043591891631703 10527252274565387837447555)
                ·
                  refine ⟨15790878411848081756171333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10527252274565387837447555 15790878411848081756171333)
                  ·
                    refine ⟨2960789702221515329282125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15790878411848081756171333 2960789702221515329282125)
                    ·
                      refine ⟨1110296138333068248480797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2960789702221515329282125 1110296138333068248480797)
                      ·
                        rfl

theorem cell23_2162294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2162294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162294 prefixEnd_2162294 := by exact prefixLift 2162294
  have htrace : WordTrace (prefixWord ++ tailWord_2162294) baseStart_2162294 baseEnd_2162294 := by
    simpa [prefixWord, tailWord_2162294, baseEnd_2162294] using wordTrace_append hprefix tailTrace_2162294
  have hstable : (prefixWord ++ tailWord_2162294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162294).length < 2 ^ (prefixWord ++ tailWord_2162294).sum := by decide
  have hdescent : baseEnd_2162294 < baseStart_2162294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162301 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_2162301 : Nat := 118140960795 + 2162301 * 2 ^ 59
def prefixEnd_2162301 : Nat := 4983230072969 + 3 ^ 40 * 2162301 * 2
def baseEnd_2162301 : Nat := 370099910899216573697755

theorem tailTrace_2162301 : CollatzResearch.WordTrace tailWord_2162301 prefixEnd_2162301 370099910899216573697755 := by
  unfold tailWord_2162301
  simp only [CollatzResearch.WordTrace]
  refine ⟨78865596539360243455102757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52577064359573495636735171 78865596539360243455102757)
  ·
    refine ⟨14787299351130045647831767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78865596539360243455102757 14787299351130045647831767)
    ·
      refine ⟨22180949026695068471747651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14787299351130045647831767 22180949026695068471747651)
      ·
        refine ⟨33271423540042602707621477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22180949026695068471747651 33271423540042602707621477)
        ·
          refine ⟨6238391913757988007679027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33271423540042602707621477 6238391913757988007679027)
          ·
            refine ⟨9357587870636982011518541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238391913757988007679027 9357587870636982011518541)
            ·
              refine ⟨3509095451488868254319453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9357587870636982011518541 3509095451488868254319453)
              ·
                refine ⟨1315910794308325595369795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3509095451488868254319453 1315910794308325595369795)
                ·
                  refine ⟨1973866191462488393054693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315910794308325595369795 1973866191462488393054693)
                  ·
                    refine ⟨370099910899216573697755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1973866191462488393054693 370099910899216573697755)
                    ·
                      rfl

theorem cell23_2162301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_2162301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162301 prefixEnd_2162301 := by exact prefixLift 2162301
  have htrace : WordTrace (prefixWord ++ tailWord_2162301) baseStart_2162301 baseEnd_2162301 := by
    simpa [prefixWord, tailWord_2162301, baseEnd_2162301] using wordTrace_append hprefix tailTrace_2162301
  have hstable : (prefixWord ++ tailWord_2162301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162301).length < 2 ^ (prefixWord ++ tailWord_2162301).sum := by decide
  have hdescent : baseEnd_2162301 < baseStart_2162301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162318 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_2162318 : Nat := 118140960795 + 2162318 * 2 ^ 59
def prefixEnd_2162318 : Nat := 4983230072969 + 3 ^ 40 * 2162318 * 2
def baseEnd_2162318 : Nat := 370102820622925384860229

theorem tailTrace_2162318 : CollatzResearch.WordTrace tailWord_2162318 prefixEnd_2162318 370102820622925384860229 := by
  unfold tailWord_2162318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9858277072537331919808951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52577477720199103572314405 9858277072537331919808951)
  ·
    refine ⟨14787415608805997879713427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9858277072537331919808951 14787415608805997879713427)
    ·
      refine ⟨22181123413208996819570141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14787415608805997879713427 22181123413208996819570141)
      ·
        refine ⟨8317921279953373807338803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22181123413208996819570141 8317921279953373807338803)
        ·
          refine ⟨12476881919930060711008205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8317921279953373807338803 12476881919930060711008205)
          ·
            refine ⟨4678830719973772766628077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12476881919930060711008205 4678830719973772766628077)
            ·
              refine ⟨1754561519990164787485529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4678830719973772766628077 1754561519990164787485529)
              ·
                refine ⟨1315921139992623590614147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1754561519990164787485529 1315921139992623590614147)
                ·
                  refine ⟨1973881709988935385921221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315921139992623590614147 1973881709988935385921221)
                  ·
                    refine ⟨370102820622925384860229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1973881709988935385921221 370102820622925384860229)
                    ·
                      rfl

theorem cell23_2162318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_2162318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162318 prefixEnd_2162318 := by exact prefixLift 2162318
  have htrace : WordTrace (prefixWord ++ tailWord_2162318) baseStart_2162318 baseEnd_2162318 := by
    simpa [prefixWord, tailWord_2162318, baseEnd_2162318] using wordTrace_append hprefix tailTrace_2162318
  have hstable : (prefixWord ++ tailWord_2162318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162318).length < 2 ^ (prefixWord ++ tailWord_2162318).sum := by decide
  have hdescent : baseEnd_2162318 < baseStart_2162318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162381 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2162381 : Nat := 118140960795 + 2162381 * 2 ^ 59
def prefixEnd_2162381 : Nat := 4983230072969 + 3 ^ 40 * 2162381 * 2
def baseEnd_2162381 : Nat := 1110340811150009408092897

theorem tailTrace_2162381 : CollatzResearch.WordTrace tailWord_2162381 prefixEnd_2162381 1110340811150009408092897 := by
  unfold tailWord_2162381
  simp only [CollatzResearch.WordTrace]
  refine ⟨78868514379070417118014997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52579009586046944745343331 78868514379070417118014997)
  ·
    refine ⟨3696961611518925802406953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78868514379070417118014997 3696961611518925802406953)
    ·
      refine ⟨2772721208639194351805215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3696961611518925802406953 2772721208639194351805215)
      ·
        refine ⟨4159081812958791527707823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772721208639194351805215 4159081812958791527707823)
        ·
          refine ⟨6238622719438187291561735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159081812958791527707823 6238622719438187291561735)
          ·
            refine ⟨9357934079157280937342603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238622719438187291561735 9357934079157280937342603)
            ·
              refine ⟨14036901118735921406013905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9357934079157280937342603 14036901118735921406013905)
              ·
                refine ⟨10527675839051941054510429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14036901118735921406013905 10527675839051941054510429)
                ·
                  refine ⟨3947878439644477895441411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10527675839051941054510429 3947878439644477895441411)
                  ·
                    refine ⟨5921817659466716843162117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947878439644477895441411 5921817659466716843162117)
                    ·
                      refine ⟨1110340811150009408092897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5921817659466716843162117 1110340811150009408092897)
                      ·
                        rfl

theorem cell23_2162381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2162381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162381 prefixEnd_2162381 := by exact prefixLift 2162381
  have htrace : WordTrace (prefixWord ++ tailWord_2162381) baseStart_2162381 baseEnd_2162381 := by
    simpa [prefixWord, tailWord_2162381, baseEnd_2162381] using wordTrace_append hprefix tailTrace_2162381
  have hstable : (prefixWord ++ tailWord_2162381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162381).length < 2 ^ (prefixWord ++ tailWord_2162381).sum := by decide
  have hdescent : baseEnd_2162381 < baseStart_2162381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162394 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_2162394 : Nat := 118140960795 + 2162394 * 2 ^ 59
def prefixEnd_2162394 : Nat := 4983230072969 + 3 ^ 40 * 2162394 * 2
def baseEnd_2162394 : Nat := 1110347486398517857230337

theorem tailTrace_2162394 : CollatzResearch.WordTrace tailWord_2162394 prefixEnd_2162394 1110347486398517857230337 := by
  unfold tailWord_2162394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19717247132005830084559559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52579325685348880225492157 19717247132005830084559559)
  ·
    refine ⟨29575870698008745126839339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19717247132005830084559559 29575870698008745126839339)
    ·
      refine ⟨44363806047013117690259009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29575870698008745126839339 44363806047013117690259009)
      ·
        refine ⟨33272854535259838267694257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44363806047013117690259009 33272854535259838267694257)
        ·
          refine ⟨24954640901444878700770693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33272854535259838267694257 24954640901444878700770693)
          ·
            refine ⟨4678995169020914756394505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24954640901444878700770693 4678995169020914756394505)
            ·
              refine ⟨3509246376765686067295879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4678995169020914756394505 3509246376765686067295879)
              ·
                refine ⟨5263869565148529100943819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509246376765686067295879 5263869565148529100943819)
                ·
                  refine ⟨7895804347722793651415729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263869565148529100943819 7895804347722793651415729)
                  ·
                    refine ⟨5921853260792095238561797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7895804347722793651415729 5921853260792095238561797)
                    ·
                      refine ⟨1110347486398517857230337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5921853260792095238561797 1110347486398517857230337)
                      ·
                        rfl

theorem cell23_2162394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_2162394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162394 prefixEnd_2162394 := by exact prefixLift 2162394
  have htrace : WordTrace (prefixWord ++ tailWord_2162394) baseStart_2162394 baseEnd_2162394 := by
    simpa [prefixWord, tailWord_2162394, baseEnd_2162394] using wordTrace_append hprefix tailTrace_2162394
  have hstable : (prefixWord ++ tailWord_2162394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162394).length < 2 ^ (prefixWord ++ tailWord_2162394).sum := by decide
  have hdescent : baseEnd_2162394 < baseStart_2162394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162414 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_2162414 : Nat := 118140960795 + 2162414 * 2 ^ 59
def prefixEnd_2162414 : Nat := 4983230072969 + 3 ^ 40 * 2162414 * 2
def baseEnd_2162414 : Nat := 1110357756011607778980245

theorem tailTrace_2162414 : CollatzResearch.WordTrace tailWord_2162414 prefixEnd_2162414 1110357756011607778980245 := by
  unfold tailWord_2162414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9858714748493857969245787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52579811991967242502644197 9858714748493857969245787)
  ·
    refine ⟨14788072122740786953868681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9858714748493857969245787 14788072122740786953868681)
    ·
      refine ⟨11091054092055590215401511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14788072122740786953868681 11091054092055590215401511)
      ·
        refine ⟨16636581138083385323102267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11091054092055590215401511 16636581138083385323102267)
        ·
          refine ⟨24954871707125077984653401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16636581138083385323102267 24954871707125077984653401)
          ·
            refine ⟨18716153780343808488490051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24954871707125077984653401 18716153780343808488490051)
            ·
              refine ⟨28074230670515712732735077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18716153780343808488490051 28074230670515712732735077)
              ·
                refine ⟨5263918250721696137387827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28074230670515712732735077 5263918250721696137387827)
                ·
                  refine ⟨7895877376082544206081741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263918250721696137387827 7895877376082544206081741)
                  ·
                    refine ⟨2960954016030954077280653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7895877376082544206081741 2960954016030954077280653)
                    ·
                      refine ⟨1110357756011607778980245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2960954016030954077280653 1110357756011607778980245)
                      ·
                        rfl

theorem cell23_2162414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_2162414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162414 prefixEnd_2162414 := by exact prefixLift 2162414
  have htrace : WordTrace (prefixWord ++ tailWord_2162414) baseStart_2162414 baseEnd_2162414 := by
    simpa [prefixWord, tailWord_2162414, baseEnd_2162414] using wordTrace_append hprefix tailTrace_2162414
  have hstable : (prefixWord ++ tailWord_2162414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162414).length < 2 ^ (prefixWord ++ tailWord_2162414).sum := by decide
  have hdescent : baseEnd_2162414 < baseStart_2162414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162424 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 5, 3, 2]
def baseStart_2162424 : Nat := 118140960795 + 2162424 * 2 ^ 59
def prefixEnd_2162424 : Nat := 4983230072969 + 3 ^ 40 * 2162424 * 2
def baseEnd_2162424 : Nat := 1110362890818152739855199

theorem tailTrace_2162424 : CollatzResearch.WordTrace tailWord_2162424 prefixEnd_2162424 1110362890818152739855199 := by
  unfold tailWord_2162424
  simp only [CollatzResearch.WordTrace]
  refine ⟨39435041358957317730915163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52580055145276423641220217 39435041358957317730915163)
  ·
    refine ⟨59152562038435976596372745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39435041358957317730915163 59152562038435976596372745)
    ·
      refine ⟨44364421528826982447279559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59152562038435976596372745 44364421528826982447279559)
      ·
        refine ⟨66546632293240473670919339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44364421528826982447279559 66546632293240473670919339)
        ·
          refine ⟨99819948439860710506379009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66546632293240473670919339 99819948439860710506379009)
          ·
            refine ⟨74864961329895532879784257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99819948439860710506379009 74864961329895532879784257)
            ·
              refine ⟨56148720997421649659838193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74864961329895532879784257 56148720997421649659838193)
              ·
                refine ⟨42111540748066237244878645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56148720997421649659838193 42111540748066237244878645)
                ·
                  refine ⟨3947956945131209741707373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42111540748066237244878645 3947956945131209741707373)
                  ·
                    refine ⟨1480483854424203653140265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3947956945131209741707373 1480483854424203653140265)
                    ·
                      refine ⟨1110362890818152739855199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480483854424203653140265 1110362890818152739855199)
                      ·
                        rfl

theorem cell23_2162424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_2162424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162424 prefixEnd_2162424 := by exact prefixLift 2162424
  have htrace : WordTrace (prefixWord ++ tailWord_2162424) baseStart_2162424 baseEnd_2162424 := by
    simpa [prefixWord, tailWord_2162424, baseEnd_2162424] using wordTrace_append hprefix tailTrace_2162424
  have hstable : (prefixWord ++ tailWord_2162424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162424).length < 2 ^ (prefixWord ++ tailWord_2162424).sum := by decide
  have hdescent : baseEnd_2162424 < baseStart_2162424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162431 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 3]
def baseStart_2162431 : Nat := 118140960795 + 2162431 * 2 ^ 59
def prefixEnd_2162431 : Nat := 4983230072969 + 3 ^ 40 * 2162431 * 2
def baseEnd_2162431 : Nat := 1110366485182734212467667

theorem tailTrace_2162431 : CollatzResearch.WordTrace tailWord_2162431 prefixEnd_2162431 1110366485182734212467667 := by
  unfold tailWord_2162431
  simp only [CollatzResearch.WordTrace]
  refine ⟨78870338028889275657335147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52580225352592850438223431 78870338028889275657335147)
  ·
    refine ⟨118305507043333913486002721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78870338028889275657335147 118305507043333913486002721)
    ·
      refine ⟨88729130282500435114502041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118305507043333913486002721 88729130282500435114502041)
      ·
        refine ⟨66546847711875326335876531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88729130282500435114502041 66546847711875326335876531)
        ·
          refine ⟨99820271567812989503814797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66546847711875326335876531 99820271567812989503814797)
          ·
            refine ⟨37432601837929871063930549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99820271567812989503814797 37432601837929871063930549)
            ·
              refine ⟨3509306422305925412243489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37432601837929871063930549 3509306422305925412243489)
              ·
                refine ⟨2631979816729444059182617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509306422305925412243489 2631979816729444059182617)
                ·
                  refine ⟨1973984862547083044386963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631979816729444059182617 1973984862547083044386963)
                  ·
                    refine ⟨2960977293820624566580445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1973984862547083044386963 2960977293820624566580445)
                    ·
                      refine ⟨1110366485182734212467667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2960977293820624566580445 1110366485182734212467667)
                      ·
                        rfl

theorem cell23_2162431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_2162431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162431 prefixEnd_2162431 := by exact prefixLift 2162431
  have htrace : WordTrace (prefixWord ++ tailWord_2162431) baseStart_2162431 baseEnd_2162431 := by
    simpa [prefixWord, tailWord_2162431, baseEnd_2162431] using wordTrace_append hprefix tailTrace_2162431
  have hstable : (prefixWord ++ tailWord_2162431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162431).length < 2 ^ (prefixWord ++ tailWord_2162431).sum := by decide
  have hdescent : baseEnd_2162431 < baseStart_2162431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162445 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2162445 : Nat := 118140960795 + 2162445 * 2 ^ 59
def prefixEnd_2162445 : Nat := 4983230072969 + 3 ^ 40 * 2162445 * 2
def baseEnd_2162445 : Nat := 1110373673911897157692603

theorem tailTrace_2162445 : CollatzResearch.WordTrace tailWord_2162445 prefixEnd_2162445 1110373673911897157692603 := by
  unfold tailWord_2162445
  simp only [CollatzResearch.WordTrace]
  refine ⟨78870848650838556048344789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52580565767225704032229859 78870848650838556048344789)
  ·
    refine ⟨1848535515254028657383081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 78870848650838556048344789 1848535515254028657383081)
    ·
      refine ⟨1386401636440521493037311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1848535515254028657383081 1386401636440521493037311)
      ·
        refine ⟨2079602454660782239555967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386401636440521493037311 2079602454660782239555967)
        ·
          refine ⟨3119403681991173359333951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079602454660782239555967 3119403681991173359333951)
          ·
            refine ⟨4679105522986760039000927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119403681991173359333951 4679105522986760039000927)
            ·
              refine ⟨7018658284480140058501391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679105522986760039000927 7018658284480140058501391)
              ·
                refine ⟨10527987426720210087752087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7018658284480140058501391 10527987426720210087752087)
                ·
                  refine ⟨15791981140080315131628131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10527987426720210087752087 15791981140080315131628131)
                  ·
                    refine ⟨23687971710120472697442197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15791981140080315131628131 23687971710120472697442197)
                    ·
                      refine ⟨1110373673911897157692603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23687971710120472697442197 1110373673911897157692603)
                      ·
                        rfl

theorem cell23_2162445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2162445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162445 prefixEnd_2162445 := by exact prefixLift 2162445
  have htrace : WordTrace (prefixWord ++ tailWord_2162445) baseStart_2162445 baseEnd_2162445 := by
    simpa [prefixWord, tailWord_2162445, baseEnd_2162445] using wordTrace_append hprefix tailTrace_2162445
  have hstable : (prefixWord ++ tailWord_2162445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162445).length < 2 ^ (prefixWord ++ tailWord_2162445).sum := by decide
  have hdescent : baseEnd_2162445 < baseStart_2162445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162452 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2162452 : Nat := 118140960795 + 2162452 * 2 ^ 59
def prefixEnd_2162452 : Nat := 4983230072969 + 3 ^ 40 * 2162452 * 2
def baseEnd_2162452 : Nat := 1110377268276478630305071

theorem tailTrace_2162452 : CollatzResearch.WordTrace tailWord_2162452 prefixEnd_2162452 1110377268276478630305071 := by
  unfold tailWord_2162452
  simp only [CollatzResearch.WordTrace]
  refine ⟨39435551980906598121924805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52580735974542130829233073 39435551980906598121924805)
  ·
    refine ⟨7394165996419987147860901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39435551980906598121924805 7394165996419987147860901)
    ·
      refine ⟨1386406124328747590223919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7394165996419987147860901 1386406124328747590223919)
      ·
        refine ⟨2079609186493121385335879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386406124328747590223919 2079609186493121385335879)
        ·
          refine ⟨3119413779739682078003819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079609186493121385335879 3119413779739682078003819)
          ·
            refine ⟨4679120669609523117005729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119413779739682078003819 4679120669609523117005729)
            ·
              refine ⟨3509340502207142337754297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4679120669609523117005729 3509340502207142337754297)
              ·
                refine ⟨2632005376655356753315723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509340502207142337754297 2632005376655356753315723)
                ·
                  refine ⟨3948008064983035129973585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632005376655356753315723 3948008064983035129973585)
                  ·
                    refine ⟨2961006048737276347480189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948008064983035129973585 2961006048737276347480189)
                    ·
                      refine ⟨1110377268276478630305071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2961006048737276347480189 1110377268276478630305071)
                      ·
                        rfl

theorem cell23_2162452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2162452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162452 prefixEnd_2162452 := by exact prefixLift 2162452
  have htrace : WordTrace (prefixWord ++ tailWord_2162452) baseStart_2162452 baseEnd_2162452 := by
    simpa [prefixWord, tailWord_2162452, baseEnd_2162452] using wordTrace_append hprefix tailTrace_2162452
  have hstable : (prefixWord ++ tailWord_2162452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162452).length < 2 ^ (prefixWord ++ tailWord_2162452).sum := by decide
  have hdescent : baseEnd_2162452 < baseStart_2162452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162457 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_2162457 : Nat := 118140960795 + 2162457 * 2 ^ 59
def prefixEnd_2162457 : Nat := 4983230072969 + 3 ^ 40 * 2162457 * 2
def baseEnd_2162457 : Nat := 1110379835679751110742547

theorem tailTrace_2162457 : CollatzResearch.WordTrace tailWord_2162457 prefixEnd_2162457 1110379835679751110742547 := by
  unfold tailWord_2162457
  simp only [CollatzResearch.WordTrace]
  refine ⟨78871286326795082097781625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52580857551196721398521083 78871286326795082097781625)
  ·
    refine ⟨59153464745096311573336219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78871286326795082097781625 59153464745096311573336219)
    ·
      refine ⟨88730197117644467360004329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59153464745096311573336219 88730197117644467360004329)
      ·
        refine ⟨66547647838233350520003247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88730197117644467360004329 66547647838233350520003247)
        ·
          refine ⟨99821471757350025780004871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66547647838233350520003247 99821471757350025780004871)
          ·
            refine ⟨149732207636025038670007307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99821471757350025780004871 149732207636025038670007307)
            ·
              refine ⟨224598311454037558005010961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149732207636025038670007307 224598311454037558005010961)
              ·
                refine ⟨168448733590528168503758221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224598311454037558005010961 168448733590528168503758221)
                ·
                  refine ⟨63168275096448063188909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168448733590528168503758221 63168275096448063188909333)
                  ·
                    refine ⟨2961012895146002961980125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63168275096448063188909333 2961012895146002961980125)
                    ·
                      refine ⟨1110379835679751110742547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2961012895146002961980125 1110379835679751110742547)
                      ·
                        rfl

theorem cell23_2162457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_2162457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162457 prefixEnd_2162457 := by exact prefixLift 2162457
  have htrace : WordTrace (prefixWord ++ tailWord_2162457) baseStart_2162457 baseEnd_2162457 := by
    simpa [prefixWord, tailWord_2162457, baseEnd_2162457] using wordTrace_append hprefix tailTrace_2162457
  have hstable : (prefixWord ++ tailWord_2162457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162457).length < 2 ^ (prefixWord ++ tailWord_2162457).sum := by decide
  have hdescent : baseEnd_2162457 < baseStart_2162457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162458 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2]
def baseStart_2162458 : Nat := 118140960795 + 2162458 * 2 ^ 59
def prefixEnd_2162458 : Nat := 4983230072969 + 3 ^ 40 * 2162458 * 2
def baseEnd_2162458 : Nat := 1110380349160405606830043

theorem tailTrace_2162458 : CollatzResearch.WordTrace tailWord_2162458 prefixEnd_2162458 1110380349160405606830043 := by
  unfold tailWord_2162458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19717830699947864817142007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52580881866527639512378685 19717830699947864817142007)
  ·
    refine ⟨29576746049921797225713011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19717830699947864817142007 29576746049921797225713011)
    ·
      refine ⟨44365119074882695838569517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29576746049921797225713011 44365119074882695838569517)
      ·
        refine ⟨16636919653081010939463569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44365119074882695838569517 16636919653081010939463569)
        ·
          refine ⟨12477689739810758204597677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16636919653081010939463569 12477689739810758204597677)
          ·
            refine ⟨4679133652429034326724129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12477689739810758204597677 4679133652429034326724129)
            ·
              refine ⟨3509350239321775745043097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4679133652429034326724129 3509350239321775745043097)
              ·
                refine ⟨2632012679491331808782323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509350239321775745043097 2632012679491331808782323)
                ·
                  refine ⟨3948019019236997713173485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632012679491331808782323 3948019019236997713173485)
                  ·
                    refine ⟨1480507132213874142440057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3948019019236997713173485 1480507132213874142440057)
                    ·
                      refine ⟨1110380349160405606830043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480507132213874142440057 1110380349160405606830043)
                      ·
                        rfl

theorem cell23_2162458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_2162458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162458 prefixEnd_2162458 := by exact prefixLift 2162458
  have htrace : WordTrace (prefixWord ++ tailWord_2162458) baseStart_2162458 baseEnd_2162458 := by
    simpa [prefixWord, tailWord_2162458, baseEnd_2162458] using wordTrace_append hprefix tailTrace_2162458
  have hstable : (prefixWord ++ tailWord_2162458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162458).length < 2 ^ (prefixWord ++ tailWord_2162458).sum := by decide
  have hdescent : baseEnd_2162458 < baseStart_2162458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162467 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2162467 : Nat := 118140960795 + 2162467 * 2 ^ 59
def prefixEnd_2162467 : Nat := 4983230072969 + 3 ^ 40 * 2162467 * 2
def baseEnd_2162467 : Nat := 1110384970486296071617501

theorem tailTrace_2162467 : CollatzResearch.WordTrace tailWord_2162467 prefixEnd_2162467 1110384970486296071617501 := by
  unfold tailWord_2162467
  simp only [CollatzResearch.WordTrace]
  refine ⟨78871651056758853805645655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52581100704505902537097103 78871651056758853805645655)
  ·
    refine ⟨118307476585138280708468483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78871651056758853805645655 118307476585138280708468483)
    ·
      refine ⟨177461214877707421062702725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118307476585138280708468483 177461214877707421062702725)
      ·
        refine ⟨33273977789570141449256761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177461214877707421062702725 33273977789570141449256761)
        ·
          refine ⟨24955483342177606086942571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33273977789570141449256761 24955483342177606086942571)
          ·
            refine ⟨37433225013266409130413857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24955483342177606086942571 37433225013266409130413857)
            ·
              refine ⟨28074918759949806847810393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37433225013266409130413857 28074918759949806847810393)
              ·
                refine ⟨21056189069962355135857795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28074918759949806847810393 21056189069962355135857795)
                ·
                  refine ⟨31584283604943532703786693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21056189069962355135857795 31584283604943532703786693)
                  ·
                    refine ⟨5922053175926912381960005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31584283604943532703786693 5922053175926912381960005)
                    ·
                      refine ⟨1110384970486296071617501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5922053175926912381960005 1110384970486296071617501)
                      ·
                        rfl

theorem cell23_2162467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2162467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162467 prefixEnd_2162467 := by exact prefixLift 2162467
  have htrace : WordTrace (prefixWord ++ tailWord_2162467) baseStart_2162467 baseEnd_2162467 := by
    simpa [prefixWord, tailWord_2162467, baseEnd_2162467] using wordTrace_append hprefix tailTrace_2162467
  have hstable : (prefixWord ++ tailWord_2162467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162467).length < 2 ^ (prefixWord ++ tailWord_2162467).sum := by decide
  have hdescent : baseEnd_2162467 < baseStart_2162467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162547 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_2162547 : Nat := 118140960795 + 2162547 * 2 ^ 59
def prefixEnd_2162547 : Nat := 4983230072969 + 3 ^ 40 * 2162547 * 2
def baseEnd_2162547 : Nat := 1110426048938655758617133

theorem tailTrace_2162547 : CollatzResearch.WordTrace tailWord_2162547 prefixEnd_2162547 1110426048938655758617133 := by
  unfold tailWord_2162547
  simp only [CollatzResearch.WordTrace]
  refine ⟨78874568896469027468557895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52583045930979351645705263 78874568896469027468557895)
  ·
    refine ⟨118311853344703541202836843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78874568896469027468557895 118311853344703541202836843)
    ·
      refine ⟨177467780017055311804255265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118311853344703541202836843 177467780017055311804255265)
      ·
        refine ⟨133100835012791483853191449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177467780017055311804255265 133100835012791483853191449)
        ·
          refine ⟨99825626259593612889893587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133100835012791483853191449 99825626259593612889893587)
          ·
            refine ⟨149738439389390419334840381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99825626259593612889893587 149738439389390419334840381)
            ·
              refine ⟨56151914771021407250565143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149738439389390419334840381 56151914771021407250565143)
              ·
                refine ⟨84227872156532110875847715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56151914771021407250565143 84227872156532110875847715)
                ·
                  refine ⟨126341808234798166313771573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84227872156532110875847715 126341808234798166313771573)
                  ·
                    refine ⟨11844544522012328091916085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126341808234798166313771573 11844544522012328091916085)
                    ·
                      refine ⟨1110426048938655758617133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11844544522012328091916085 1110426048938655758617133)
                      ·
                        rfl

theorem cell23_2162547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_2162547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162547 prefixEnd_2162547 := by exact prefixLift 2162547
  have htrace : WordTrace (prefixWord ++ tailWord_2162547) baseStart_2162547 baseEnd_2162547 := by
    simpa [prefixWord, tailWord_2162547, baseEnd_2162547] using wordTrace_append hprefix tailTrace_2162547
  have hstable : (prefixWord ++ tailWord_2162547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162547).length < 2 ^ (prefixWord ++ tailWord_2162547).sum := by decide
  have hdescent : baseEnd_2162547 < baseStart_2162547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162578 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2162578 : Nat := 118140960795 + 2162578 * 2 ^ 59
def prefixEnd_2162578 : Nat := 4983230072969 + 3 ^ 40 * 2162578 * 2
def baseEnd_2162578 : Nat := 1110441966838945137329491

theorem tailTrace_2162578 : CollatzResearch.WordTrace tailWord_2162578 prefixEnd_2162578 1110441966838945137329491 := by
  unfold tailWord_2162578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19718924889839179940734097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52583799706237813175290925 19718924889839179940734097)
  ·
    refine ⟨14789193667379384955550573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19718924889839179940734097 14789193667379384955550573)
    ·
      refine ⟨5545947625267269358331465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14789193667379384955550573 5545947625267269358331465)
      ·
        refine ⟨4159460718950452018748599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5545947625267269358331465 4159460718950452018748599)
        ·
          refine ⟨6239191078425678028122899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159460718950452018748599 6239191078425678028122899)
          ·
            refine ⟨9358786617638517042184349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6239191078425678028122899 9358786617638517042184349)
            ·
              refine ⟨3509544981614443890819131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9358786617638517042184349 3509544981614443890819131)
              ·
                refine ⟨5264317472421665836228697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509544981614443890819131 5264317472421665836228697)
                ·
                  refine ⟨3948238104316249377171523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5264317472421665836228697 3948238104316249377171523)
                  ·
                    refine ⟨5922357156474374065757285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3948238104316249377171523 5922357156474374065757285)
                    ·
                      refine ⟨1110441966838945137329491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5922357156474374065757285 1110441966838945137329491)
                      ·
                        rfl

theorem cell23_2162578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2162578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162578 prefixEnd_2162578 := by exact prefixLift 2162578
  have htrace : WordTrace (prefixWord ++ tailWord_2162578) baseStart_2162578 baseEnd_2162578 := by
    simpa [prefixWord, tailWord_2162578, baseEnd_2162578] using wordTrace_append hprefix tailTrace_2162578
  have hstable : (prefixWord ++ tailWord_2162578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162578).length < 2 ^ (prefixWord ++ tailWord_2162578).sum := by decide
  have hdescent : baseEnd_2162578 < baseStart_2162578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162638 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_2162638 : Nat := 118140960795 + 2162638 * 2 ^ 59
def prefixEnd_2162638 : Nat := 4983230072969 + 3 ^ 40 * 2162638 * 2
def baseEnd_2162638 : Nat := 1110472775678214902579215

theorem tailTrace_2162638 : CollatzResearch.WordTrace tailWord_2162638 prefixEnd_2162638 1110472775678214902579215 := by
  unfold tailWord_2162638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9859735992392418751265071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52585258626092900006747045 9859735992392418751265071)
  ·
    refine ⟨14789603988588628126897607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9859735992392418751265071 14789603988588628126897607)
    ·
      refine ⟨22184405982882942190346411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14789603988588628126897607 22184405982882942190346411)
      ·
        refine ⟨33276608974324413285519617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22184405982882942190346411 33276608974324413285519617)
        ·
          refine ⟨24957456730743309964139713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33276608974324413285519617 24957456730743309964139713)
          ·
            refine ⟨18718092548057482473104785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24957456730743309964139713 18718092548057482473104785)
            ·
              refine ⟨14038569411043111854828589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18718092548057482473104785 14038569411043111854828589)
              ·
                refine ⟨5264463529141166945560721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14038569411043111854828589 5264463529141166945560721)
                ·
                  refine ⟨3948347646855875209170541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5264463529141166945560721 3948347646855875209170541)
                  ·
                    refine ⟨1480630367570953203438953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3948347646855875209170541 1480630367570953203438953)
                    ·
                      refine ⟨1110472775678214902579215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480630367570953203438953 1110472775678214902579215)
                      ·
                        rfl

theorem cell23_2162638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_2162638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162638 prefixEnd_2162638 := by exact prefixLift 2162638
  have htrace : WordTrace (prefixWord ++ tailWord_2162638) baseStart_2162638 baseEnd_2162638 := by
    simpa [prefixWord, tailWord_2162638, baseEnd_2162638] using wordTrace_append hprefix tailTrace_2162638
  have hstable : (prefixWord ++ tailWord_2162638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162638).length < 2 ^ (prefixWord ++ tailWord_2162638).sum := by decide
  have hdescent : baseEnd_2162638 < baseStart_2162638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162671 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_2162671 : Nat := 118140960795 + 2162671 * 2 ^ 59
def prefixEnd_2162671 : Nat := 4983230072969 + 3 ^ 40 * 2162671 * 2
def baseEnd_2162671 : Nat := 1110489720539813273466563

theorem tailTrace_2162671 : CollatzResearch.WordTrace tailWord_2162671 prefixEnd_2162671 1110489720539813273466563 := by
  unfold tailWord_2162671
  simp only [CollatzResearch.WordTrace]
  refine ⟨78879091548019796646071867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52586061032013197764047911 78879091548019796646071867)
  ·
    refine ⟨118318637322029694969107801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78879091548019796646071867 118318637322029694969107801)
    ·
      refine ⟨88738977991522271226830851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118318637322029694969107801 88738977991522271226830851)
      ·
        refine ⟨133108466987283406840246277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88738977991522271226830851 133108466987283406840246277)
        ·
          refine ⟨24957837560115638782546177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133108466987283406840246277 24957837560115638782546177)
          ·
            refine ⟨18718378170086729086909633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24957837560115638782546177 18718378170086729086909633)
            ·
              refine ⟨14038783627565046815182225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18718378170086729086909633 14038783627565046815182225)
              ·
                refine ⟨10529087720673785111386669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14038783627565046815182225 10529087720673785111386669)
                ·
                  refine ⟨3948407895252669416770001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10529087720673785111386669 3948407895252669416770001)
                  ·
                    refine ⟨2961305921439502062577501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948407895252669416770001 2961305921439502062577501)
                    ·
                      refine ⟨1110489720539813273466563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2961305921439502062577501 1110489720539813273466563)
                      ·
                        rfl

theorem cell23_2162671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_2162671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162671 prefixEnd_2162671 := by exact prefixLift 2162671
  have htrace : WordTrace (prefixWord ++ tailWord_2162671) baseStart_2162671 baseEnd_2162671 := by
    simpa [prefixWord, tailWord_2162671, baseEnd_2162671] using wordTrace_append hprefix tailTrace_2162671
  have hstable : (prefixWord ++ tailWord_2162671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162671).length < 2 ^ (prefixWord ++ tailWord_2162671).sum := by decide
  have hdescent : baseEnd_2162671 < baseStart_2162671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162698 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2162698 : Nat := 118140960795 + 2162698 * 2 ^ 59
def prefixEnd_2162698 : Nat := 4983230072969 + 3 ^ 40 * 2162698 * 2
def baseEnd_2162698 : Nat := 1110503584517484667828939

theorem tailTrace_2162698 : CollatzResearch.WordTrace tailWord_2162698 prefixEnd_2162698 1110503584517484667828939 := by
  unfold tailWord_2162698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19720019079730495064326187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52586717545947986838203165 19720019079730495064326187)
  ·
    refine ⟨29580028619595742596489281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19720019079730495064326187 29580028619595742596489281)
    ·
      refine ⟨22185021464696806947366961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29580028619595742596489281 22185021464696806947366961)
      ·
        refine ⟨16638766098522605210525221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22185021464696806947366961 16638766098522605210525221)
        ·
          refine ⟨3119768643472988476973479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16638766098522605210525221 3119768643472988476973479)
          ·
            refine ⟨4679652965209482715460219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119768643472988476973479 4679652965209482715460219)
            ·
              refine ⟨7019479447814224073190329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679652965209482715460219 7019479447814224073190329)
              ·
                refine ⟨5264609585860668054892747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7019479447814224073190329 5264609585860668054892747)
                ·
                  refine ⟨7896914378791002082339121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5264609585860668054892747 7896914378791002082339121)
                  ·
                    refine ⟨5922685784093251561754341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7896914378791002082339121 5922685784093251561754341)
                    ·
                      refine ⟨1110503584517484667828939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5922685784093251561754341 1110503584517484667828939)
                      ·
                        rfl

theorem cell23_2162698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2162698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162698 prefixEnd_2162698 := by exact prefixLift 2162698
  have htrace : WordTrace (prefixWord ++ tailWord_2162698) baseStart_2162698 baseEnd_2162698 := by
    simpa [prefixWord, tailWord_2162698, baseEnd_2162698] using wordTrace_append hprefix tailTrace_2162698
  have hstable : (prefixWord ++ tailWord_2162698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162698).length < 2 ^ (prefixWord ++ tailWord_2162698).sum := by decide
  have hdescent : baseEnd_2162698 < baseStart_2162698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162702 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_2162702 : Nat := 118140960795 + 2162702 * 2 ^ 59
def prefixEnd_2162702 : Nat := 4983230072969 + 3 ^ 40 * 2162702 * 2
def baseEnd_2162702 : Nat := 1110505638440102652178921

theorem tailTrace_2162702 : CollatzResearch.WordTrace tailWord_2162702 prefixEnd_2162702 1110505638440102652178921 := by
  unfold tailWord_2162702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860027776363436117556295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52586814807271659293633573 9860027776363436117556295)
  ·
    refine ⟨14790041664545154176334443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860027776363436117556295 14790041664545154176334443)
    ·
      refine ⟨22185062496817731264501665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14790041664545154176334443 22185062496817731264501665)
      ·
        refine ⟨16638796872613298448376249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22185062496817731264501665 16638796872613298448376249)
        ·
          refine ⟨12479097654459973836282187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16638796872613298448376249 12479097654459973836282187)
          ·
            refine ⟨18718646481689960754423281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12479097654459973836282187 18718646481689960754423281)
            ·
              refine ⟨14038984861267470565817461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18718646481689960754423281 14038984861267470565817461)
              ·
                refine ⟨1316154830743825365545387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14038984861267470565817461 1316154830743825365545387)
                ·
                  refine ⟨1974232246115738048318081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316154830743825365545387 1974232246115738048318081)
                  ·
                    refine ⟨1480674184586803536238561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1974232246115738048318081 1480674184586803536238561)
                    ·
                      refine ⟨1110505638440102652178921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480674184586803536238561 1110505638440102652178921)
                      ·
                        rfl

theorem cell23_2162702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_2162702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162702 prefixEnd_2162702 := by exact prefixLift 2162702
  have htrace : WordTrace (prefixWord ++ tailWord_2162702) baseStart_2162702 baseEnd_2162702 := by
    simpa [prefixWord, tailWord_2162702, baseEnd_2162702] using wordTrace_append hprefix tailTrace_2162702
  have hstable : (prefixWord ++ tailWord_2162702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162702).length < 2 ^ (prefixWord ++ tailWord_2162702).sum := by decide
  have hdescent : baseEnd_2162702 < baseStart_2162702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162708 : List Nat := [2, 4, 3, 2, 1, 11]
def baseStart_2162708 : Nat := 118140960795 + 2162708 * 2 ^ 59
def prefixEnd_2162708 : Nat := 4983230072969 + 3 ^ 40 * 2162708 * 2
def baseEnd_2162708 : Nat := 4569994729728516990551

theorem tailTrace_2162708 : CollatzResearch.WordTrace tailWord_2162708 prefixEnd_2162708 4569994729728516990551 := by
  unfold tailWord_2162708
  simp only [CollatzResearch.WordTrace]
  refine ⟨39440220524442875982584389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52586960699257167976779185 39440220524442875982584389)
  ·
    refine ⟨7395041348333039246734573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39440220524442875982584389 7395041348333039246734573)
    ·
      refine ⟨2773140505624889717525465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7395041348333039246734573 2773140505624889717525465)
      ·
        refine ⟨2079855379218667288144099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773140505624889717525465 2079855379218667288144099)
        ·
          refine ⟨3119783068828000932216149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079855379218667288144099 3119783068828000932216149)
          ·
            refine ⟨4569994729728516990551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3119783068828000932216149 4569994729728516990551)
            ·
              rfl

theorem cell23_2162708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 11].length) (baseStart_2162708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162708 prefixEnd_2162708 := by exact prefixLift 2162708
  have htrace : WordTrace (prefixWord ++ tailWord_2162708) baseStart_2162708 baseEnd_2162708 := by
    simpa [prefixWord, tailWord_2162708, baseEnd_2162708] using wordTrace_append hprefix tailTrace_2162708
  have hstable : (prefixWord ++ tailWord_2162708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162708).length < 2 ^ (prefixWord ++ tailWord_2162708).sum := by decide
  have hdescent : baseEnd_2162708 < baseStart_2162708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162875 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 1, 4]
def baseStart_2162875 : Nat := 118140960795 + 2162875 * 2 ^ 59
def prefixEnd_2162875 : Nat := 4983230072969 + 3 ^ 40 * 2162875 * 2
def baseEnd_2162875 : Nat := 370198156864443491771875

theorem tailTrace_2162875 : CollatzResearch.WordTrace tailWord_2162875 prefixEnd_2162875 370198156864443491771875 := by
  unfold tailWord_2162875
  simp only [CollatzResearch.WordTrace]
  refine ⟨78886532039280739486498079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52591021359520492990998719 78886532039280739486498079)
  ·
    refine ⟨118329798058921109229747119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78886532039280739486498079 118329798058921109229747119)
    ·
      refine ⟨177494697088381663844620679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118329798058921109229747119 177494697088381663844620679)
      ·
        refine ⟨266242045632572495766931019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177494697088381663844620679 266242045632572495766931019)
        ·
          refine ⟨399363068448858743650396529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266242045632572495766931019 399363068448858743650396529)
          ·
            refine ⟨299522301336644057737797397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399363068448858743650396529 299522301336644057737797397)
            ·
              refine ⟨14040107875155190206459253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 299522301336644057737797397 14040107875155190206459253)
              ·
                refine ⟨1316260113295799081855555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14040107875155190206459253 1316260113295799081855555)
                ·
                  refine ⟨1974390169943698622783333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316260113295799081855555 1974390169943698622783333)
                  ·
                    refine ⟨370198156864443491771875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974390169943698622783333 370198156864443491771875)
                    ·
                      rfl

theorem cell23_2162875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 4].length) (baseStart_2162875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162875 prefixEnd_2162875 := by exact prefixLift 2162875
  have htrace : WordTrace (prefixWord ++ tailWord_2162875) baseStart_2162875 baseEnd_2162875 := by
    simpa [prefixWord, tailWord_2162875, baseEnd_2162875] using wordTrace_append hprefix tailTrace_2162875
  have hstable : (prefixWord ++ tailWord_2162875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162875).length < 2 ^ (prefixWord ++ tailWord_2162875).sum := by decide
  have hdescent : baseEnd_2162875 < baseStart_2162875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162891 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_2162891 : Nat := 118140960795 + 2162891 * 2 ^ 59
def prefixEnd_2162891 : Nat := 4983230072969 + 3 ^ 40 * 2162891 * 2
def baseEnd_2162891 : Nat := 1110602686283802412715551

theorem tailTrace_2162891 : CollatzResearch.WordTrace tailWord_2162891 prefixEnd_2162891 1110602686283802412715551 := by
  unfold tailWord_2162891
  simp only [CollatzResearch.WordTrace]
  refine ⟨78887115607222774219080527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52591410404815182812720351 78887115607222774219080527)
  ·
    refine ⟨118330673410834161328620791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78887115607222774219080527 118330673410834161328620791)
    ·
      refine ⟨177496010116251241992931187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118330673410834161328620791 177496010116251241992931187)
      ·
        refine ⟨266244015174376862989396781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177496010116251241992931187 266244015174376862989396781)
        ·
          refine ⟨99841505690391323621023793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266244015174376862989396781 99841505690391323621023793)
          ·
            refine ⟨74881129267793492715767845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99841505690391323621023793 74881129267793492715767845)
            ·
              refine ⟨14040211737711279884206471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74881129267793492715767845 14040211737711279884206471)
              ·
                refine ⟨21060317606566919826309707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14040211737711279884206471 21060317606566919826309707)
                ·
                  refine ⟨31590476409850379739464561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21060317606566919826309707 31590476409850379739464561)
                  ·
                    refine ⟨23692857307387784804598421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31590476409850379739464561 23692857307387784804598421)
                    ·
                      refine ⟨1110602686283802412715551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23692857307387784804598421 1110602686283802412715551)
                      ·
                        rfl

theorem cell23_2162891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_2162891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162891 prefixEnd_2162891 := by exact prefixLift 2162891
  have htrace : WordTrace (prefixWord ++ tailWord_2162891) baseStart_2162891 baseEnd_2162891 := by
    simpa [prefixWord, tailWord_2162891, baseEnd_2162891] using wordTrace_append hprefix tailTrace_2162891
  have hstable : (prefixWord ++ tailWord_2162891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162891).length < 2 ^ (prefixWord ++ tailWord_2162891).sum := by decide
  have hdescent : baseEnd_2162891 < baseStart_2162891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162911 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2162911 : Nat := 118140960795 + 2162911 * 2 ^ 59
def prefixEnd_2162911 : Nat := 4983230072969 + 3 ^ 40 * 2162911 * 2
def baseEnd_2162911 : Nat := 1110612955896892334465459

theorem tailTrace_2162911 : CollatzResearch.WordTrace tailWord_2162911 prefixEnd_2162911 1110612955896892334465459 := by
  unfold tailWord_2162911
  simp only [CollatzResearch.WordTrace]
  refine ⟨78887845067150317634808587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52591896711433545089872391 78887845067150317634808587)
  ·
    refine ⟨118331767600725476452212881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78887845067150317634808587 118331767600725476452212881)
    ·
      refine ⟨88748825700544107339159661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118331767600725476452212881 88748825700544107339159661)
      ·
        refine ⟨33280809637704040252184873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88748825700544107339159661 33280809637704040252184873)
        ·
          refine ⟨24960607228278030189138655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33280809637704040252184873 24960607228278030189138655)
          ·
            refine ⟨37440910842417045283707983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24960607228278030189138655 37440910842417045283707983)
            ·
              refine ⟨56161366263625567925561975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37440910842417045283707983 56161366263625567925561975)
              ·
                refine ⟨84242049395438351888342963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56161366263625567925561975 84242049395438351888342963)
                ·
                  refine ⟨126363074093157527832514445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84242049395438351888342963 126363074093157527832514445)
                  ·
                    refine ⟨47386152784934072937192917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126363074093157527832514445 47386152784934072937192917)
                    ·
                      refine ⟨1110612955896892334465459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47386152784934072937192917 1110612955896892334465459)
                      ·
                        rfl

theorem cell23_2162911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2162911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162911 prefixEnd_2162911 := by exact prefixLift 2162911
  have htrace : WordTrace (prefixWord ++ tailWord_2162911) baseStart_2162911 baseEnd_2162911 := by
    simpa [prefixWord, tailWord_2162911, baseEnd_2162911] using wordTrace_append hprefix tailTrace_2162911
  have hstable : (prefixWord ++ tailWord_2162911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162911).length < 2 ^ (prefixWord ++ tailWord_2162911).sum := by decide
  have hdescent : baseEnd_2162911 < baseStart_2162911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162942 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_2162942 : Nat := 118140960795 + 2162942 * 2 ^ 59
def prefixEnd_2162942 : Nat := 4983230072969 + 3 ^ 40 * 2162942 * 2
def baseEnd_2162942 : Nat := 1110628873797181713177817

theorem tailTrace_2162942 : CollatzResearch.WordTrace tailWord_2162942 prefixEnd_2162942 1110628873797181713177817 := by
  unfold tailWord_2162942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861121966254751241148385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52592650486692006619458053 9861121966254751241148385)
  ·
    refine ⟨7395841474691063430861289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9861121966254751241148385 7395841474691063430861289)
    ·
      refine ⟨5546881106018297573145967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7395841474691063430861289 5546881106018297573145967)
      ·
        refine ⟨8320321659027446359718951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5546881106018297573145967 8320321659027446359718951)
        ·
          refine ⟨12480482488541169539578427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8320321659027446359718951 12480482488541169539578427)
          ·
            refine ⟨18720723732811754309367641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12480482488541169539578427 18720723732811754309367641)
            ·
              refine ⟨14040542799608815732025731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18720723732811754309367641 14040542799608815732025731)
              ·
                refine ⟨21060814199413223598038597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14040542799608815732025731 21060814199413223598038597)
                ·
                  refine ⟨3948902662389979424632237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21060814199413223598038597 3948902662389979424632237)
                  ·
                    refine ⟨1480838498396242284237089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3948902662389979424632237 1480838498396242284237089)
                    ·
                      refine ⟨1110628873797181713177817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480838498396242284237089 1110628873797181713177817)
                      ·
                        rfl

theorem cell23_2162942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_2162942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162942 prefixEnd_2162942 := by exact prefixLift 2162942
  have htrace : WordTrace (prefixWord ++ tailWord_2162942) baseStart_2162942 baseEnd_2162942 := by
    simpa [prefixWord, tailWord_2162942, baseEnd_2162942] using wordTrace_append hprefix tailTrace_2162942
  have hstable : (prefixWord ++ tailWord_2162942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162942).length < 2 ^ (prefixWord ++ tailWord_2162942).sum := by decide
  have hdescent : baseEnd_2162942 < baseStart_2162942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162965 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_2162965 : Nat := 118140960795 + 2162965 * 2 ^ 59
def prefixEnd_2162965 : Nat := 4983230072969 + 3 ^ 40 * 2162965 * 2
def baseEnd_2162965 : Nat := 370213561284078374396737

theorem tailTrace_2162965 : CollatzResearch.WordTrace tailWord_2162965 prefixEnd_2162965 370213561284078374396737 := by
  unfold tailWord_2162965
  simp only [CollatzResearch.WordTrace]
  refine ⟨78889814608954684857274349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52593209739303123238182899 78889814608954684857274349)
  ·
    refine ⟨29583680478358006821477881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78889814608954684857274349 29583680478358006821477881)
    ·
      refine ⟨22187760358768505116108411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29583680478358006821477881 22187760358768505116108411)
      ·
        refine ⟨33281640538152757674162617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22187760358768505116108411 33281640538152757674162617)
        ·
          refine ⟨24961230403614568255621963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33281640538152757674162617 24961230403614568255621963)
          ·
            refine ⟨37441845605421852383432945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24961230403614568255621963 37441845605421852383432945)
            ·
              refine ⟨28081384204066389287574709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37441845605421852383432945 28081384204066389287574709)
              ·
                refine ⟨2632629769131223995710129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28081384204066389287574709 2632629769131223995710129)
                ·
                  refine ⟨1974472326848417996782597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2632629769131223995710129 1974472326848417996782597)
                  ·
                    refine ⟨370213561284078374396737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974472326848417996782597 370213561284078374396737)
                    ·
                      rfl

theorem cell23_2162965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_2162965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162965 prefixEnd_2162965 := by exact prefixLift 2162965
  have htrace : WordTrace (prefixWord ++ tailWord_2162965) baseStart_2162965 baseEnd_2162965 := by
    simpa [prefixWord, tailWord_2162965, baseEnd_2162965] using wordTrace_append hprefix tailTrace_2162965
  have hstable : (prefixWord ++ tailWord_2162965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162965).length < 2 ^ (prefixWord ++ tailWord_2162965).sum := by decide
  have hdescent : baseEnd_2162965 < baseStart_2162965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162968 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2162968 : Nat := 118140960795 + 2162968 * 2 ^ 59
def prefixEnd_2162968 : Nat := 4983230072969 + 3 ^ 40 * 2162968 * 2
def baseEnd_2162968 : Nat := 1110642224294198611452697

theorem tailTrace_2162968 : CollatzResearch.WordTrace tailWord_2162968 prefixEnd_2162968 1110642224294198611452697 := by
  unfold tailWord_2162968
  simp only [CollatzResearch.WordTrace]
  refine ⟨39444962013971908184816779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52593282685295877579755705 39444962013971908184816779)
  ·
    refine ⟨59167443020957862277225169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39444962013971908184816779 59167443020957862277225169)
    ·
      refine ⟨44375582265718396707918877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59167443020957862277225169 44375582265718396707918877)
      ·
        refine ⟨16640843349644398765469579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44375582265718396707918877 16640843349644398765469579)
        ·
          refine ⟨24961265024466598148204369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16640843349644398765469579 24961265024466598148204369)
          ·
            refine ⟨18720948768349948611153277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24961265024466598148204369 18720948768349948611153277)
            ·
              refine ⟨7020355788131230729182479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18720948768349948611153277 7020355788131230729182479)
              ·
                refine ⟨10530533682196846093773719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7020355788131230729182479 10530533682196846093773719)
                ·
                  refine ⟨15795800523295269140660579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10530533682196846093773719 15795800523295269140660579)
                  ·
                    refine ⟨23693700784942903710990869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15795800523295269140660579 23693700784942903710990869)
                    ·
                      refine ⟨1110642224294198611452697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23693700784942903710990869 1110642224294198611452697)
                      ·
                        rfl

theorem cell23_2162968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2162968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2162968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2162968 prefixEnd_2162968 := by exact prefixLift 2162968
  have htrace : WordTrace (prefixWord ++ tailWord_2162968) baseStart_2162968 baseEnd_2162968 := by
    simpa [prefixWord, tailWord_2162968, baseEnd_2162968] using wordTrace_append hprefix tailTrace_2162968
  have hstable : (prefixWord ++ tailWord_2162968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162968).length < 2 ^ (prefixWord ++ tailWord_2162968).sum := by decide
  have hdescent : baseEnd_2162968 < baseStart_2162968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163006 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_2163006 : Nat := 118140960795 + 2163006 * 2 ^ 59
def prefixEnd_2163006 : Nat := 4983230072969 + 3 ^ 40 * 2163006 * 2
def baseEnd_2163006 : Nat := 1110661736559069462777523

theorem tailTrace_2163006 : CollatzResearch.WordTrace tailWord_2163006 prefixEnd_2163006 1110661736559069462777523 := by
  unfold tailWord_2163006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861413750225768607439609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52594206667870765906344581 9861413750225768607439609)
  ·
    refine ⟨7396060312669326455579707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9861413750225768607439609 7396060312669326455579707)
    ·
      refine ⟨11094090469003989683369561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7396060312669326455579707 11094090469003989683369561)
      ·
        refine ⟨8320567851752992262527171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11094090469003989683369561 8320567851752992262527171)
        ·
          refine ⟨12480851777629488393790757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8320567851752992262527171 12480851777629488393790757)
          ·
            refine ⟨2340159708305529073835767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12480851777629488393790757 2340159708305529073835767)
            ·
              refine ⟨3510239562458293610753651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340159708305529073835767 3510239562458293610753651)
              ·
                refine ⟨5265359343687440416130477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510239562458293610753651 5265359343687440416130477)
                ·
                  refine ⟨1974509753882790156048929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5265359343687440416130477 1974509753882790156048929)
                  ·
                    refine ⟨1480882315412092617036697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1974509753882790156048929 1480882315412092617036697)
                    ·
                      refine ⟨1110661736559069462777523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480882315412092617036697 1110661736559069462777523)
                      ·
                        rfl

theorem cell23_2163006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_2163006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163006 prefixEnd_2163006 := by exact prefixLift 2163006
  have htrace : WordTrace (prefixWord ++ tailWord_2163006) baseStart_2163006 baseEnd_2163006 := by
    simpa [prefixWord, tailWord_2163006, baseEnd_2163006] using wordTrace_append hprefix tailTrace_2163006
  have hstable : (prefixWord ++ tailWord_2163006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163006).length < 2 ^ (prefixWord ++ tailWord_2163006).sum := by decide
  have hdescent : baseEnd_2163006 < baseStart_2163006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163012 : List Nat := [2, 3, 4, 1, 2, 1, 2, 8]
def baseStart_2163012 : Nat := 118140960795 + 2163012 * 2 ^ 59
def prefixEnd_2163012 : Nat := 4983230072969 + 3 ^ 40 * 2163012 * 2
def baseEnd_2163012 : Nat := 41135733979370238492685

theorem tailTrace_2163012 : CollatzResearch.WordTrace tailWord_2163012 prefixEnd_2163012 41135733979370238492685 := by
  unfold tailWord_2163012
  simp only [CollatzResearch.WordTrace]
  refine ⟨39445764419892205942117645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52594352559856274589490193 39445764419892205942117645)
  ·
    refine ⟨14792161657459577228294117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39445764419892205942117645 14792161657459577228294117)
    ·
      refine ⟨2773530310773670730305147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14792161657459577228294117 2773530310773670730305147)
      ·
        refine ⟨4160295466160506095457721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773530310773670730305147 4160295466160506095457721)
        ·
          refine ⟨3120221599620379571593291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4160295466160506095457721 3120221599620379571593291)
          ·
            refine ⟨4680332399430569357389937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120221599620379571593291 4680332399430569357389937)
            ·
              refine ⟨3510249299572927018042453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680332399430569357389937 3510249299572927018042453)
              ·
                refine ⟨41135733979370238492685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3510249299572927018042453 41135733979370238492685)
                ·
                  rfl

theorem cell23_2163012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 8].length) (baseStart_2163012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163012 prefixEnd_2163012 := by exact prefixLift 2163012
  have htrace : WordTrace (prefixWord ++ tailWord_2163012) baseStart_2163012 baseEnd_2163012 := by
    simpa [prefixWord, tailWord_2163012, baseEnd_2163012] using wordTrace_append hprefix tailTrace_2163012
  have hstable : (prefixWord ++ tailWord_2163012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163012).length < 2 ^ (prefixWord ++ tailWord_2163012).sum := by decide
  have hdescent : baseEnd_2163012 < baseStart_2163012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163032 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 1, 3, 2]
def baseStart_2163032 : Nat := 118140960795 + 2163032 * 2 ^ 59
def prefixEnd_2163032 : Nat := 4983230072969 + 3 ^ 40 * 2163032 * 2
def baseEnd_2163032 : Nat := 1110675087056086361052403

theorem tailTrace_2163032 : CollatzResearch.WordTrace tailWord_2163032 prefixEnd_2163032 1110675087056086361052403 := by
  unfold tailWord_2163032
  simp only [CollatzResearch.WordTrace]
  refine ⟨39446129149855977649981675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52594838866474636866642233 39446129149855977649981675)
  ·
    refine ⟨59169193724783966474972513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39446129149855977649981675 59169193724783966474972513)
    ·
      refine ⟨44376895293587974856229385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59169193724783966474972513 44376895293587974856229385)
      ·
        refine ⟨33282671470190981142172039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44376895293587974856229385 33282671470190981142172039)
        ·
          refine ⟨49924007205286471713258059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33282671470190981142172039 49924007205286471713258059)
          ·
            refine ⟨74886010807929707569887089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49924007205286471713258059 74886010807929707569887089)
            ·
              refine ⟨56164508105947280677415317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74886010807929707569887089 56164508105947280677415317)
              ·
                refine ⟨2632711317466278781753843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56164508105947280677415317 2632711317466278781753843)
                ·
                  refine ⟨3949066976199418172630765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632711317466278781753843 3949066976199418172630765)
                  ·
                    refine ⟨1480900116074781814736537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3949066976199418172630765 1480900116074781814736537)
                    ·
                      refine ⟨1110675087056086361052403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480900116074781814736537 1110675087056086361052403)
                      ·
                        rfl

theorem cell23_2163032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_2163032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163032 prefixEnd_2163032 := by exact prefixLift 2163032
  have htrace : WordTrace (prefixWord ++ tailWord_2163032) baseStart_2163032 baseEnd_2163032 := by
    simpa [prefixWord, tailWord_2163032, baseEnd_2163032] using wordTrace_append hprefix tailTrace_2163032
  have hstable : (prefixWord ++ tailWord_2163032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163032).length < 2 ^ (prefixWord ++ tailWord_2163032).sum := by decide
  have hdescent : baseEnd_2163032 < baseStart_2163032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163049 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 1, 3, 2]
def baseStart_2163049 : Nat := 118140960795 + 2163049 * 2 ^ 59
def prefixEnd_2163049 : Nat := 4983230072969 + 3 ^ 40 * 2163049 * 2
def baseEnd_2163049 : Nat := 1110683816227212794539825

theorem tailTrace_2163049 : CollatzResearch.WordTrace tailWord_2163049 prefixEnd_2163049 1110683816227212794539825 := by
  unfold tailWord_2163049
  simp only [CollatzResearch.WordTrace]
  refine ⟨78892878340650367203332201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52595252227100244802221467 78892878340650367203332201)
  ·
    refine ⟨59169658755487775402499151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78892878340650367203332201 59169658755487775402499151)
    ·
      refine ⟨88754488133231663103748727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59169658755487775402499151 88754488133231663103748727)
      ·
        refine ⟨133131732199847494655623091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88754488133231663103748727 133131732199847494655623091)
        ·
          refine ⟨199697598299771241983434637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133131732199847494655623091 199697598299771241983434637)
          ·
            refine ⟨74886599362414215743787989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199697598299771241983434637 74886599362414215743787989)
            ·
              refine ⟨1755154672556583181495031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74886599362414215743787989 1755154672556583181495031)
              ·
                refine ⟨2632732008834874772242547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755154672556583181495031 2632732008834874772242547)
                ·
                  refine ⟨3949098013252312158363821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632732008834874772242547 3949098013252312158363821)
                  ·
                    refine ⟨1480911754969617059386433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3949098013252312158363821 1480911754969617059386433)
                    ·
                      refine ⟨1110683816227212794539825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480911754969617059386433 1110683816227212794539825)
                      ·
                        rfl

theorem cell23_2163049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 3, 2].length) (baseStart_2163049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163049 prefixEnd_2163049 := by exact prefixLift 2163049
  have htrace : WordTrace (prefixWord ++ tailWord_2163049) baseStart_2163049 baseEnd_2163049 := by
    simpa [prefixWord, tailWord_2163049, baseEnd_2163049] using wordTrace_append hprefix tailTrace_2163049
  have hstable : (prefixWord ++ tailWord_2163049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163049).length < 2 ^ (prefixWord ++ tailWord_2163049).sum := by decide
  have hdescent : baseEnd_2163049 < baseStart_2163049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163079 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_2163079 : Nat := 118140960795 + 2163079 * 2 ^ 59
def prefixEnd_2163079 : Nat := 4983230072969 + 3 ^ 40 * 2163079 * 2
def baseEnd_2163079 : Nat := 1110699220646847677164687

theorem tailTrace_2163079 : CollatzResearch.WordTrace tailWord_2163079 prefixEnd_2163079 1110699220646847677164687 := by
  unfold tailWord_2163079
  simp only [CollatzResearch.WordTrace]
  refine ⟨78893972530541682326924291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52595981687027788217949527 78893972530541682326924291)
  ·
    refine ⟨118340958795812523490386437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78893972530541682326924291 118340958795812523490386437)
    ·
      refine ⟨22188929774214848154447457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118340958795812523490386437 22188929774214848154447457)
      ·
        refine ⟨16641697330661136115835593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22188929774214848154447457 16641697330661136115835593)
        ·
          refine ⟨12481272997995852086876695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16641697330661136115835593 12481272997995852086876695)
          ·
            refine ⟨18721909496993778130315043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12481272997995852086876695 18721909496993778130315043)
            ·
              refine ⟨28082864245490667195472565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18721909496993778130315043 28082864245490667195472565)
              ·
                refine ⟨2632768523014750049575553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28082864245490667195472565 2632768523014750049575553)
                ·
                  refine ⟨1974576392261062537181665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2632768523014750049575553 1974576392261062537181665)
                  ·
                    refine ⟨1480932294195796902886249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1974576392261062537181665 1480932294195796902886249)
                    ·
                      refine ⟨1110699220646847677164687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1480932294195796902886249 1110699220646847677164687)
                      ·
                        rfl

theorem cell23_2163079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_2163079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163079 prefixEnd_2163079 := by exact prefixLift 2163079
  have htrace : WordTrace (prefixWord ++ tailWord_2163079) baseStart_2163079 baseEnd_2163079 := by
    simpa [prefixWord, tailWord_2163079, baseEnd_2163079] using wordTrace_append hprefix tailTrace_2163079
  have hstable : (prefixWord ++ tailWord_2163079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163079).length < 2 ^ (prefixWord ++ tailWord_2163079).sum := by decide
  have hdescent : baseEnd_2163079 < baseStart_2163079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163175 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 8]
def baseStart_2163175 : Nat := 118140960795 + 2163175 * 2 ^ 59
def prefixEnd_2163175 : Nat := 4983230072969 + 3 ^ 40 * 2163175 * 2
def baseEnd_2163175 : Nat := 123416501643297700173805

theorem tailTrace_2163175 : CollatzResearch.WordTrace tailWord_2163175 prefixEnd_2163175 123416501643297700173805 := by
  unfold tailWord_2163175
  simp only [CollatzResearch.WordTrace]
  refine ⟨78897473938193890722418979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52598315958795927148279319 78897473938193890722418979)
  ·
    refine ⟨118346210907290836083628469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78897473938193890722418979 118346210907290836083628469)
    ·
      refine ⟨11094957272558515882840169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118346210907290836083628469 11094957272558515882840169)
      ·
        refine ⟨8321217954418886912130127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11094957272558515882840169 8321217954418886912130127)
        ·
          refine ⟨12481826931628330368195191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8321217954418886912130127 12481826931628330368195191)
          ·
            refine ⟨18722740397442495552292787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12481826931628330368195191 18722740397442495552292787)
            ·
              refine ⟨28084110596163743328439181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18722740397442495552292787 28084110596163743328439181)
              ·
                refine ⟨10531541473561403748164693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28084110596163743328439181 10531541473561403748164693)
                ·
                  refine ⟨123416501643297700173805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10531541473561403748164693 123416501643297700173805)
                  ·
                    rfl

theorem cell23_2163175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 8].length) (baseStart_2163175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163175 prefixEnd_2163175 := by exact prefixLift 2163175
  have htrace : WordTrace (prefixWord ++ tailWord_2163175) baseStart_2163175 baseEnd_2163175 := by
    simpa [prefixWord, tailWord_2163175, baseEnd_2163175] using wordTrace_append hprefix tailTrace_2163175
  have hstable : (prefixWord ++ tailWord_2163175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163175).length < 2 ^ (prefixWord ++ tailWord_2163175).sum := by decide
  have hdescent : baseEnd_2163175 < baseStart_2163175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163270 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2163270 : Nat := 118140960795 + 2163270 * 2 ^ 59
def prefixEnd_2163270 : Nat := 4983230072969 + 3 ^ 40 * 2163270 * 2
def baseEnd_2163270 : Nat := 1110797295451856429876309

theorem tailTrace_2163270 : CollatzResearch.WordTrace tailWord_2163270 prefixEnd_2163270 1110797295451856429876309 := by
  unfold tailWord_2163270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465654339776553810847727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52600625915233147964751509 2465654339776553810847727)
  ·
    refine ⟨3698481509664830716271591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465654339776553810847727 3698481509664830716271591)
    ·
      refine ⟨5547722264497246074407387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698481509664830716271591 5547722264497246074407387)
      ·
        refine ⟨8321583396745869111611081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5547722264497246074407387 8321583396745869111611081)
        ·
          refine ⟨6241187547559401833708311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8321583396745869111611081 6241187547559401833708311)
          ·
            refine ⟨9361781321339102750562467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6241187547559401833708311 9361781321339102750562467)
            ·
              refine ⟨14042671982008654125843701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9361781321339102750562467 14042671982008654125843701)
              ·
                refine ⟨1316500498313311324297847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14042671982008654125843701 1316500498313311324297847)
                ·
                  refine ⟨1974750747469966986446771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316500498313311324297847 1974750747469966986446771)
                  ·
                    refine ⟨2962126121204950479670157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1974750747469966986446771 2962126121204950479670157)
                    ·
                      refine ⟨1110797295451856429876309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962126121204950479670157 1110797295451856429876309)
                      ·
                        rfl

theorem cell23_2163270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2163270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163270 prefixEnd_2163270 := by exact prefixLift 2163270
  have htrace : WordTrace (prefixWord ++ tailWord_2163270) baseStart_2163270 baseEnd_2163270 := by
    simpa [prefixWord, tailWord_2163270, baseEnd_2163270] using wordTrace_append hprefix tailTrace_2163270
  have hstable : (prefixWord ++ tailWord_2163270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163270).length < 2 ^ (prefixWord ++ tailWord_2163270).sum := by decide
  have hdescent : baseEnd_2163270 < baseStart_2163270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163295 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 9]
def baseStart_2163295 : Nat := 118140960795 + 2163295 * 2 ^ 59
def prefixEnd_2163295 : Nat := 4983230072969 + 3 ^ 40 * 2163295 * 2
def baseEnd_2163295 : Nat := 370270044156072944021231

theorem tailTrace_2163295 : CollatzResearch.WordTrace tailWord_2163295 prefixEnd_2163295 370270044156072944021231 := by
  unfold tailWord_2163295
  simp only [CollatzResearch.WordTrace]
  refine ⟨78901850697759151216787339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52601233798506100811191559 78901850697759151216787339)
  ·
    refine ⟨118352776046638726825181009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78901850697759151216787339 118352776046638726825181009)
    ·
      refine ⟨88764582034979045118885757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118352776046638726825181009 88764582034979045118885757)
      ·
        refine ⟨33286718263117141919582159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88764582034979045118885757 33286718263117141919582159)
        ·
          refine ⟨49930077394675712879373239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33286718263117141919582159 49930077394675712879373239)
          ·
            refine ⟨74895116092013569319059859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49930077394675712879373239 74895116092013569319059859)
            ·
              refine ⟨112342674138020353978589789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74895116092013569319059859 112342674138020353978589789)
              ·
                refine ⟨42128502801757632741971171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112342674138020353978589789 42128502801757632741971171)
                ·
                  refine ⟨63192754202636449112956757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42128502801757632741971171 63192754202636449112956757)
                  ·
                    refine ⟨370270044156072944021231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63192754202636449112956757 370270044156072944021231)
                    ·
                      rfl

theorem cell23_2163295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_2163295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163295 prefixEnd_2163295 := by exact prefixLift 2163295
  have htrace : WordTrace (prefixWord ++ tailWord_2163295) baseStart_2163295 baseEnd_2163295 := by
    simpa [prefixWord, tailWord_2163295, baseEnd_2163295] using wordTrace_append hprefix tailTrace_2163295
  have hstable : (prefixWord ++ tailWord_2163295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163295).length < 2 ^ (prefixWord ++ tailWord_2163295).sum := by decide
  have hdescent : baseEnd_2163295 < baseStart_2163295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163315 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_2163315 : Nat := 118140960795 + 2163315 * 2 ^ 59
def prefixEnd_2163315 : Nat := 4983230072969 + 3 ^ 40 * 2163315 * 2
def baseEnd_2163315 : Nat := 1110820402081308753813601

theorem tailTrace_2163315 : CollatzResearch.WordTrace tailWord_2163315 prefixEnd_2163315 1110820402081308753813601 := by
  unfold tailWord_2163315
  simp only [CollatzResearch.WordTrace]
  refine ⟨78902580157686694632515399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52601720105124463088343599 78902580157686694632515399)
  ·
    refine ⟨118353870236530041948773099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78902580157686694632515399 118353870236530041948773099)
    ·
      refine ⟨177530805354795062923159649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118353870236530041948773099 177530805354795062923159649)
      ·
        refine ⟨133148104016096297192369737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177530805354795062923159649 133148104016096297192369737)
        ·
          refine ⟨99861078012072222894277303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133148104016096297192369737 99861078012072222894277303)
          ·
            refine ⟨149791617018108334341415955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99861078012072222894277303 149791617018108334341415955)
            ·
              refine ⟨224687425527162501512123933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149791617018108334341415955 224687425527162501512123933)
              ·
                refine ⟨84257784572685938067046475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224687425527162501512123933 84257784572685938067046475)
                ·
                  refine ⟨126386676859028907100569713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84257784572685938067046475 126386676859028907100569713)
                  ·
                    refine ⟨94790007644271680325427285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126386676859028907100569713 94790007644271680325427285)
                    ·
                      refine ⟨1110820402081308753813601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94790007644271680325427285 1110820402081308753813601)
                      ·
                        rfl

theorem cell23_2163315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_2163315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163315 prefixEnd_2163315 := by exact prefixLift 2163315
  have htrace : WordTrace (prefixWord ++ tailWord_2163315) baseStart_2163315 baseEnd_2163315 := by
    simpa [prefixWord, tailWord_2163315, baseEnd_2163315] using wordTrace_append hprefix tailTrace_2163315
  have hstable : (prefixWord ++ tailWord_2163315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163315).length < 2 ^ (prefixWord ++ tailWord_2163315).sum := by decide
  have hdescent : baseEnd_2163315 < baseStart_2163315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163319 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 3, 3, 2]
def baseStart_2163319 : Nat := 118140960795 + 2163319 * 2 ^ 59
def prefixEnd_2163319 : Nat := 4983230072969 + 3 ^ 40 * 2163319 * 2
def baseEnd_2163319 : Nat := 1110822456003926738163583

theorem tailTrace_2163319 : CollatzResearch.WordTrace tailWord_2163319 prefixEnd_2163319 1110822456003926738163583 := by
  unfold tailWord_2163319
  simp only [CollatzResearch.WordTrace]
  refine ⟨78902726049672203315661011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52601817366448135543774007 78902726049672203315661011)
  ·
    refine ⟨118354089074508304973491517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78902726049672203315661011 118354089074508304973491517)
    ·
      refine ⟨44382783402940614365059319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118354089074508304973491517 44382783402940614365059319)
      ·
        refine ⟨66574175104410921547588979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44382783402940614365059319 66574175104410921547588979)
        ·
          refine ⟨99861262656616382321383469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66574175104410921547588979 99861262656616382321383469)
          ·
            refine ⟨37447973496231143370518801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99861262656616382321383469 37447973496231143370518801)
            ·
              refine ⟨28085980122173357527889101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37447973496231143370518801 28085980122173357527889101)
              ·
                refine ⟨10532242545815009072958413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28085980122173357527889101 10532242545815009072958413)
                ·
                  refine ⟨3949590954680628402359405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10532242545815009072958413 3949590954680628402359405)
                  ·
                    refine ⟨1481096608005235650884777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3949590954680628402359405 1481096608005235650884777)
                    ·
                      refine ⟨1110822456003926738163583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481096608005235650884777 1110822456003926738163583)
                      ·
                        rfl

theorem cell23_2163319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_2163319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163319 prefixEnd_2163319 := by exact prefixLift 2163319
  have htrace : WordTrace (prefixWord ++ tailWord_2163319) baseStart_2163319 baseEnd_2163319 := by
    simpa [prefixWord, tailWord_2163319, baseEnd_2163319] using wordTrace_append hprefix tailTrace_2163319
  have hstable : (prefixWord ++ tailWord_2163319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163319).length < 2 ^ (prefixWord ++ tailWord_2163319).sum := by decide
  have hdescent : baseEnd_2163319 < baseStart_2163319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163330 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2163330 : Nat := 118140960795 + 2163330 * 2 ^ 59
def prefixEnd_2163330 : Nat := 4983230072969 + 3 ^ 40 * 2163330 * 2
def baseEnd_2163330 : Nat := 1110828104291126195126033

theorem tailTrace_2163330 : CollatzResearch.WordTrace tailWord_2163330 prefixEnd_2163330 1110828104291126195126033 := by
  unfold tailWord_2163330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19725781813158088048577861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52602084835088234796207629 19725781813158088048577861)
  ·
    refine ⟨3698584089967141509108349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19725781813158088048577861 3698584089967141509108349)
    ·
      refine ⟨1386969033737678065915631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3698584089967141509108349 1386969033737678065915631)
      ·
        refine ⟨2080453550606517098873447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386969033737678065915631 2080453550606517098873447)
        ·
          refine ⟨3120680325909775648310171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080453550606517098873447 3120680325909775648310171)
          ·
            refine ⟨4681020488864663472465257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120680325909775648310171 4681020488864663472465257)
            ·
              refine ⟨3510765366648497604348943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4681020488864663472465257 3510765366648497604348943)
              ·
                refine ⟨5266148049972746406523415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510765366648497604348943 5266148049972746406523415)
                ·
                  refine ⟨7899222074959119609785123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5266148049972746406523415 7899222074959119609785123)
                  ·
                    refine ⟨11848833112438679414677685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7899222074959119609785123 11848833112438679414677685)
                    ·
                      refine ⟨1110828104291126195126033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11848833112438679414677685 1110828104291126195126033)
                      ·
                        rfl

theorem cell23_2163330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2163330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163330 prefixEnd_2163330 := by exact prefixLift 2163330
  have htrace : WordTrace (prefixWord ++ tailWord_2163330) baseStart_2163330 baseEnd_2163330 := by
    simpa [prefixWord, tailWord_2163330, baseEnd_2163330] using wordTrace_append hprefix tailTrace_2163330
  have hstable : (prefixWord ++ tailWord_2163330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163330).length < 2 ^ (prefixWord ++ tailWord_2163330).sum := by decide
  have hdescent : baseEnd_2163330 < baseStart_2163330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163352 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2163352 : Nat := 118140960795 + 2163352 * 2 ^ 59
def prefixEnd_2163352 : Nat := 4983230072969 + 3 ^ 40 * 2163352 * 2
def baseEnd_2163352 : Nat := 1110839400865525109050931

theorem tailTrace_2163352 : CollatzResearch.WordTrace tailWord_2163352 prefixEnd_2163352 1110839400865525109050931 := by
  unfold tailWord_2163352
  simp only [CollatzResearch.WordTrace]
  refine ⟨39451964829276324975806155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52602619772368433301074873 39451964829276324975806155)
  ·
    refine ⟨59177947243914487463709233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39451964829276324975806155 59177947243914487463709233)
    ·
      refine ⟨44383460432935865597781925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59177947243914487463709233 44383460432935865597781925)
      ·
        refine ⟨8321898831175474799584111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44383460432935865597781925 8321898831175474799584111)
        ·
          refine ⟨12482848246763212199376167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8321898831175474799584111 12482848246763212199376167)
          ·
            refine ⟨18724272370144818299064251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12482848246763212199376167 18724272370144818299064251)
            ·
              refine ⟨28086408555217227448596377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18724272370144818299064251 28086408555217227448596377)
              ·
                refine ⟨21064806416412920586447283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28086408555217227448596377 21064806416412920586447283)
                ·
                  refine ⟨31597209624619380879670925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21064806416412920586447283 31597209624619380879670925)
                  ·
                    refine ⟨11848953609232267829876597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31597209624619380879670925 11848953609232267829876597)
                    ·
                      refine ⟨1110839400865525109050931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11848953609232267829876597 1110839400865525109050931)
                      ·
                        rfl

theorem cell23_2163352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2163352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163352 prefixEnd_2163352 := by exact prefixLift 2163352
  have htrace : WordTrace (prefixWord ++ tailWord_2163352) baseStart_2163352 baseEnd_2163352 := by
    simpa [prefixWord, tailWord_2163352, baseEnd_2163352] using wordTrace_append hprefix tailTrace_2163352
  have hstable : (prefixWord ++ tailWord_2163352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163352).length < 2 ^ (prefixWord ++ tailWord_2163352).sum := by decide
  have hdescent : baseEnd_2163352 < baseStart_2163352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163360 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 2, 1, 3]
def baseStart_2163360 : Nat := 118140960795 + 2163360 * 2 ^ 59
def prefixEnd_2163360 : Nat := 4983230072969 + 3 ^ 40 * 2163360 * 2
def baseEnd_2163360 : Nat := 1110843508710761077750895

theorem tailTrace_2163360 : CollatzResearch.WordTrace tailWord_2163360 prefixEnd_2163360 1110843508710761077750895 := by
  unfold tailWord_2163360
  simp only [CollatzResearch.WordTrace]
  refine ⟨39452110721261833658951767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52602814295015778211935689 39452110721261833658951767)
  ·
    refine ⟨59178166081892750488427651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39452110721261833658951767 59178166081892750488427651)
    ·
      refine ⟨88767249122839125732641477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59178166081892750488427651 88767249122839125732641477)
      ·
        refine ⟨16643859210532336074870277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88767249122839125732641477 16643859210532336074870277)
        ·
          refine ⟨3120723601974813014038177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16643859210532336074870277 3120723601974813014038177)
          ·
            refine ⟨2340542701481109760528633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3120723601974813014038177 2340542701481109760528633)
            ·
              refine ⟨1755407026110832320396475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340542701481109760528633 1755407026110832320396475)
              ·
                refine ⟨2633110539166248480594713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755407026110832320396475 2633110539166248480594713)
                ·
                  refine ⟨1974832904374686360446035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633110539166248480594713 1974832904374686360446035)
                  ·
                    refine ⟨2962249356562029540669053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1974832904374686360446035 2962249356562029540669053)
                    ·
                      refine ⟨1110843508710761077750895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962249356562029540669053 1110843508710761077750895)
                      ·
                        rfl

theorem cell23_2163360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_2163360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163360 prefixEnd_2163360 := by exact prefixLift 2163360
  have htrace : WordTrace (prefixWord ++ tailWord_2163360) baseStart_2163360 baseEnd_2163360 := by
    simpa [prefixWord, tailWord_2163360, baseEnd_2163360] using wordTrace_append hprefix tailTrace_2163360
  have hstable : (prefixWord ++ tailWord_2163360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163360).length < 2 ^ (prefixWord ++ tailWord_2163360).sum := by decide
  have hdescent : baseEnd_2163360 < baseStart_2163360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163370 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2163370 : Nat := 118140960795 + 2163370 * 2 ^ 59
def prefixEnd_2163370 : Nat := 4983230072969 + 3 ^ 40 * 2163370 * 2
def baseEnd_2163370 : Nat := 1110848643517306038625849

theorem tailTrace_2163370 : CollatzResearch.WordTrace tailWord_2163370 prefixEnd_2163370 1110848643517306038625849 := by
  unfold tailWord_2163370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19726146543121859756441891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52603057448324959350511709 19726146543121859756441891)
  ·
    refine ⟨29589219814682789634662837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19726146543121859756441891 29589219814682789634662837)
    ·
      refine ⟨2773989357626511528249641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29589219814682789634662837 2773989357626511528249641)
      ·
        refine ⟨2080492018219883646187231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773989357626511528249641 2080492018219883646187231)
        ·
          refine ⟨3120738027329825469280847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080492018219883646187231 3120738027329825469280847)
          ·
            refine ⟨4681107040994738203921271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120738027329825469280847 4681107040994738203921271)
            ·
              refine ⟨7021660561492107305881907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681107040994738203921271 7021660561492107305881907)
              ·
                refine ⟨10532490842238160958822861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021660561492107305881907 10532490842238160958822861)
                ·
                  refine ⟨3949684065839310359558573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10532490842238160958822861 3949684065839310359558573)
                  ·
                    refine ⟨1481131524689741384834465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3949684065839310359558573 1481131524689741384834465)
                    ·
                      refine ⟨1110848643517306038625849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481131524689741384834465 1110848643517306038625849)
                      ·
                        rfl

theorem cell23_2163370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2163370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163370 prefixEnd_2163370 := by exact prefixLift 2163370
  have htrace : WordTrace (prefixWord ++ tailWord_2163370) baseStart_2163370 baseEnd_2163370 := by
    simpa [prefixWord, tailWord_2163370, baseEnd_2163370] using wordTrace_append hprefix tailTrace_2163370
  have hstable : (prefixWord ++ tailWord_2163370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163370).length < 2 ^ (prefixWord ++ tailWord_2163370).sum := by decide
  have hdescent : baseEnd_2163370 < baseStart_2163370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163406 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_2163406 : Nat := 118140960795 + 2163406 * 2 ^ 59
def prefixEnd_2163406 : Nat := 4983230072969 + 3 ^ 40 * 2163406 * 2
def baseEnd_2163406 : Nat := 123429680980096433086187

theorem tailTrace_2163406 : CollatzResearch.WordTrace tailWord_2163406 prefixEnd_2163406 123429680980096433086187 := by
  unfold tailWord_2163406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9863237400044627146759759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52603932800238011449385381 9863237400044627146759759)
  ·
    refine ⟨14794856100066940720139639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9863237400044627146759759 14794856100066940720139639)
    ·
      refine ⟨22192284150100411080209459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14794856100066940720139639 22192284150100411080209459)
      ·
        refine ⟨33288426225150616620314189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22192284150100411080209459 33288426225150616620314189)
        ·
          refine ⟨12483159834431481232617821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33288426225150616620314189 12483159834431481232617821)
          ·
            refine ⟨4681184937911805462231683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12483159834431481232617821 4681184937911805462231683)
            ·
              refine ⟨7021777406867708193347525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681184937911805462231683 7021777406867708193347525)
              ·
                refine ⟨1316583263787695286252661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7021777406867708193347525 1316583263787695286252661)
                ·
                  refine ⟨123429680980096433086187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1316583263787695286252661 123429680980096433086187)
                  ·
                    rfl

theorem cell23_2163406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_2163406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163406 prefixEnd_2163406 := by exact prefixLift 2163406
  have htrace : WordTrace (prefixWord ++ tailWord_2163406) baseStart_2163406 baseEnd_2163406 := by
    simpa [prefixWord, tailWord_2163406, baseEnd_2163406] using wordTrace_append hprefix tailTrace_2163406
  have hstable : (prefixWord ++ tailWord_2163406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163406).length < 2 ^ (prefixWord ++ tailWord_2163406).sum := by decide
  have hdescent : baseEnd_2163406 < baseStart_2163406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163409 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 7, 2]
def baseStart_2163409 : Nat := 118140960795 + 2163409 * 2 ^ 59
def prefixEnd_2163409 : Nat := 4983230072969 + 3 ^ 40 * 2163409 * 2
def baseEnd_2163409 : Nat := 1110868669262831386038169

theorem tailTrace_2163409 : CollatzResearch.WordTrace tailWord_2163409 prefixEnd_2163409 1110868669262831386038169 := by
  unfold tailWord_2163409
  simp only [CollatzResearch.WordTrace]
  refine ⟨78906008619346148686437281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52604005746230765790958187 78906008619346148686437281)
  ·
    refine ⟨59179506464509611514827961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78906008619346148686437281 59179506464509611514827961)
    ·
      refine ⟨44384629848382208636120971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59179506464509611514827961 44384629848382208636120971)
      ·
        refine ⟨66576944772573312954181457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44384629848382208636120971 66576944772573312954181457)
        ·
          refine ⟨49932708579429984715636093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66576944772573312954181457 49932708579429984715636093)
          ·
            refine ⟨18724765717286244268363535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49932708579429984715636093 18724765717286244268363535)
            ·
              refine ⟨28087148575929366402545303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18724765717286244268363535 28087148575929366402545303)
              ·
                refine ⟨42130722863894049603817955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28087148575929366402545303 42130722863894049603817955)
                ·
                  refine ⟨63196084295841074405726933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42130722863894049603817955 63196084295841074405726933)
                  ·
                    refine ⟨1481158225683775181384225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63196084295841074405726933 1481158225683775181384225)
                    ·
                      refine ⟨1110868669262831386038169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481158225683775181384225 1110868669262831386038169)
                      ·
                        rfl

theorem cell23_2163409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_2163409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163409 prefixEnd_2163409 := by exact prefixLift 2163409
  have htrace : WordTrace (prefixWord ++ tailWord_2163409) baseStart_2163409 baseEnd_2163409 := by
    simpa [prefixWord, tailWord_2163409, baseEnd_2163409] using wordTrace_append hprefix tailTrace_2163409
  have hstable : (prefixWord ++ tailWord_2163409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163409).length < 2 ^ (prefixWord ++ tailWord_2163409).sum := by decide
  have hdescent : baseEnd_2163409 < baseStart_2163409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163439 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_2163439 : Nat := 118140960795 + 2163439 * 2 ^ 59
def prefixEnd_2163439 : Nat := 4983230072969 + 3 ^ 40 * 2163439 * 2
def baseEnd_2163439 : Nat := 1110884073682466268663031

theorem tailTrace_2163439 : CollatzResearch.WordTrace tailWord_2163439 prefixEnd_2163439 1110884073682466268663031 := by
  unfold tailWord_2163439
  simp only [CollatzResearch.WordTrace]
  refine ⟨78907102809237463810029371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52604735206158309206686247 78907102809237463810029371)
  ·
    refine ⟨118360654213856195715044057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78907102809237463810029371 118360654213856195715044057)
    ·
      refine ⟨88770490660392146786283043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118360654213856195715044057 88770490660392146786283043)
      ·
        refine ⟨133155735990588220179424565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88770490660392146786283043 133155735990588220179424565)
        ·
          refine ⟨12483350249117645641821053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133155735990588220179424565 12483350249117645641821053)
          ·
            refine ⟨4681256343419117115682895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12483350249117645641821053 4681256343419117115682895)
            ·
              refine ⟨7021884515128675673524343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681256343419117115682895 7021884515128675673524343)
              ·
                refine ⟨10532826772693013510286515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021884515128675673524343 10532826772693013510286515)
                ·
                  refine ⟨15799240159039520265429773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10532826772693013510286515 15799240159039520265429773)
                  ·
                    refine ⟨5924715059639820099536165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15799240159039520265429773 5924715059639820099536165)
                    ·
                      refine ⟨1110884073682466268663031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5924715059639820099536165 1110884073682466268663031)
                      ·
                        rfl

theorem cell23_2163439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_2163439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163439 prefixEnd_2163439 := by exact prefixLift 2163439
  have htrace : WordTrace (prefixWord ++ tailWord_2163439) baseStart_2163439 baseEnd_2163439 := by
    simpa [prefixWord, tailWord_2163439, baseEnd_2163439] using wordTrace_append hprefix tailTrace_2163439
  have hstable : (prefixWord ++ tailWord_2163439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163439).length < 2 ^ (prefixWord ++ tailWord_2163439).sum := by decide
  have hdescent : baseEnd_2163439 < baseStart_2163439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163459 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 3]
def baseStart_2163459 : Nat := 118140960795 + 2163459 * 2 ^ 59
def prefixEnd_2163459 : Nat := 4983230072969 + 3 ^ 40 * 2163459 * 2
def baseEnd_2163459 : Nat := 1110894343295556190412939

theorem tailTrace_2163459 : CollatzResearch.WordTrace tailWord_2163459 prefixEnd_2163459 1110894343295556190412939 := by
  unfold tailWord_2163459
  simp only [CollatzResearch.WordTrace]
  refine ⟨78907832269165007225757431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52605221512776671483838287 78907832269165007225757431)
  ·
    refine ⟨118361748403747510838636147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78907832269165007225757431 118361748403747510838636147)
    ·
      refine ⟨177542622605621266257954221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118361748403747510838636147 177542622605621266257954221)
      ·
        refine ⟨66578483477107974846732833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177542622605621266257954221 66578483477107974846732833)
        ·
          refine ⟨49933862607830981135049625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66578483477107974846732833 49933862607830981135049625)
          ·
            refine ⟨37450396955873235851287219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49933862607830981135049625 37450396955873235851287219)
            ·
              refine ⟨56175595433809853776930829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37450396955873235851287219 56175595433809853776930829)
              ·
                refine ⟨21065848287678695166349061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56175595433809853776930829 21065848287678695166349061)
                ·
                  refine ⟨3949846553939755343690449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21065848287678695166349061 3949846553939755343690449)
                  ·
                    refine ⟨2962384915454816507767837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949846553939755343690449 2962384915454816507767837)
                    ·
                      refine ⟨1110894343295556190412939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962384915454816507767837 1110894343295556190412939)
                      ·
                        rfl

theorem cell23_2163459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_2163459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163459 prefixEnd_2163459 := by exact prefixLift 2163459
  have htrace : WordTrace (prefixWord ++ tailWord_2163459) baseStart_2163459 baseEnd_2163459 := by
    simpa [prefixWord, tailWord_2163459, baseEnd_2163459] using wordTrace_append hprefix tailTrace_2163459
  have hstable : (prefixWord ++ tailWord_2163459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163459).length < 2 ^ (prefixWord ++ tailWord_2163459).sum := by decide
  have hdescent : baseEnd_2163459 < baseStart_2163459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163466 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_2163466 : Nat := 118140960795 + 2163466 * 2 ^ 59
def prefixEnd_2163466 : Nat := 4983230072969 + 3 ^ 40 * 2163466 * 2
def baseEnd_2163466 : Nat := 370299312553379221008469

theorem tailTrace_2163466 : CollatzResearch.WordTrace tailWord_2163466 prefixEnd_2163466 370299312553379221008469 := by
  unfold tailWord_2163466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19727021895034911855315563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52605391720093098280841501 19727021895034911855315563)
  ·
    refine ⟨29590532842552367782973345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19727021895034911855315563 29590532842552367782973345)
    ·
      refine ⟨22192899631914275837230009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29590532842552367782973345 22192899631914275837230009)
      ·
        refine ⟨16644674723935706877922507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22192899631914275837230009 16644674723935706877922507)
        ·
          refine ⟨24967012085903560316883761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16644674723935706877922507 24967012085903560316883761)
          ·
            refine ⟨18725259064427670237662821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24967012085903560316883761 18725259064427670237662821)
            ·
              refine ⟨3510986074580188169561779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18725259064427670237662821 3510986074580188169561779)
              ·
                refine ⟨5266479111870282254342669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510986074580188169561779 5266479111870282254342669)
                ·
                  refine ⟨1974929666951355845378501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5266479111870282254342669 1974929666951355845378501)
                  ·
                    refine ⟨370299312553379221008469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974929666951355845378501 370299312553379221008469)
                    ·
                      rfl

theorem cell23_2163466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_2163466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163466 prefixEnd_2163466 := by exact prefixLift 2163466
  have htrace : WordTrace (prefixWord ++ tailWord_2163466) baseStart_2163466 baseEnd_2163466 := by
    simpa [prefixWord, tailWord_2163466, baseEnd_2163466] using wordTrace_append hprefix tailTrace_2163466
  have hstable : (prefixWord ++ tailWord_2163466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163466).length < 2 ^ (prefixWord ++ tailWord_2163466).sum := by decide
  have hdescent : baseEnd_2163466 < baseStart_2163466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163489 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2163489 : Nat := 118140960795 + 2163489 * 2 ^ 59
def prefixEnd_2163489 : Nat := 4983230072969 + 3 ^ 40 * 2163489 * 2
def baseEnd_2163489 : Nat := 1110909747715191073037801

theorem tailTrace_2163489 : CollatzResearch.WordTrace tailWord_2163489 prefixEnd_2163489 1110909747715191073037801 := by
  unfold tailWord_2163489
  simp only [CollatzResearch.WordTrace]
  refine ⟨78908926459056322349349521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52605950972704214899566347 78908926459056322349349521)
  ·
    refine ⟨59181694844292241762012141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78908926459056322349349521 59181694844292241762012141)
    ·
      refine ⟨22193135566609590660754553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59181694844292241762012141 22193135566609590660754553)
      ·
        refine ⟨16644851674957192995565915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22193135566609590660754553 16644851674957192995565915)
        ·
          refine ⟨24967277512435789493348873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16644851674957192995565915 24967277512435789493348873)
          ·
            refine ⟨18725458134326842120011655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24967277512435789493348873 18725458134326842120011655)
            ·
              refine ⟨28088187201490263180017483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18725458134326842120011655 28088187201490263180017483)
              ·
                refine ⟨42132280802235394770026225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28088187201490263180017483 42132280802235394770026225)
                ·
                  refine ⟨31599210601676546077519669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42132280802235394770026225 31599210601676546077519669)
                  ·
                    refine ⟨2962425993907176194767469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31599210601676546077519669 2962425993907176194767469)
                    ·
                      refine ⟨1110909747715191073037801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962425993907176194767469 1110909747715191073037801)
                      ·
                        rfl

theorem cell23_2163489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2163489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163489 prefixEnd_2163489 := by exact prefixLift 2163489
  have htrace : WordTrace (prefixWord ++ tailWord_2163489) baseStart_2163489 baseEnd_2163489 := by
    simpa [prefixWord, tailWord_2163489, baseEnd_2163489] using wordTrace_append hprefix tailTrace_2163489
  have hstable : (prefixWord ++ tailWord_2163489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163489).length < 2 ^ (prefixWord ++ tailWord_2163489).sum := by decide
  have hdescent : baseEnd_2163489 < baseStart_2163489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163510 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2163510 : Nat := 118140960795 + 2163510 * 2 ^ 59
def prefixEnd_2163510 : Nat := 4983230072969 + 3 ^ 40 * 2163510 * 2
def baseEnd_2163510 : Nat := 1110920530808935490875205

theorem tailTrace_2163510 : CollatzResearch.WordTrace tailWord_2163510 prefixEnd_2163510 1110920530808935490875205 := by
  unfold tailWord_2163510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931855774498765183491499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52606461594653495290575989 4931855774498765183491499)
  ·
    refine ⟨7397783661748147775237249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4931855774498765183491499 7397783661748147775237249)
    ·
      refine ⟨5548337746311110831427937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7397783661748147775237249 5548337746311110831427937)
      ·
        refine ⟨4161253309733333123570953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5548337746311110831427937 4161253309733333123570953)
        ·
          refine ⟨3120939982299999842678215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4161253309733333123570953 3120939982299999842678215)
          ·
            refine ⟨4681409973449999764017323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120939982299999842678215 4681409973449999764017323)
            ·
              refine ⟨7022114960174999646025985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681409973449999764017323 7022114960174999646025985)
              ·
                refine ⟨5266586220131249734519489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7022114960174999646025985 5266586220131249734519489)
                ·
                  refine ⟨3949939665098437300889617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5266586220131249734519489 3949939665098437300889617)
                  ·
                    refine ⟨2962454748823827975667213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949939665098437300889617 2962454748823827975667213)
                    ·
                      refine ⟨1110920530808935490875205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962454748823827975667213 1110920530808935490875205)
                      ·
                        rfl

theorem cell23_2163510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2163510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163510 prefixEnd_2163510 := by exact prefixLift 2163510
  have htrace : WordTrace (prefixWord ++ tailWord_2163510) baseStart_2163510 baseEnd_2163510 := by
    simpa [prefixWord, tailWord_2163510, baseEnd_2163510] using wordTrace_append hprefix tailTrace_2163510
  have hstable : (prefixWord ++ tailWord_2163510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163510).length < 2 ^ (prefixWord ++ tailWord_2163510).sum := by decide
  have hdescent : baseEnd_2163510 < baseStart_2163510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163517 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_2163517 : Nat := 118140960795 + 2163517 * 2 ^ 59
def prefixEnd_2163517 : Nat := 4983230072969 + 3 ^ 40 * 2163517 * 2
def baseEnd_2163517 : Nat := 370308041724505654495891

theorem tailTrace_2163517 : CollatzResearch.WordTrace tailWord_2163517 prefixEnd_2163517 370308041724505654495891 := by
  unfold tailWord_2163517
  simp only [CollatzResearch.WordTrace]
  refine ⟨78909947702954883131368805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52606631801969922087579203 78909947702954883131368805)
  ·
    refine ⟨14795615194304040587131651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78909947702954883131368805 14795615194304040587131651)
    ·
      refine ⟨22193422791456060880697477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14795615194304040587131651 22193422791456060880697477)
      ·
        refine ⟨4161266773398011415130777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22193422791456060880697477 4161266773398011415130777)
        ·
          refine ⟨3120950080048508561348083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4161266773398011415130777 3120950080048508561348083)
          ·
            refine ⟨4681425120072762842022125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120950080048508561348083 4681425120072762842022125)
            ·
              refine ⟨1755534420027286065758297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4681425120072762842022125 1755534420027286065758297)
              ·
                refine ⟨1316650815020464549318723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1755534420027286065758297 1316650815020464549318723)
                ·
                  refine ⟨1974976222530696823978085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316650815020464549318723 1974976222530696823978085)
                  ·
                    refine ⟨370308041724505654495891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1974976222530696823978085 370308041724505654495891)
                    ·
                      rfl

theorem cell23_2163517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_2163517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163517 prefixEnd_2163517 := by exact prefixLift 2163517
  have htrace : WordTrace (prefixWord ++ tailWord_2163517) baseStart_2163517 baseEnd_2163517 := by
    simpa [prefixWord, tailWord_2163517, baseEnd_2163517] using wordTrace_append hprefix tailTrace_2163517
  have hstable : (prefixWord ++ tailWord_2163517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163517).length < 2 ^ (prefixWord ++ tailWord_2163517).sum := by decide
  have hdescent : baseEnd_2163517 < baseStart_2163517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163543 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 1, 5]
def baseStart_2163543 : Nat := 118140960795 + 2163543 * 2 ^ 59
def prefixEnd_2163543 : Nat := 4983230072969 + 3 ^ 40 * 2163543 * 2
def baseEnd_2163543 : Nat := 370312491890177953920851

theorem tailTrace_2163543 : CollatzResearch.WordTrace tailWord_2163543 prefixEnd_2163543 370312491890177953920851 := by
  unfold tailWord_2163543
  simp only [CollatzResearch.WordTrace]
  refine ⟨78910896000860689571815283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52607264000573793047876855 78910896000860689571815283)
  ·
    refine ⟨118366344001291034357722925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78910896000860689571815283 118366344001291034357722925)
    ·
      refine ⟨44387379000484137884146097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118366344001291034357722925 44387379000484137884146097)
      ·
        refine ⟨33290534250363103413109573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44387379000484137884146097 33290534250363103413109573)
        ·
          refine ⟨6241975171943081889958045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33290534250363103413109573 6241975171943081889958045)
          ·
            refine ⟨2340740689478655708734267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6241975171943081889958045 2340740689478655708734267)
            ·
              refine ⟨3511111034217983563101401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340740689478655708734267 3511111034217983563101401)
              ·
                refine ⟨2633333275663487672326051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511111034217983563101401 2633333275663487672326051)
                ·
                  refine ⟨3949999913495231508489077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633333275663487672326051 3949999913495231508489077)
                  ·
                    refine ⟨370312491890177953920851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3949999913495231508489077 370312491890177953920851)
                    ·
                      rfl

theorem cell23_2163543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_2163543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163543 prefixEnd_2163543 := by exact prefixLift 2163543
  have htrace : WordTrace (prefixWord ++ tailWord_2163543) baseStart_2163543 baseEnd_2163543 := by
    simpa [prefixWord, tailWord_2163543, baseEnd_2163543] using wordTrace_append hprefix tailTrace_2163543
  have hstable : (prefixWord ++ tailWord_2163543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163543).length < 2 ^ (prefixWord ++ tailWord_2163543).sum := by decide
  have hdescent : baseEnd_2163543 < baseStart_2163543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163546 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_2163546 : Nat := 118140960795 + 2163546 * 2 ^ 59
def prefixEnd_2163546 : Nat := 4983230072969 + 3 ^ 40 * 2163546 * 2
def baseEnd_2163546 : Nat := 1110939016112497350025039

theorem tailTrace_2163546 : CollatzResearch.WordTrace tailWord_2163546 prefixEnd_2163546 1110939016112497350025039 := by
  unfold tailWord_2163546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19727751354962455271043623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52607336946566547389449661 19727751354962455271043623)
  ·
    refine ⟨29591627032443682906565435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19727751354962455271043623 29591627032443682906565435)
    ·
      refine ⟨44387440548665524359848153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29591627032443682906565435 44387440548665524359848153)
      ·
        refine ⟨33290580411499143269886115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44387440548665524359848153 33290580411499143269886115)
        ·
          refine ⟨49935870617248714904829173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33290580411499143269886115 49935870617248714904829173)
          ·
            refine ⟨4681487870367067022327735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49935870617248714904829173 4681487870367067022327735)
            ·
              refine ⟨7022231805550600533491603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681487870367067022327735 7022231805550600533491603)
              ·
                refine ⟨10533347708325900800237405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7022231805550600533491603 10533347708325900800237405)
                ·
                  refine ⟨3950005390622212800089027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10533347708325900800237405 3950005390622212800089027)
                  ·
                    refine ⟨5925008085933319200133541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950005390622212800089027 5925008085933319200133541)
                    ·
                      refine ⟨1110939016112497350025039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5925008085933319200133541 1110939016112497350025039)
                      ·
                        rfl

theorem cell23_2163546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_2163546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163546 prefixEnd_2163546 := by exact prefixLift 2163546
  have htrace : WordTrace (prefixWord ++ tailWord_2163546) baseStart_2163546 baseEnd_2163546 := by
    simpa [prefixWord, tailWord_2163546, baseEnd_2163546] using wordTrace_append hprefix tailTrace_2163546
  have hstable : (prefixWord ++ tailWord_2163546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163546).length < 2 ^ (prefixWord ++ tailWord_2163546).sum := by decide
  have hdescent : baseEnd_2163546 < baseStart_2163546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163556 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_2163556 : Nat := 118140960795 + 2163556 * 2 ^ 59
def prefixEnd_2163556 : Nat := 4983230072969 + 3 ^ 40 * 2163556 * 2
def baseEnd_2163556 : Nat := 370314716973014103633331

theorem tailTrace_2163556 : CollatzResearch.WordTrace tailWord_2163556 prefixEnd_2163556 370314716973014103633331 := by
  unfold tailWord_2163556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39455685074906796396019261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52607580099875728528025681 39455685074906796396019261)
  ·
    refine ⟨14795881903090048648507223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39455685074906796396019261 14795881903090048648507223)
    ·
      refine ⟨22193822854635072972760835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14795881903090048648507223 22193822854635072972760835)
      ·
        refine ⟨33290734281952609459141253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22193822854635072972760835 33290734281952609459141253)
        ·
          refine ⟨6242012677866114273588985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33290734281952609459141253 6242012677866114273588985)
          ·
            refine ⟨4681509508399585705191739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6242012677866114273588985 4681509508399585705191739)
            ·
              refine ⟨7022264262599378557787609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681509508399585705191739 7022264262599378557787609)
              ·
                refine ⟨5266698196949533918340707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7022264262599378557787609 5266698196949533918340707)
                ·
                  refine ⟨7900047295424300877511061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5266698196949533918340707 7900047295424300877511061)
                  ·
                    refine ⟨370314716973014103633331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7900047295424300877511061 370314716973014103633331)
                    ·
                      rfl

theorem cell23_2163556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_2163556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163556 prefixEnd_2163556 := by exact prefixLift 2163556
  have htrace : WordTrace (prefixWord ++ tailWord_2163556) baseStart_2163556 baseEnd_2163556 := by
    simpa [prefixWord, tailWord_2163556, baseEnd_2163556] using wordTrace_append hprefix tailTrace_2163556
  have hstable : (prefixWord ++ tailWord_2163556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163556).length < 2 ^ (prefixWord ++ tailWord_2163556).sum := by decide
  have hdescent : baseEnd_2163556 < baseStart_2163556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163573 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2163573 : Nat := 118140960795 + 2163573 * 2 ^ 59
def prefixEnd_2163573 : Nat := 4983230072969 + 3 ^ 40 * 2163573 * 2
def baseEnd_2163573 : Nat := 370317626696722914795805

theorem tailTrace_2163573 : CollatzResearch.WordTrace tailWord_2163573 prefixEnd_2163573 370317626696722914795805 := by
  unfold tailWord_2163573
  simp only [CollatzResearch.WordTrace]
  refine ⟨78911990190752004695407373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52607993460501336463604915 78911990190752004695407373)
  ·
    refine ⟨29591996321532001760777765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78911990190752004695407373 29591996321532001760777765)
    ·
      refine ⟨5548499310287250330145831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29591996321532001760777765 5548499310287250330145831)
      ·
        refine ⟨8322748965430875495218747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5548499310287250330145831 8322748965430875495218747)
        ·
          refine ⟨12484123448146313242828121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8322748965430875495218747 12484123448146313242828121)
          ·
            refine ⟨9363092586109734932121091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12484123448146313242828121 9363092586109734932121091)
            ·
              refine ⟨14044638879164602398181637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9363092586109734932121091 14044638879164602398181637)
              ·
                refine ⟨2633369789843362949659057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14044638879164602398181637 2633369789843362949659057)
                ·
                  refine ⟨1975027342382522212244293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633369789843362949659057 1975027342382522212244293)
                  ·
                    refine ⟨370317626696722914795805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975027342382522212244293 370317626696722914795805)
                    ·
                      rfl

theorem cell23_2163573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2163573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163573 prefixEnd_2163573 := by exact prefixLift 2163573
  have htrace : WordTrace (prefixWord ++ tailWord_2163573) baseStart_2163573 baseEnd_2163573 := by
    simpa [prefixWord, tailWord_2163573, baseEnd_2163573] using wordTrace_append hprefix tailTrace_2163573
  have hstable : (prefixWord ++ tailWord_2163573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163573).length < 2 ^ (prefixWord ++ tailWord_2163573).sum := by decide
  have hdescent : baseEnd_2163573 < baseStart_2163573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163574 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2163574 : Nat := 118140960795 + 2163574 * 2 ^ 59
def prefixEnd_2163574 : Nat := 4983230072969 + 3 ^ 40 * 2163574 * 2
def baseEnd_2163574 : Nat := 1110953393570823240474911

theorem tailTrace_2163574 : CollatzResearch.WordTrace tailWord_2163574 prefixEnd_2163574 1110953393570823240474911 := by
  unfold tailWord_2163574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4932001666484273866637111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52608017775832254577462517 4932001666484273866637111)
  ·
    refine ⟨7398002499726410799955667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4932001666484273866637111 7398002499726410799955667)
    ·
      refine ⟨11097003749589616199933501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7398002499726410799955667 11097003749589616199933501)
      ·
        refine ⟨4161376406096106074975063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11097003749589616199933501 4161376406096106074975063)
        ·
          refine ⟨6242064609144159112462595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161376406096106074975063 6242064609144159112462595)
          ·
            refine ⟨9363096913716238668693893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6242064609144159112462595 9363096913716238668693893)
            ·
              refine ⟨1755580671321794750380105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9363096913716238668693893 1755580671321794750380105)
              ·
                refine ⟨1316685503491346062785079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1755580671321794750380105 1316685503491346062785079)
                ·
                  refine ⟨1975028255237019094177619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316685503491346062785079 1975028255237019094177619)
                  ·
                    refine ⟨2962542382855528641266429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1975028255237019094177619 2962542382855528641266429)
                    ·
                      refine ⟨1110953393570823240474911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962542382855528641266429 1110953393570823240474911)
                      ·
                        rfl

theorem cell23_2163574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2163574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163574 prefixEnd_2163574 := by exact prefixLift 2163574
  have htrace : WordTrace (prefixWord ++ tailWord_2163574) baseStart_2163574 baseEnd_2163574 := by
    simpa [prefixWord, tailWord_2163574, baseEnd_2163574] using wordTrace_append hprefix tailTrace_2163574
  have hstable : (prefixWord ++ tailWord_2163574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163574).length < 2 ^ (prefixWord ++ tailWord_2163574).sum := by decide
  have hdescent : baseEnd_2163574 < baseStart_2163574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163596 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_2163596 : Nat := 118140960795 + 2163596 * 2 ^ 59
def prefixEnd_2163596 : Nat := 4983230072969 + 3 ^ 40 * 2163596 * 2
def baseEnd_2163596 : Nat := 1110964690145222154399809

theorem tailTrace_2163596 : CollatzResearch.WordTrace tailWord_2163596 prefixEnd_2163596 1110964690145222154399809 := by
  unfold tailWord_2163596
  simp only [CollatzResearch.WordTrace]
  refine ⟨39456414534834339811747321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52608552713112453082329761 39456414534834339811747321)
  ·
    refine ⟨29592310901125754858810491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39456414534834339811747321 29592310901125754858810491)
    ·
      refine ⟨44388466351688632288215737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29592310901125754858810491 44388466351688632288215737)
      ·
        refine ⟨33291349763766474216161803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44388466351688632288215737 33291349763766474216161803)
        ·
          refine ⟨49937024645649711324242705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33291349763766474216161803 49937024645649711324242705)
          ·
            refine ⟨37452768484237283493182029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49937024645649711324242705 37452768484237283493182029)
            ·
              refine ⟨14044788181588981309943261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37452768484237283493182029 14044788181588981309943261)
              ·
                refine ⟨5266795568095867991228723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14044788181588981309943261 5266795568095867991228723)
                ·
                  refine ⟨7900193352143801986843085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5266795568095867991228723 7900193352143801986843085)
                  ·
                    refine ⟨2962572507053925745066157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7900193352143801986843085 2962572507053925745066157)
                    ·
                      refine ⟨1110964690145222154399809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962572507053925745066157 1110964690145222154399809)
                      ·
                        rfl

theorem cell23_2163596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_2163596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163596 prefixEnd_2163596 := by exact prefixLift 2163596
  have htrace : WordTrace (prefixWord ++ tailWord_2163596) baseStart_2163596 baseEnd_2163596 := by
    simpa [prefixWord, tailWord_2163596, baseEnd_2163596] using wordTrace_append hprefix tailTrace_2163596
  have hstable : (prefixWord ++ tailWord_2163596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163596).length < 2 ^ (prefixWord ++ tailWord_2163596).sum := by decide
  have hdescent : baseEnd_2163596 < baseStart_2163596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163609 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_2163609 : Nat := 118140960795 + 2163609 * 2 ^ 59
def prefixEnd_2163609 : Nat := 4983230072969 + 3 ^ 40 * 2163609 * 2
def baseEnd_2163609 : Nat := 1110971365393730603537249

theorem tailTrace_2163609 : CollatzResearch.WordTrace tailWord_2163609 prefixEnd_2163609 1110971365393730603537249 := by
  unfold tailWord_2163609
  simp only [CollatzResearch.WordTrace]
  refine ⟨78913303218621582843717881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52608868812414388562478587 78913303218621582843717881)
  ·
    refine ⟨59184977413966187132788411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78913303218621582843717881 59184977413966187132788411)
    ·
      refine ⟨88777466120949280699182617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59184977413966187132788411 88777466120949280699182617)
      ·
        refine ⟨66583099590711960524386963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88777466120949280699182617 66583099590711960524386963)
        ·
          refine ⟨99874649386067940786580445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66583099590711960524386963 99874649386067940786580445)
          ·
            refine ⟨37452993519775477794967667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99874649386067940786580445 37452993519775477794967667)
            ·
              refine ⟨56179490279663216692451501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37452993519775477794967667 56179490279663216692451501)
              ·
                refine ⟨21067308854873706259669313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56179490279663216692451501 21067308854873706259669313)
                ·
                  refine ⟨15800481641155279694751985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21067308854873706259669313 15800481641155279694751985)
                  ·
                    refine ⟨11850361230866459771063989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15800481641155279694751985 11850361230866459771063989)
                    ·
                      refine ⟨1110971365393730603537249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11850361230866459771063989 1110971365393730603537249)
                      ·
                        rfl

theorem cell23_2163609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_2163609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163609 prefixEnd_2163609 := by exact prefixLift 2163609
  have htrace : WordTrace (prefixWord ++ tailWord_2163609) baseStart_2163609 baseEnd_2163609 := by
    simpa [prefixWord, tailWord_2163609, baseEnd_2163609] using wordTrace_append hprefix tailTrace_2163609
  have hstable : (prefixWord ++ tailWord_2163609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163609).length < 2 ^ (prefixWord ++ tailWord_2163609).sum := by decide
  have hdescent : baseEnd_2163609 < baseStart_2163609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163613 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2163613 : Nat := 118140960795 + 2163613 * 2 ^ 59
def prefixEnd_2163613 : Nat := 4983230072969 + 3 ^ 40 * 2163613 * 2
def baseEnd_2163613 : Nat := 1110973419316348587887231

theorem tailTrace_2163613 : CollatzResearch.WordTrace tailWord_2163613 prefixEnd_2163613 1110973419316348587887231 := by
  unfold tailWord_2163613
  simp only [CollatzResearch.WordTrace]
  refine ⟨78913449110607091526863493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52608966073738061017908995 78913449110607091526863493)
  ·
    refine ⟨14796271708238829661286905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78913449110607091526863493 14796271708238829661286905)
    ·
      refine ⟨11097203781179122245965179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14796271708238829661286905 11097203781179122245965179)
      ·
        refine ⟨16645805671768683368947769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11097203781179122245965179 16645805671768683368947769)
        ·
          refine ⟨12484354253826512526710827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16645805671768683368947769 12484354253826512526710827)
          ·
            refine ⟨18726531380739768790066241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12484354253826512526710827 18726531380739768790066241)
            ·
              refine ⟨14044898535554826592549681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18726531380739768790066241 14044898535554826592549681)
              ·
                refine ⟨10533673901666119944412261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14044898535554826592549681 10533673901666119944412261)
                ·
                  refine ⟨1975063856562397489577299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10533673901666119944412261 1975063856562397489577299)
                  ·
                    refine ⟨2962595784843596234365949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1975063856562397489577299 2962595784843596234365949)
                    ·
                      refine ⟨1110973419316348587887231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962595784843596234365949 1110973419316348587887231)
                      ·
                        rfl

theorem cell23_2163613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2163613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163613 prefixEnd_2163613 := by exact prefixLift 2163613
  have htrace : WordTrace (prefixWord ++ tailWord_2163613) baseStart_2163613 baseEnd_2163613 := by
    simpa [prefixWord, tailWord_2163613, baseEnd_2163613] using wordTrace_append hprefix tailTrace_2163613
  have hstable : (prefixWord ++ tailWord_2163613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163613).length < 2 ^ (prefixWord ++ tailWord_2163613).sum := by decide
  have hdescent : baseEnd_2163613 < baseStart_2163613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163617 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2163617 : Nat := 118140960795 + 2163617 * 2 ^ 59
def prefixEnd_2163617 : Nat := 4983230072969 + 3 ^ 40 * 2163617 * 2
def baseEnd_2163617 : Nat := 1110975473238966572237213

theorem tailTrace_2163617 : CollatzResearch.WordTrace tailWord_2163617 prefixEnd_2163617 1110975473238966572237213 := by
  unfold tailWord_2163617
  simp only [CollatzResearch.WordTrace]
  refine ⟨78913595002592600210009105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52609063335061733473339403 78913595002592600210009105)
  ·
    refine ⟨59185196251944450157506829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78913595002592600210009105 59185196251944450157506829)
    ·
      refine ⟨22194448594479168809065061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59185196251944450157506829 22194448594479168809065061)
      ·
        refine ⟨4161459111464844151699699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22194448594479168809065061 4161459111464844151699699)
        ·
          refine ⟨6242188667197266227549549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161459111464844151699699 6242188667197266227549549)
          ·
            refine ⟨2340820750198974835331081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6242188667197266227549549 2340820750198974835331081)
            ·
              refine ⟨1755615562649231126498311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340820750198974835331081 1755615562649231126498311)
              ·
                refine ⟨2633423343973846689747467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755615562649231126498311 2633423343973846689747467)
                ·
                  refine ⟨3950135015960770034621201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633423343973846689747467 3950135015960770034621201)
                  ·
                    refine ⟨2962601261970577525965901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950135015960770034621201 2962601261970577525965901)
                    ·
                      refine ⟨1110975473238966572237213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962601261970577525965901 1110975473238966572237213)
                      ·
                        rfl

theorem cell23_2163617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2163617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163617 prefixEnd_2163617 := by exact prefixLift 2163617
  have htrace : WordTrace (prefixWord ++ tailWord_2163617) baseStart_2163617 baseEnd_2163617 := by
    simpa [prefixWord, tailWord_2163617, baseEnd_2163617] using wordTrace_append hprefix tailTrace_2163617
  have hstable : (prefixWord ++ tailWord_2163617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163617).length < 2 ^ (prefixWord ++ tailWord_2163617).sum := by decide
  have hdescent : baseEnd_2163617 < baseStart_2163617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163646 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2163646 : Nat := 118140960795 + 2163646 * 2 ^ 59
def prefixEnd_2163646 : Nat := 4983230072969 + 3 ^ 40 * 2163646 * 2
def baseEnd_2163646 : Nat := 370330121392648986258193

theorem tailTrace_2163646 : CollatzResearch.WordTrace tailWord_2163646 prefixEnd_2163646 370330121392648986258193 := by
  unfold tailWord_2163646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9864331589935942270351849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52609768479658358775209861 9864331589935942270351849)
  ·
    refine ⟨7398248692451956702763887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9864331589935942270351849 7398248692451956702763887)
    ·
      refine ⟨11097373038677935054145831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7398248692451956702763887 11097373038677935054145831)
      ·
        refine ⟨16646059558016902581218747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11097373038677935054145831 16646059558016902581218747)
        ·
          refine ⟨24969089337025353871828121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16646059558016902581218747 24969089337025353871828121)
          ·
            refine ⟨18726817002769015403871091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24969089337025353871828121 18726817002769015403871091)
            ·
              refine ⟨28090225504153523105806637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18726817002769015403871091 28090225504153523105806637)
              ·
                refine ⟨10533834564057571164677489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28090225504153523105806637 10533834564057571164677489)
                ·
                  refine ⟨7900375923043178373508117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10533834564057571164677489 7900375923043178373508117)
                  ·
                    refine ⟨370330121392648986258193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7900375923043178373508117 370330121392648986258193)
                    ·
                      rfl

theorem cell23_2163646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2163646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163646 prefixEnd_2163646 := by exact prefixLift 2163646
  have htrace : WordTrace (prefixWord ++ tailWord_2163646) baseStart_2163646 baseEnd_2163646 := by
    simpa [prefixWord, tailWord_2163646, baseEnd_2163646] using wordTrace_append hprefix tailTrace_2163646
  have hstable : (prefixWord ++ tailWord_2163646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163646).length < 2 ^ (prefixWord ++ tailWord_2163646).sum := by decide
  have hdescent : baseEnd_2163646 < baseStart_2163646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163689 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_2163689 : Nat := 118140960795 + 2163689 * 2 ^ 59
def prefixEnd_2163689 : Nat := 4983230072969 + 3 ^ 40 * 2163689 * 2
def baseEnd_2163689 : Nat := 370337481282030096845627

theorem tailTrace_2163689 : CollatzResearch.WordTrace tailWord_2163689 prefixEnd_2163689 370337481282030096845627 := by
  unfold tailWord_2163689
  simp only [CollatzResearch.WordTrace]
  refine ⟨78916221058331756506630121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52610814038887837671086747 78916221058331756506630121)
  ·
    refine ⟨59187165793748817379972591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78916221058331756506630121 59187165793748817379972591)
    ·
      refine ⟨88780748690623226069958887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59187165793748817379972591 88780748690623226069958887)
      ·
        refine ⟨133171123035934839104938331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88780748690623226069958887 133171123035934839104938331)
        ·
          refine ⟨199756684553902258657407497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133171123035934839104938331 199756684553902258657407497)
          ·
            refine ⟨149817513415426693993055623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199756684553902258657407497 149817513415426693993055623)
            ·
              refine ⟨224726270123140040989583435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149817513415426693993055623 224726270123140040989583435)
              ·
                refine ⟨337089405184710061484375153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224726270123140040989583435 337089405184710061484375153)
                ·
                  refine ⟨252817053888532546113281365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337089405184710061484375153 252817053888532546113281365)
                  ·
                    refine ⟨370337481282030096845627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 252817053888532546113281365 370337481282030096845627)
                    ·
                      rfl

theorem cell23_2163689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_2163689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163689 prefixEnd_2163689 := by exact prefixLift 2163689
  have htrace : WordTrace (prefixWord ++ tailWord_2163689) baseStart_2163689 baseEnd_2163689 := by
    simpa [prefixWord, tailWord_2163689, baseEnd_2163689] using wordTrace_append hprefix tailTrace_2163689
  have hstable : (prefixWord ++ tailWord_2163689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163689).length < 2 ^ (prefixWord ++ tailWord_2163689).sum := by decide
  have hdescent : baseEnd_2163689 < baseStart_2163689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163723 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 2, 5]
def baseStart_2163723 : Nat := 118140960795 + 2163723 * 2 ^ 59
def prefixEnd_2163723 : Nat := 4983230072969 + 3 ^ 40 * 2163723 * 2
def baseEnd_2163723 : Nat := 370343300729447719170575

theorem tailTrace_2163723 : CollatzResearch.WordTrace tailWord_2163723 prefixEnd_2163723 370343300729447719170575 := by
  unfold tailWord_2163723
  simp only [CollatzResearch.WordTrace]
  refine ⟨78917461140208580313367823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52611640760139053542245215 78917461140208580313367823)
  ·
    refine ⟨118376191710312870470051735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78917461140208580313367823 118376191710312870470051735)
    ·
      refine ⟨177564287565469305705077603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118376191710312870470051735 177564287565469305705077603)
      ·
        refine ⟨266346431348203958557616405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177564287565469305705077603 266346431348203958557616405)
        ·
          refine ⟨12484988969447060557388269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 266346431348203958557616405 12484988969447060557388269)
          ·
            refine ⟨4681870863542647709020601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12484988969447060557388269 4681870863542647709020601)
            ·
              refine ⟨3511403147656985781765451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4681870863542647709020601 3511403147656985781765451)
              ·
                refine ⟨5267104721485478672648177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511403147656985781765451 5267104721485478672648177)
                ·
                  refine ⟨3950328541114109004486133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267104721485478672648177 3950328541114109004486133)
                  ·
                    refine ⟨370343300729447719170575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3950328541114109004486133 370343300729447719170575)
                    ·
                      rfl

theorem cell23_2163723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 5].length) (baseStart_2163723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163723 prefixEnd_2163723 := by exact prefixLift 2163723
  have htrace : WordTrace (prefixWord ++ tailWord_2163723) baseStart_2163723 baseEnd_2163723 := by
    simpa [prefixWord, tailWord_2163723, baseEnd_2163723] using wordTrace_append hprefix tailTrace_2163723
  have hstable : (prefixWord ++ tailWord_2163723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163723).length < 2 ^ (prefixWord ++ tailWord_2163723).sum := by decide
  have hdescent : baseEnd_2163723 < baseStart_2163723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163743 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2163743 : Nat := 118140960795 + 2163743 * 2 ^ 59
def prefixEnd_2163743 : Nat := 4983230072969 + 3 ^ 40 * 2163743 * 2
def baseEnd_2163743 : Nat := 1111040171801433079261633

theorem tailTrace_2163743 : CollatzResearch.WordTrace tailWord_2163743 prefixEnd_2163743 1111040171801433079261633 := by
  unfold tailWord_2163743
  simp only [CollatzResearch.WordTrace]
  refine ⟨78918190600136123729095883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52612127066757415819397255 78918190600136123729095883)
  ·
    refine ⟨118377285900204185593643825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78918190600136123729095883 118377285900204185593643825)
    ·
      refine ⟨88782964425153139195232869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118377285900204185593643825 88782964425153139195232869)
      ·
        refine ⟨16646805829716213599106163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88782964425153139195232869 16646805829716213599106163)
        ·
          refine ⟨24970208744574320398659245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16646805829716213599106163 24970208744574320398659245)
          ·
            refine ⟨9363828279215370149497217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24970208744574320398659245 9363828279215370149497217)
            ·
              refine ⟨7022871209411527612122913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9363828279215370149497217 7022871209411527612122913)
              ·
                refine ⟨5267153407058645709092185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7022871209411527612122913 5267153407058645709092185)
                ·
                  refine ⟨3950365055293984281819139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267153407058645709092185 3950365055293984281819139)
                  ·
                    refine ⟨5925547582940976422728709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950365055293984281819139 5925547582940976422728709)
                    ·
                      refine ⟨1111040171801433079261633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5925547582940976422728709 1111040171801433079261633)
                      ·
                        rfl

theorem cell23_2163743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2163743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163743 prefixEnd_2163743 := by exact prefixLift 2163743
  have htrace : WordTrace (prefixWord ++ tailWord_2163743) baseStart_2163743 baseEnd_2163743 := by
    simpa [prefixWord, tailWord_2163743, baseEnd_2163743] using wordTrace_append hprefix tailTrace_2163743
  have hstable : (prefixWord ++ tailWord_2163743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163743).length < 2 ^ (prefixWord ++ tailWord_2163743).sum := by decide
  have hdescent : baseEnd_2163743 < baseStart_2163743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163744 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 5]
def baseStart_2163744 : Nat := 118140960795 + 2163744 * 2 ^ 59
def prefixEnd_2163744 : Nat := 4983230072969 + 3 ^ 40 * 2163744 * 2
def baseEnd_2163744 : Nat := 123448965031343063927681

theorem tailTrace_2163744 : CollatzResearch.WordTrace tailWord_2163744 prefixEnd_2163744 123448965031343063927681 := by
  unfold tailWord_2163744
  simp only [CollatzResearch.WordTrace]
  refine ⟨39459113536566250449941143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52612151382088333933254857 39459113536566250449941143)
  ·
    refine ⟨59188670304849375674911715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39459113536566250449941143 59188670304849375674911715)
    ·
      refine ⟨88783005457274063512367573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59188670304849375674911715 88783005457274063512367573)
      ·
        refine ⟨2080851690404860863571115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 88783005457274063512367573 2080851690404860863571115)
        ·
          refine ⟨3121277535607291295356673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080851690404860863571115 3121277535607291295356673)
          ·
            refine ⟨2340958151705468471517505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121277535607291295356673 2340958151705468471517505)
            ·
              refine ⟨1755718613779101353638129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340958151705468471517505 1755718613779101353638129)
              ·
                refine ⟨1316788960334326015228597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1755718613779101353638129 1316788960334326015228597)
                ·
                  refine ⟨123448965031343063927681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1316788960334326015228597 123448965031343063927681)
                  ·
                    rfl

theorem cell23_2163744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 5].length) (baseStart_2163744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163744 prefixEnd_2163744 := by exact prefixLift 2163744
  have htrace : WordTrace (prefixWord ++ tailWord_2163744) baseStart_2163744 baseEnd_2163744 := by
    simpa [prefixWord, tailWord_2163744, baseEnd_2163744] using wordTrace_append hprefix tailTrace_2163744
  have hstable : (prefixWord ++ tailWord_2163744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163744).length < 2 ^ (prefixWord ++ tailWord_2163744).sum := by decide
  have hdescent : baseEnd_2163744 < baseStart_2163744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163777 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2163777 : Nat := 118140960795 + 2163777 * 2 ^ 59
def prefixEnd_2163777 : Nat := 4983230072969 + 3 ^ 40 * 2163777 * 2
def baseEnd_2163777 : Nat := 1111057630143685946236477

theorem tailTrace_2163777 : CollatzResearch.WordTrace tailWord_2163777 prefixEnd_2163777 1111057630143685946236477 := by
  unfold tailWord_2163777
  simp only [CollatzResearch.WordTrace]
  refine ⟨78919430682012947535833585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52612953788008631690555723 78919430682012947535833585)
  ·
    refine ⟨59189573011509710651875189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78919430682012947535833585 59189573011509710651875189)
    ·
      refine ⟨5549022469829035373613299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59189573011509710651875189 5549022469829035373613299)
      ·
        refine ⟨8323533704743553060419949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5549022469829035373613299 8323533704743553060419949)
        ·
          refine ⟨3121325139278832397657481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8323533704743553060419949 3121325139278832397657481)
          ·
            refine ⟨2340993854459124298243111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121325139278832397657481 2340993854459124298243111)
            ·
              refine ⟨3511490781688686447364667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340993854459124298243111 3511490781688686447364667)
              ·
                refine ⟨5267236172533029671047001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511490781688686447364667 5267236172533029671047001)
                ·
                  refine ⟨3950427129399772253285251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267236172533029671047001 3950427129399772253285251)
                  ·
                    refine ⟨5925640694099658379927877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950427129399772253285251 5925640694099658379927877)
                    ·
                      refine ⟨1111057630143685946236477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5925640694099658379927877 1111057630143685946236477)
                      ·
                        rfl

theorem cell23_2163777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2163777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163777 prefixEnd_2163777 := by exact prefixLift 2163777
  have htrace : WordTrace (prefixWord ++ tailWord_2163777) baseStart_2163777 baseEnd_2163777 := by
    simpa [prefixWord, tailWord_2163777, baseEnd_2163777] using wordTrace_append hprefix tailTrace_2163777
  have hstable : (prefixWord ++ tailWord_2163777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163777).length < 2 ^ (prefixWord ++ tailWord_2163777).sum := by decide
  have hdescent : baseEnd_2163777 < baseStart_2163777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163843 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 6, 4]
def baseStart_2163843 : Nat := 118140960795 + 2163843 * 2 ^ 59
def prefixEnd_2163843 : Nat := 4983230072969 + 3 ^ 40 * 2163843 * 2
def baseEnd_2163843 : Nat := 370363839955627562670391

theorem tailTrace_2163843 : CollatzResearch.WordTrace tailWord_2163843 prefixEnd_2163843 370363839955627562670391 := by
  unfold tailWord_2163843
  simp only [CollatzResearch.WordTrace]
  refine ⟨78921837899773840807736183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52614558599849227205157455 78921837899773840807736183)
  ·
    refine ⟨118382756849660761211604275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78921837899773840807736183 118382756849660761211604275)
    ·
      refine ⟨177574135274491141817406413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118382756849660761211604275 177574135274491141817406413)
      ·
        refine ⟨66590300727934178181527405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177574135274491141817406413 66590300727934178181527405)
        ·
          refine ⟨24971362772975316818072777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66590300727934178181527405 24971362772975316818072777)
          ·
            refine ⟨18728522079731487613554583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24971362772975316818072777 18728522079731487613554583)
            ·
              refine ⟨28092783119597231420331875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18728522079731487613554583 28092783119597231420331875)
              ·
                refine ⟨42139174679395847130497813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28092783119597231420331875 42139174679395847130497813)
                ·
                  refine ⟨1975273813096680334242085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42139174679395847130497813 1975273813096680334242085)
                  ·
                    refine ⟨370363839955627562670391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975273813096680334242085 370363839955627562670391)
                    ·
                      rfl

theorem cell23_2163843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 4].length) (baseStart_2163843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163843 prefixEnd_2163843 := by exact prefixLift 2163843
  have htrace : WordTrace (prefixWord ++ tailWord_2163843) baseStart_2163843 baseEnd_2163843 := by
    simpa [prefixWord, tailWord_2163843, baseEnd_2163843] using wordTrace_append hprefix tailTrace_2163843
  have hstable : (prefixWord ++ tailWord_2163843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163843).length < 2 ^ (prefixWord ++ tailWord_2163843).sum := by decide
  have hdescent : baseEnd_2163843 < baseStart_2163843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163844 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_2163844 : Nat := 118140960795 + 2163844 * 2 ^ 59
def prefixEnd_2163844 : Nat := 4983230072969 + 3 ^ 40 * 2163844 * 2
def baseEnd_2163844 : Nat := 1111092033347537184098669

theorem tailTrace_2163844 : CollatzResearch.WordTrace tailWord_2163844 prefixEnd_2163844 1111092033347537184098669 := by
  unfold tailWord_2163844
  simp only [CollatzResearch.WordTrace]
  refine ⟨39460937186385108989261293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52614582915180145319015057 39460937186385108989261293)
  ·
    refine ⟨14797851444894415870972985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39460937186385108989261293 14797851444894415870972985)
    ·
      refine ⟨11098388583670811903229739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14797851444894415870972985 11098388583670811903229739)
      ·
        refine ⟨16647582875506217854844609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11098388583670811903229739 16647582875506217854844609)
        ·
          refine ⟨12485687156629663391133457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16647582875506217854844609 12485687156629663391133457)
          ·
            refine ⟨9364265367472247543350093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12485687156629663391133457 9364265367472247543350093)
            ·
              refine ⟨3511599512802092828756285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9364265367472247543350093 3511599512802092828756285)
              ·
                refine ⟨1316849817300784810783607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3511599512802092828756285 1316849817300784810783607)
                ·
                  refine ⟨1975274725951177216175411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316849817300784810783607 1975274725951177216175411)
                  ·
                    refine ⟨2962912088926765824263117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1975274725951177216175411 2962912088926765824263117)
                    ·
                      refine ⟨1111092033347537184098669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962912088926765824263117 1111092033347537184098669)
                      ·
                        rfl

theorem cell23_2163844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_2163844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163844 prefixEnd_2163844 := by exact prefixLift 2163844
  have htrace : WordTrace (prefixWord ++ tailWord_2163844) baseStart_2163844 baseEnd_2163844 := by
    simpa [prefixWord, tailWord_2163844, baseEnd_2163844] using wordTrace_append hprefix tailTrace_2163844
  have hstable : (prefixWord ++ tailWord_2163844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163844).length < 2 ^ (prefixWord ++ tailWord_2163844).sum := by decide
  have hdescent : baseEnd_2163844 < baseStart_2163844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163850 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2163850 : Nat := 118140960795 + 2163850 * 2 ^ 59
def prefixEnd_2163850 : Nat := 4983230072969 + 3 ^ 40 * 2163850 * 2
def baseEnd_2163850 : Nat := 1111095114231464160623641

theorem tailTrace_2163850 : CollatzResearch.WordTrace tailWord_2163850 prefixEnd_2163850 1111095114231464160623641 := by
  unfold tailWord_2163850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19730523302687120250810251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52614728807165654002160669 19730523302687120250810251)
  ·
    refine ⟨29595784954030680376215377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19730523302687120250810251 29595784954030680376215377)
    ·
      refine ⟨22196838715523010282161533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29595784954030680376215377 22196838715523010282161533)
      ·
        refine ⟨8323814518321128855810575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22196838715523010282161533 8323814518321128855810575)
        ·
          refine ⟨12485721777481693283715863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8323814518321128855810575 12485721777481693283715863)
          ·
            refine ⟨18728582666222539925573795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12485721777481693283715863 18728582666222539925573795)
            ·
              refine ⟨28092873999333809888360693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18728582666222539925573795 28092873999333809888360693)
              ·
                refine ⟨2633706937437544677033815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28092873999333809888360693 2633706937437544677033815)
                ·
                  refine ⟨3950560406156317015550723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633706937437544677033815 3950560406156317015550723)
                  ·
                    refine ⟨5925840609234475523326085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950560406156317015550723 5925840609234475523326085)
                    ·
                      refine ⟨1111095114231464160623641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5925840609234475523326085 1111095114231464160623641)
                      ·
                        rfl

theorem cell23_2163850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2163850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163850 prefixEnd_2163850 := by exact prefixLift 2163850
  have htrace : WordTrace (prefixWord ++ tailWord_2163850) baseStart_2163850 baseEnd_2163850 := by
    simpa [prefixWord, tailWord_2163850, baseEnd_2163850] using wordTrace_append hprefix tailTrace_2163850
  have hstable : (prefixWord ++ tailWord_2163850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163850).length < 2 ^ (prefixWord ++ tailWord_2163850).sum := by decide
  have hdescent : baseEnd_2163850 < baseStart_2163850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163863 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2163863 : Nat := 118140960795 + 2163863 * 2 ^ 59
def prefixEnd_2163863 : Nat := 4983230072969 + 3 ^ 40 * 2163863 * 2
def baseEnd_2163863 : Nat := 1111101789479972609761081

theorem tailTrace_2163863 : CollatzResearch.WordTrace tailWord_2163863 prefixEnd_2163863 1111101789479972609761081 := by
  unfold tailWord_2163863
  simp only [CollatzResearch.WordTrace]
  refine ⟨78922567359701384223464243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52615044906467589482309495 78922567359701384223464243)
  ·
    refine ⟨118383851039552076335196365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78922567359701384223464243 118383851039552076335196365)
    ·
      refine ⟨44393944139832028625698637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118383851039552076335196365 44393944139832028625698637)
      ·
        refine ⟨16647729052437010734636989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44393944139832028625698637 16647729052437010734636989)
        ·
          refine ⟨6242898394663879025488871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16647729052437010734636989 6242898394663879025488871)
          ·
            refine ⟨9364347591995818538233307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6242898394663879025488871 9364347591995818538233307)
            ·
              refine ⟨14046521387993727807349961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9364347591995818538233307 14046521387993727807349961)
              ·
                refine ⟨10534891040995295855512471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14046521387993727807349961 10534891040995295855512471)
                ·
                  refine ⟨15802336561492943783268707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10534891040995295855512471 15802336561492943783268707)
                  ·
                    refine ⟨23703504842239415674903061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15802336561492943783268707 23703504842239415674903061)
                    ·
                      refine ⟨1111101789479972609761081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23703504842239415674903061 1111101789479972609761081)
                      ·
                        rfl

theorem cell23_2163863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2163863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163863 prefixEnd_2163863 := by exact prefixLift 2163863
  have htrace : WordTrace (prefixWord ++ tailWord_2163863) baseStart_2163863 baseEnd_2163863 := by
    simpa [prefixWord, tailWord_2163863, baseEnd_2163863] using wordTrace_append hprefix tailTrace_2163863
  have hstable : (prefixWord ++ tailWord_2163863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163863).length < 2 ^ (prefixWord ++ tailWord_2163863).sum := by decide
  have hdescent : baseEnd_2163863 < baseStart_2163863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163873 : List Nat := [1, 2, 3, 3, 1, 1, 4, 8]
def baseStart_2163873 : Nat := 118140960795 + 2163873 * 2 ^ 59
def prefixEnd_2163873 : Nat := 4983230072969 + 3 ^ 40 * 2163873 * 2
def baseEnd_2163873 : Nat := 41152108306908058171705

theorem tailTrace_2163873 : CollatzResearch.WordTrace tailWord_2163873 prefixEnd_2163873 41152108306908058171705 := by
  unfold tailWord_2163873
  simp only [CollatzResearch.WordTrace]
  refine ⟨78922932089665155931328273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52615288059776770620885515 78922932089665155931328273)
  ·
    refine ⟨59192199067248866948496205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78922932089665155931328273 59192199067248866948496205)
    ·
      refine ⟨22197074650218325105686077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59192199067248866948496205 22197074650218325105686077)
      ·
        refine ⟨8323902993831871914632279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22197074650218325105686077 8323902993831871914632279)
        ·
          refine ⟨12485854490747807871948419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8323902993831871914632279 12485854490747807871948419)
          ·
            refine ⟨18728781736121711807922629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12485854490747807871948419 18728781736121711807922629)
            ·
              refine ⟨3511646575522820963985493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18728781736121711807922629 3511646575522820963985493)
              ·
                refine ⟨41152108306908058171705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3511646575522820963985493 41152108306908058171705)
                ·
                  rfl

theorem cell23_2163873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 8].length) (baseStart_2163873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163873 prefixEnd_2163873 := by exact prefixLift 2163873
  have htrace : WordTrace (prefixWord ++ tailWord_2163873) baseStart_2163873 baseEnd_2163873 := by
    simpa [prefixWord, tailWord_2163873, baseEnd_2163873] using wordTrace_append hprefix tailTrace_2163873
  have hstable : (prefixWord ++ tailWord_2163873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163873).length < 2 ^ (prefixWord ++ tailWord_2163873).sum := by decide
  have hdescent : baseEnd_2163873 < baseStart_2163873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163877 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_2163877 : Nat := 118140960795 + 2163877 * 2 ^ 59
def prefixEnd_2163877 : Nat := 4983230072969 + 3 ^ 40 * 2163877 * 2
def baseEnd_2163877 : Nat := 370369659403045184995339

theorem tailTrace_2163877 : CollatzResearch.WordTrace tailWord_2163877 prefixEnd_2163877 370369659403045184995339 := by
  unfold tailWord_2163877
  simp only [CollatzResearch.WordTrace]
  refine ⟨78923077981650664614473885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52615385321100443076315923 78923077981650664614473885)
  ·
    refine ⟨29596154243118999230427707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78923077981650664614473885 29596154243118999230427707)
    ·
      refine ⟨44394231364678498845641561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29596154243118999230427707 44394231364678498845641561)
      ·
        refine ⟨33295673523508874134231171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44394231364678498845641561 33295673523508874134231171)
        ·
          refine ⟨49943510285263311201346757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33295673523508874134231171 49943510285263311201346757)
          ·
            refine ⟨9364408178486870850252517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49943510285263311201346757 9364408178486870850252517)
            ·
              refine ⟨1755826533466288284422347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9364408178486870850252517 1755826533466288284422347)
              ·
                refine ⟨2633739800199432426633521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755826533466288284422347 2633739800199432426633521)
                ·
                  refine ⟨1975304850149574319975141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633739800199432426633521 1975304850149574319975141)
                  ·
                    refine ⟨370369659403045184995339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975304850149574319975141 370369659403045184995339)
                    ·
                      rfl

theorem cell23_2163877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_2163877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163877 prefixEnd_2163877 := by exact prefixLift 2163877
  have htrace : WordTrace (prefixWord ++ tailWord_2163877) baseStart_2163877 baseEnd_2163877 := by
    simpa [prefixWord, tailWord_2163877, baseEnd_2163877] using wordTrace_append hprefix tailTrace_2163877
  have hstable : (prefixWord ++ tailWord_2163877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163877).length < 2 ^ (prefixWord ++ tailWord_2163877).sum := by decide
  have hdescent : baseEnd_2163877 < baseStart_2163877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163894 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2163894 : Nat := 118140960795 + 2163894 * 2 ^ 59
def prefixEnd_2163894 : Nat := 4983230072969 + 3 ^ 40 * 2163894 * 2
def baseEnd_2163894 : Nat := 370372569126753996157813

theorem tailTrace_2163894 : CollatzResearch.WordTrace tailWord_2163894 prefixEnd_2163894 370372569126753996157813 := by
  unfold tailWord_2163894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4932731126411817282365171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52615798681726051011895157 4932731126411817282365171)
  ·
    refine ⟨7399096689617725923547757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4932731126411817282365171 7399096689617725923547757)
    ·
      refine ⟨2774661258606647221330409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7399096689617725923547757 2774661258606647221330409)
      ·
        refine ⟨2080995943954985415997807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774661258606647221330409 2080995943954985415997807)
        ·
          refine ⟨3121493915932478123996711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080995943954985415997807 3121493915932478123996711)
          ·
            refine ⟨4682240873898717185995067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121493915932478123996711 4682240873898717185995067)
            ·
              refine ⟨7023361310848075778992601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682240873898717185995067 7023361310848075778992601)
              ·
                refine ⟨5267520983136056834244451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7023361310848075778992601 5267520983136056834244451)
                ·
                  refine ⟨7901281474704085251366677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5267520983136056834244451 7901281474704085251366677)
                  ·
                    refine ⟨370372569126753996157813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7901281474704085251366677 370372569126753996157813)
                    ·
                      rfl

theorem cell23_2163894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2163894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163894 prefixEnd_2163894 := by exact prefixLift 2163894
  have htrace : WordTrace (prefixWord ++ tailWord_2163894) baseStart_2163894 baseEnd_2163894 := by
    simpa [prefixWord, tailWord_2163894, baseEnd_2163894] using wordTrace_append hprefix tailTrace_2163894
  have hstable : (prefixWord ++ tailWord_2163894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163894).length < 2 ^ (prefixWord ++ tailWord_2163894).sum := by decide
  have hdescent : baseEnd_2163894 < baseStart_2163894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163900 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_2163900 : Nat := 118140960795 + 2163900 * 2 ^ 59
def prefixEnd_2163900 : Nat := 4983230072969 + 3 ^ 40 * 2163900 * 2
def baseEnd_2163900 : Nat := 1111120788264188964998411

theorem tailTrace_2163900 : CollatzResearch.WordTrace tailWord_2163900 prefixEnd_2163900 1111120788264188964998411 := by
  unfold tailWord_2163900
  simp only [CollatzResearch.WordTrace]
  refine ⟨39461958430283669771280577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52615944573711559695040769 39461958430283669771280577)
  ·
    refine ⟨29596468822712752328460433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39461958430283669771280577 29596468822712752328460433)
    ·
      refine ⟨22197351617034564246345325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29596468822712752328460433 22197351617034564246345325)
      ·
        refine ⟨8324006856387961592379497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22197351617034564246345325 8324006856387961592379497)
        ·
          refine ⟨6243005142290971194284623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8324006856387961592379497 6243005142290971194284623)
          ·
            refine ⟨9364507713436456791426935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243005142290971194284623 9364507713436456791426935)
            ·
              refine ⟨14046761570154685187140403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9364507713436456791426935 14046761570154685187140403)
              ·
                refine ⟨21070142355232027780710605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14046761570154685187140403 21070142355232027780710605)
                ·
                  refine ⟨7901303383212010417766477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21070142355232027780710605 7901303383212010417766477)
                  ·
                    refine ⟨2962988768704503906662429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7901303383212010417766477 2962988768704503906662429)
                    ·
                      refine ⟨1111120788264188964998411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962988768704503906662429 1111120788264188964998411)
                      ·
                        rfl

theorem cell23_2163900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_2163900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163900 prefixEnd_2163900 := by exact prefixLift 2163900
  have htrace : WordTrace (prefixWord ++ tailWord_2163900) baseStart_2163900 baseEnd_2163900 := by
    simpa [prefixWord, tailWord_2163900, baseEnd_2163900] using wordTrace_append hprefix tailTrace_2163900
  have hstable : (prefixWord ++ tailWord_2163900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163900).length < 2 ^ (prefixWord ++ tailWord_2163900).sum := by decide
  have hdescent : baseEnd_2163900 < baseStart_2163900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163904 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 1, 2, 3]
def baseStart_2163904 : Nat := 118140960795 + 2163904 * 2 ^ 59
def prefixEnd_2163904 : Nat := 4983230072969 + 3 ^ 40 * 2163904 * 2
def baseEnd_2163904 : Nat := 1111122842186806949348393

theorem tailTrace_2163904 : CollatzResearch.WordTrace tailWord_2163904 prefixEnd_2163904 1111122842186806949348393 := by
  unfold tailWord_2163904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39462031376276424112853383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52616041835035232150471177 39462031376276424112853383)
  ·
    refine ⟨59193047064414636169280075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39462031376276424112853383 59193047064414636169280075)
    ·
      refine ⟨88789570596621954253920113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59193047064414636169280075 88789570596621954253920113)
      ·
        refine ⟨66592177947466465690440085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88789570596621954253920113 66592177947466465690440085)
        ·
          refine ⟨3121508341287490579239379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66592177947466465690440085 3121508341287490579239379)
          ·
            refine ⟨4682262511931235868859069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121508341287490579239379 4682262511931235868859069)
            ·
              refine ⟨1755848441974213450822151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4682262511931235868859069 1755848441974213450822151)
              ·
                refine ⟨2633772662961320176233227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755848441974213450822151 2633772662961320176233227)
                ·
                  refine ⟨3950658994441980264349841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633772662961320176233227 3950658994441980264349841)
                  ·
                    refine ⟨2962994245831485198262381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950658994441980264349841 2962994245831485198262381)
                    ·
                      refine ⟨1111122842186806949348393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2962994245831485198262381 1111122842186806949348393)
                      ·
                        rfl

theorem cell23_2163904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_2163904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163904 prefixEnd_2163904 := by exact prefixLift 2163904
  have htrace : WordTrace (prefixWord ++ tailWord_2163904) baseStart_2163904 baseEnd_2163904 := by
    simpa [prefixWord, tailWord_2163904, baseEnd_2163904] using wordTrace_append hprefix tailTrace_2163904
  have hstable : (prefixWord ++ tailWord_2163904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163904).length < 2 ^ (prefixWord ++ tailWord_2163904).sum := by decide
  have hdescent : baseEnd_2163904 < baseStart_2163904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163924 : List Nat := [2, 4, 1, 4, 2, 1, 1, 8]
def baseStart_2163924 : Nat := 118140960795 + 2163924 * 2 ^ 59
def prefixEnd_2163924 : Nat := 4983230072969 + 3 ^ 40 * 2163924 * 2
def baseEnd_2163924 : Nat := 41153078214810995225863

theorem tailTrace_2163924 : CollatzResearch.WordTrace tailWord_2163924 prefixEnd_2163924 41153078214810995225863 := by
  unfold tailWord_2163924
  simp only [CollatzResearch.WordTrace]
  refine ⟨39462396106240195820717413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52616528141653594427623217 39462396106240195820717413)
  ·
    refine ⟨7399199269920036716384515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39462396106240195820717413 7399199269920036716384515)
    ·
      refine ⟨11098798904880055074576773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7399199269920036716384515 11098798904880055074576773)
      ·
        refine ⟨2081024794665010326483145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11098798904880055074576773 2081024794665010326483145)
        ·
          refine ⟨1560768595998757744862359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2081024794665010326483145 1560768595998757744862359)
          ·
            refine ⟨2341152893998136617293539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560768595998757744862359 2341152893998136617293539)
            ·
              refine ⟨3511729340997204925940309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341152893998136617293539 3511729340997204925940309)
              ·
                refine ⟨41153078214810995225863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3511729340997204925940309 41153078214810995225863)
                ·
                  rfl

theorem cell23_2163924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 8].length) (baseStart_2163924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163924 prefixEnd_2163924 := by exact prefixLift 2163924
  have htrace : WordTrace (prefixWord ++ tailWord_2163924) baseStart_2163924 baseEnd_2163924 := by
    simpa [prefixWord, tailWord_2163924, baseEnd_2163924] using wordTrace_append hprefix tailTrace_2163924
  have hstable : (prefixWord ++ tailWord_2163924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163924).length < 2 ^ (prefixWord ++ tailWord_2163924).sum := by decide
  have hdescent : baseEnd_2163924 < baseStart_2163924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163953 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2163953 : Nat := 118140960795 + 2163953 * 2 ^ 59
def prefixEnd_2163953 : Nat := 4983230072969 + 3 ^ 40 * 2163953 * 2
def baseEnd_2163953 : Nat := 1111148002738877257635667

theorem tailTrace_2163953 : CollatzResearch.WordTrace tailWord_2163953 prefixEnd_2163953 1111148002738877257635667 := by
  unfold tailWord_2163953
  simp only [CollatzResearch.WordTrace]
  refine ⟨78925849929375329594240513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52617233286250219729493675 78925849929375329594240513)
  ·
    refine ⟨59194387447031497195680385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78925849929375329594240513 59194387447031497195680385)
    ·
      refine ⟨44395790585273622896760289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59194387447031497195680385 44395790585273622896760289)
      ·
        refine ⟨33296842938955217172570217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44395790585273622896760289 33296842938955217172570217)
        ·
          refine ⟨24972632204216412879427663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33296842938955217172570217 24972632204216412879427663)
          ·
            refine ⟨37458948306324619319141495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24972632204216412879427663 37458948306324619319141495)
            ·
              refine ⟨56188422459486928978712243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37458948306324619319141495 56188422459486928978712243)
              ·
                refine ⟨84282633689230393468068365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56188422459486928978712243 84282633689230393468068365)
                ·
                  refine ⟨31605987633461397550525637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84282633689230393468068365 31605987633461397550525637)
                  ·
                    refine ⟨5926122681274012040723557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31605987633461397550525637 5926122681274012040723557)
                    ·
                      refine ⟨1111148002738877257635667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5926122681274012040723557 1111148002738877257635667)
                      ·
                        rfl

theorem cell23_2163953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2163953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163953 prefixEnd_2163953 := by exact prefixLift 2163953
  have htrace : WordTrace (prefixWord ++ tailWord_2163953) baseStart_2163953 baseEnd_2163953 := by
    simpa [prefixWord, tailWord_2163953, baseEnd_2163953] using wordTrace_append hprefix tailTrace_2163953
  have hstable : (prefixWord ++ tailWord_2163953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163953).length < 2 ^ (prefixWord ++ tailWord_2163953).sum := by decide
  have hdescent : baseEnd_2163953 < baseStart_2163953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163980 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 7]
def baseStart_2163980 : Nat := 118140960795 + 2163980 * 2 ^ 59
def prefixEnd_2163980 : Nat := 4983230072969 + 3 ^ 40 * 2163980 * 2
def baseEnd_2163980 : Nat := 123462429635172072444227

theorem tailTrace_2163980 : CollatzResearch.WordTrace tailWord_2163980 prefixEnd_2163980 123462429635172072444227 := by
  unfold tailWord_2163980
  simp only [CollatzResearch.WordTrace]
  refine ⟨39463417350138756602736697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52617889800185008803648929 39463417350138756602736697)
  ·
    refine ⟨29597563012604067452052523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39463417350138756602736697 29597563012604067452052523)
    ·
      refine ⟨44396344518906101178078785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29597563012604067452052523 44396344518906101178078785)
      ·
        refine ⟨33297258389179575883559089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44396344518906101178078785 33297258389179575883559089)
        ·
          refine ⟨24972943791884681912669317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33297258389179575883559089 24972943791884681912669317)
          ·
            refine ⟨4682426960978377858625497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24972943791884681912669317 4682426960978377858625497)
            ·
              refine ⟨3511820220733783393969123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4682426960978377858625497 3511820220733783393969123)
              ·
                refine ⟨5267730331100675090953685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511820220733783393969123 5267730331100675090953685)
                ·
                  refine ⟨123462429635172072444227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5267730331100675090953685 123462429635172072444227)
                  ·
                    rfl

theorem cell23_2163980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_2163980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163980 prefixEnd_2163980 := by exact prefixLift 2163980
  have htrace : WordTrace (prefixWord ++ tailWord_2163980) baseStart_2163980 baseEnd_2163980 := by
    simpa [prefixWord, tailWord_2163980, baseEnd_2163980] using wordTrace_append hprefix tailTrace_2163980
  have hstable : (prefixWord ++ tailWord_2163980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163980).length < 2 ^ (prefixWord ++ tailWord_2163980).sum := by decide
  have hdescent : baseEnd_2163980 < baseStart_2163980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163991 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 2, 2, 2]
def baseStart_2163991 : Nat := 118140960795 + 2163991 * 2 ^ 59
def prefixEnd_2163991 : Nat := 4983230072969 + 3 ^ 40 * 2163991 * 2
def baseEnd_2163991 : Nat := 1111167515003748108960493

theorem tailTrace_2163991 : CollatzResearch.WordTrace tailWord_2163991 prefixEnd_2163991 1111167515003748108960493 := by
  unfold tailWord_2163991
  simp only [CollatzResearch.WordTrace]
  refine ⟨78927235903237662084123827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52618157268825108056082551 78927235903237662084123827)
  ·
    refine ⟨118390853854856493126185741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78927235903237662084123827 118390853854856493126185741)
    ·
      refine ⟨44396570195571184922319653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118390853854856493126185741 44396570195571184922319653)
      ·
        refine ⟨8324356911669597172934935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44396570195571184922319653 8324356911669597172934935)
        ·
          refine ⟨12486535367504395759402403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8324356911669597172934935 12486535367504395759402403)
          ·
            refine ⟨18729803051256593639103605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12486535367504395759402403 18729803051256593639103605)
            ·
              refine ⟨1755919036055305653665963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18729803051256593639103605 1755919036055305653665963)
              ·
                refine ⟨2633878554082958480498945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755919036055305653665963 2633878554082958480498945)
                ·
                  refine ⟨1975408915562218860374209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633878554082958480498945 1975408915562218860374209)
                  ·
                    refine ⟨1481556686671664145280657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1975408915562218860374209 1481556686671664145280657)
                    ·
                      refine ⟨1111167515003748108960493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481556686671664145280657 1111167515003748108960493)
                      ·
                        rfl

theorem cell23_2163991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_2163991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2163991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2163991 prefixEnd_2163991 := by exact prefixLift 2163991
  have htrace : WordTrace (prefixWord ++ tailWord_2163991) baseStart_2163991 baseEnd_2163991 := by
    simpa [prefixWord, tailWord_2163991, baseEnd_2163991] using wordTrace_append hprefix tailTrace_2163991
  have hstable : (prefixWord ++ tailWord_2163991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163991).length < 2 ^ (prefixWord ++ tailWord_2163991).sum := by decide
  have hdescent : baseEnd_2163991 < baseStart_2163991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164043 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_2164043 : Nat := 118140960795 + 2164043 * 2 ^ 59
def prefixEnd_2164043 : Nat := 4983230072969 + 3 ^ 40 * 2164043 * 2
def baseEnd_2164043 : Nat := 1111194215997781905510253

theorem tailTrace_2164043 : CollatzResearch.WordTrace tailWord_2164043 prefixEnd_2164043 1111194215997781905510253 := by
  unfold tailWord_2164043
  simp only [CollatzResearch.WordTrace]
  refine ⟨78929132499049274965016783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52619421666032849976677855 78929132499049274965016783)
  ·
    refine ⟨118393698748573912447525175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78929132499049274965016783 118393698748573912447525175)
    ·
      refine ⟨177590548122860868671287763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118393698748573912447525175 177590548122860868671287763)
      ·
        refine ⟨266385822184291303006931645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177590548122860868671287763 266385822184291303006931645)
        ·
          refine ⟨99894683319109238627599367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266385822184291303006931645 99894683319109238627599367)
          ·
            refine ⟨149842024978663857941399051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99894683319109238627599367 149842024978663857941399051)
            ·
              refine ⟨224763037467995786912098577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149842024978663857941399051 224763037467995786912098577)
              ·
                refine ⟨168572278100996840184073933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224763037467995786912098577 168572278100996840184073933)
                ·
                  refine ⟨63214604287873815069027725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168572278100996840184073933 63214604287873815069027725)
                  ·
                    refine ⟨23705476607952680650885397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63214604287873815069027725 23705476607952680650885397)
                    ·
                      refine ⟨1111194215997781905510253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23705476607952680650885397 1111194215997781905510253)
                      ·
                        rfl

theorem cell23_2164043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_2164043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164043 prefixEnd_2164043 := by exact prefixLift 2164043
  have htrace : WordTrace (prefixWord ++ tailWord_2164043) baseStart_2164043 baseEnd_2164043 := by
    simpa [prefixWord, tailWord_2164043, baseEnd_2164043] using wordTrace_append hprefix tailTrace_2164043
  have hstable : (prefixWord ++ tailWord_2164043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164043).length < 2 ^ (prefixWord ++ tailWord_2164043).sum := by decide
  have hdescent : baseEnd_2164043 < baseStart_2164043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164067 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2164067 : Nat := 118140960795 + 2164067 * 2 ^ 59
def prefixEnd_2164067 : Nat := 4983230072969 + 3 ^ 40 * 2164067 * 2
def baseEnd_2164067 : Nat := 1111206539533489811610143

theorem tailTrace_2164067 : CollatzResearch.WordTrace tailWord_2164067 prefixEnd_2164067 1111206539533489811610143 := by
  unfold tailWord_2164067
  simp only [CollatzResearch.WordTrace]
  refine ⟨78930007850962327063890455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52620005233974884709260303 78930007850962327063890455)
  ·
    refine ⟨118395011776443490595835683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78930007850962327063890455 118395011776443490595835683)
    ·
      refine ⟨177592517664665235893753525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118395011776443490595835683 177592517664665235893753525)
      ·
        refine ⟨16649298531062365865039393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177592517664665235893753525 16649298531062365865039393)
        ·
          refine ⟨12486973898296774398779545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16649298531062365865039393 12486973898296774398779545)
          ·
            refine ⟨9365230423722580799084659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12486973898296774398779545 9365230423722580799084659)
            ·
              refine ⟨14047845635583871198626989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9365230423722580799084659 14047845635583871198626989)
              ·
                refine ⟨5267942113343951699485121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14047845635583871198626989 5267942113343951699485121)
                ·
                  refine ⟨3950956585007963774613841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267942113343951699485121 3950956585007963774613841)
                  ·
                    refine ⟨2963217438755972830960381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950956585007963774613841 2963217438755972830960381)
                    ·
                      refine ⟨1111206539533489811610143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2963217438755972830960381 1111206539533489811610143)
                      ·
                        rfl

theorem cell23_2164067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2164067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164067 prefixEnd_2164067 := by exact prefixLift 2164067
  have htrace : WordTrace (prefixWord ++ tailWord_2164067) baseStart_2164067 baseEnd_2164067 := by
    simpa [prefixWord, tailWord_2164067, baseEnd_2164067] using wordTrace_append hprefix tailTrace_2164067
  have hstable : (prefixWord ++ tailWord_2164067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164067).length < 2 ^ (prefixWord ++ tailWord_2164067).sum := by decide
  have hdescent : baseEnd_2164067 < baseStart_2164067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164107 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 1, 5, 2]
def baseStart_2164107 : Nat := 118140960795 + 2164107 * 2 ^ 59
def prefixEnd_2164107 : Nat := 4983230072969 + 3 ^ 40 * 2164107 * 2
def baseEnd_2164107 : Nat := 1111227078759669655109959

theorem tailTrace_2164107 : CollatzResearch.WordTrace tailWord_2164107 prefixEnd_2164107 1111227078759669655109959 := by
  unfold tailWord_2164107
  simp only [CollatzResearch.WordTrace]
  refine ⟨78931466770817413895346575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52620977847211609263564383 78931466770817413895346575)
  ·
    refine ⟨118397200156226120843019863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78931466770817413895346575 118397200156226120843019863)
    ·
      refine ⟨177595800234339181264529795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118397200156226120843019863 177595800234339181264529795)
      ·
        refine ⟨266393700351508771896794693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177595800234339181264529795 266393700351508771896794693)
        ·
          refine ⟨49948818815907894730649005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266393700351508771896794693 49948818815907894730649005)
          ·
            refine ⟨18730807055965460523993377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49948818815907894730649005 18730807055965460523993377)
            ·
              refine ⟨14048105291974095392995033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18730807055965460523993377 14048105291974095392995033)
              ·
                refine ⟨10536078968980571544746275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14048105291974095392995033 10536078968980571544746275)
                ·
                  refine ⟨15804118453470857317119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10536078968980571544746275 15804118453470857317119413)
                  ·
                    refine ⟨1481636105012892873479945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15804118453470857317119413 1481636105012892873479945)
                    ·
                      refine ⟨1111227078759669655109959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481636105012892873479945 1111227078759669655109959)
                      ·
                        rfl

theorem cell23_2164107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5, 2].length) (baseStart_2164107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164107 prefixEnd_2164107 := by exact prefixLift 2164107
  have htrace : WordTrace (prefixWord ++ tailWord_2164107) baseStart_2164107 baseEnd_2164107 := by
    simpa [prefixWord, tailWord_2164107, baseEnd_2164107] using wordTrace_append hprefix tailTrace_2164107
  have hstable : (prefixWord ++ tailWord_2164107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164107).length < 2 ^ (prefixWord ++ tailWord_2164107).sum := by decide
  have hdescent : baseEnd_2164107 < baseStart_2164107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164131 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 1, 1, 3]
def baseStart_2164131 : Nat := 118140960795 + 2164131 * 2 ^ 59
def prefixEnd_2164131 : Nat := 4983230072969 + 3 ^ 40 * 2164131 * 2
def baseEnd_2164131 : Nat := 1111239402295377561209849

theorem tailTrace_2164131 : CollatzResearch.WordTrace tailWord_2164131 prefixEnd_2164131 1111239402295377561209849 := by
  unfold tailWord_2164131
  simp only [CollatzResearch.WordTrace]
  refine ⟨78932342122730465994220247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52621561415153643996146831 78932342122730465994220247)
  ·
    refine ⟨118398513184095698991330371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78932342122730465994220247 118398513184095698991330371)
    ·
      refine ⟨177597769776143548486995557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118398513184095698991330371 177597769776143548486995557)
      ·
        refine ⟨33299581833026915341311667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177597769776143548486995557 33299581833026915341311667)
        ·
          refine ⟨49949372749540373011967501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33299581833026915341311667 49949372749540373011967501)
          ·
            refine ⟨18731014781077639879487813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49949372749540373011967501 18731014781077639879487813)
            ·
              refine ⟨3512065271452057477403965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18731014781077639879487813 3512065271452057477403965)
              ·
                refine ⟨1317024476794521554026487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3512065271452057477403965 1317024476794521554026487)
                ·
                  refine ⟨1975536715191782331039731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317024476794521554026487 1975536715191782331039731)
                  ·
                    refine ⟨2963305072787673496559597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1975536715191782331039731 2963305072787673496559597)
                    ·
                      refine ⟨1111239402295377561209849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2963305072787673496559597 1111239402295377561209849)
                      ·
                        rfl

theorem cell23_2164131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_2164131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164131 prefixEnd_2164131 := by exact prefixLift 2164131
  have htrace : WordTrace (prefixWord ++ tailWord_2164131) baseStart_2164131 baseEnd_2164131 := by
    simpa [prefixWord, tailWord_2164131, baseEnd_2164131] using wordTrace_append hprefix tailTrace_2164131
  have hstable : (prefixWord ++ tailWord_2164131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164131).length < 2 ^ (prefixWord ++ tailWord_2164131).sum := by decide
  have hdescent : baseEnd_2164131 < baseStart_2164131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164157 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2164157 : Nat := 118140960795 + 2164157 * 2 ^ 59
def prefixEnd_2164157 : Nat := 4983230072969 + 3 ^ 40 * 2164157 * 2
def baseEnd_2164157 : Nat := 1111252752792394459484729

theorem tailTrace_2164157 : CollatzResearch.WordTrace tailWord_2164157 prefixEnd_2164157 1111252752792394459484729 := by
  unfold tailWord_2164157
  simp only [CollatzResearch.WordTrace]
  refine ⟨78933290420636272434666725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52622193613757514956444483 78933290420636272434666725)
  ·
    refine ⟨14799991953869301081500011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78933290420636272434666725 14799991953869301081500011)
    ·
      refine ⟨22199987930803951622250017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14799991953869301081500011 22199987930803951622250017)
      ·
        refine ⟨16649990948102963716687513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22199987930803951622250017 16649990948102963716687513)
        ·
          refine ⟨12487493211077222787515635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16649990948102963716687513 12487493211077222787515635)
          ·
            refine ⟨18731239816615834181273453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12487493211077222787515635 18731239816615834181273453)
            ·
              refine ⟨7024214931230937817977545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18731239816615834181273453 7024214931230937817977545)
              ·
                refine ⟨5268161198423203363483159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7024214931230937817977545 5268161198423203363483159)
                ·
                  refine ⟨7902241797634805045224739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268161198423203363483159 7902241797634805045224739)
                  ·
                    refine ⟨11853362696452207567837109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7902241797634805045224739 11853362696452207567837109)
                    ·
                      refine ⟨1111252752792394459484729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11853362696452207567837109 1111252752792394459484729)
                      ·
                        rfl

theorem cell23_2164157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2164157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164157 prefixEnd_2164157 := by exact prefixLift 2164157
  have htrace : WordTrace (prefixWord ++ tailWord_2164157) baseStart_2164157 baseEnd_2164157 := by
    simpa [prefixWord, tailWord_2164157, baseEnd_2164157] using wordTrace_append hprefix tailTrace_2164157
  have hstable : (prefixWord ++ tailWord_2164157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164157).length < 2 ^ (prefixWord ++ tailWord_2164157).sum := by decide
  have hdescent : baseEnd_2164157 < baseStart_2164157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164164 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_2164164 : Nat := 118140960795 + 2164164 * 2 ^ 59
def prefixEnd_2164164 : Nat := 4983230072969 + 3 ^ 40 * 2164164 * 2
def baseEnd_2164164 : Nat := 370418782385658644032399

theorem tailTrace_2164164 : CollatzResearch.WordTrace tailWord_2164164 prefixEnd_2164164 370418782385658644032399 := by
  unfold tailWord_2164164
  simp only [CollatzResearch.WordTrace]
  refine ⟨39466772865805456315085773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52622363821073941753447697 39466772865805456315085773)
  ·
    refine ⟨14800039824677046118157165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39466772865805456315085773 14800039824677046118157165)
    ·
      refine ⟨5550014934253892294308937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14800039824677046118157165 5550014934253892294308937)
      ·
        refine ⟨4162511200690419220731703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5550014934253892294308937 4162511200690419220731703)
        ·
          refine ⟨6243766801035628831097555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4162511200690419220731703 6243766801035628831097555)
          ·
            refine ⟨9365650201553443246646333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243766801035628831097555 9365650201553443246646333)
            ·
              refine ⟨3512118825582541217492375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9365650201553443246646333 3512118825582541217492375)
              ·
                refine ⟨5268178238373811826238563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512118825582541217492375 5268178238373811826238563)
                ·
                  refine ⟨7902267357560717739357845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268178238373811826238563 7902267357560717739357845)
                  ·
                    refine ⟨370418782385658644032399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7902267357560717739357845 370418782385658644032399)
                    ·
                      rfl

theorem cell23_2164164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_2164164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164164 prefixEnd_2164164 := by exact prefixLift 2164164
  have htrace : WordTrace (prefixWord ++ tailWord_2164164) baseStart_2164164 baseEnd_2164164 := by
    simpa [prefixWord, tailWord_2164164, baseEnd_2164164] using wordTrace_append hprefix tailTrace_2164164
  have hstable : (prefixWord ++ tailWord_2164164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164164).length < 2 ^ (prefixWord ++ tailWord_2164164).sum := by decide
  have hdescent : baseEnd_2164164 < baseStart_2164164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164174 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_2164174 : Nat := 118140960795 + 2164174 * 2 ^ 59
def prefixEnd_2164174 : Nat := 4983230072969 + 3 ^ 40 * 2164174 * 2
def baseEnd_2164174 : Nat := 1111261481963520892972151

theorem tailTrace_2164174 : CollatzResearch.WordTrace tailWord_2164174 prefixEnd_2164174 1111261481963520892972151 := by
  unfold tailWord_2164174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9866738807696835542254447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52622606974383122892023717 9866738807696835542254447)
  ·
    refine ⟨14800108211545253313381671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9866738807696835542254447 14800108211545253313381671)
    ·
      refine ⟨22200162317317879970072507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14800108211545253313381671 22200162317317879970072507)
      ·
        refine ⟨33300243475976819955108761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22200162317317879970072507 33300243475976819955108761)
        ·
          refine ⟨24975182606982614966331571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33300243475976819955108761 24975182606982614966331571)
          ·
            refine ⟨37462773910473922449497357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24975182606982614966331571 37462773910473922449497357)
            ·
              refine ⟨14048540216427720918561509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37462773910473922449497357 14048540216427720918561509)
              ·
                refine ⟨2634101290580197672230283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14048540216427720918561509 2634101290580197672230283)
                ·
                  refine ⟨3951151935870296508345425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634101290580197672230283 3951151935870296508345425)
                  ·
                    refine ⟨2963363951902722381259069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3951151935870296508345425 2963363951902722381259069)
                    ·
                      refine ⟨1111261481963520892972151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2963363951902722381259069 1111261481963520892972151)
                      ·
                        rfl

theorem cell23_2164174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_2164174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164174 prefixEnd_2164174 := by exact prefixLift 2164174
  have htrace : WordTrace (prefixWord ++ tailWord_2164174) baseStart_2164174 baseEnd_2164174 := by
    simpa [prefixWord, tailWord_2164174, baseEnd_2164174] using wordTrace_append hprefix tailTrace_2164174
  have hstable : (prefixWord ++ tailWord_2164174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164174).length < 2 ^ (prefixWord ++ tailWord_2164174).sum := by decide
  have hdescent : baseEnd_2164174 < baseStart_2164174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164205 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2164205 : Nat := 118140960795 + 2164205 * 2 ^ 59
def prefixEnd_2164205 : Nat := 4983230072969 + 3 ^ 40 * 2164205 * 2
def baseEnd_2164205 : Nat := 1111277399863810271684509

theorem tailTrace_2164205 : CollatzResearch.WordTrace tailWord_2164205 prefixEnd_2164205 1111277399863810271684509 := by
  unfold tailWord_2164205
  simp only [CollatzResearch.WordTrace]
  refine ⟨78935041124462376632414069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52623360749641584421609379 78935041124462376632414069)
  ·
    refine ⟨7400160105418347809288819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78935041124462376632414069 7400160105418347809288819)
    ·
      refine ⟨11100240158127521713933229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7400160105418347809288819 11100240158127521713933229)
      ·
        refine ⟨4162590059297820642724961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11100240158127521713933229 4162590059297820642724961)
        ·
          refine ⟨3121942544473365482043721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4162590059297820642724961 3121942544473365482043721)
          ·
            refine ⟨2341456908355024111532791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121942544473365482043721 2341456908355024111532791)
            ·
              refine ⟨3512185362532536167299187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341456908355024111532791 3512185362532536167299187)
              ·
                refine ⟨5268278043798804250948781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512185362532536167299187 5268278043798804250948781)
                ·
                  refine ⟨1975604266424551594105793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5268278043798804250948781 1975604266424551594105793)
                  ·
                    refine ⟨1481703199818413695579345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1975604266424551594105793 1481703199818413695579345)
                    ·
                      refine ⟨1111277399863810271684509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1481703199818413695579345 1111277399863810271684509)
                      ·
                        rfl

theorem cell23_2164205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2164205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164205 prefixEnd_2164205 := by exact prefixLift 2164205
  have htrace : WordTrace (prefixWord ++ tailWord_2164205) baseStart_2164205 baseEnd_2164205 := by
    simpa [prefixWord, tailWord_2164205, baseEnd_2164205] using wordTrace_append hprefix tailTrace_2164205
  have hstable : (prefixWord ++ tailWord_2164205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164205).length < 2 ^ (prefixWord ++ tailWord_2164205).sum := by decide
  have hdescent : baseEnd_2164205 < baseStart_2164205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164221 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_2164221 : Nat := 118140960795 + 2164221 * 2 ^ 59
def prefixEnd_2164221 : Nat := 4983230072969 + 3 ^ 40 * 2164221 * 2
def baseEnd_2164221 : Nat := 1111285615554282209084435

theorem tailTrace_2164221 : CollatzResearch.WordTrace tailWord_2164221 prefixEnd_2164221 1111285615554282209084435 := by
  unfold tailWord_2164221
  simp only [CollatzResearch.WordTrace]
  refine ⟨78935624692404411364996517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52623749794936274243331011 78935624692404411364996517)
  ·
    refine ⟨14800429629825827130936847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78935624692404411364996517 14800429629825827130936847)
    ·
      refine ⟨22200644444738740696405271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14800429629825827130936847 22200644444738740696405271)
      ·
        refine ⟨33300966667108111044607907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22200644444738740696405271 33300966667108111044607907)
        ·
          refine ⟨49951450000662166566911861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33300966667108111044607907 49951450000662166566911861)
          ·
            refine ⟨4682948437562078115647987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49951450000662166566911861 4682948437562078115647987)
            ·
              refine ⟨7024422656343117173471981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682948437562078115647987 7024422656343117173471981)
              ·
                refine ⟨2634158496128668940051993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7024422656343117173471981 2634158496128668940051993)
                ·
                  refine ⟨1975618872096501705038995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2634158496128668940051993 1975618872096501705038995)
                  ·
                    refine ⟨2963428308144752557558493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1975618872096501705038995 2963428308144752557558493)
                    ·
                      refine ⟨1111285615554282209084435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2963428308144752557558493 1111285615554282209084435)
                      ·
                        rfl

theorem cell23_2164221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_2164221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2164221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2164221 prefixEnd_2164221 := by exact prefixLift 2164221
  have htrace : WordTrace (prefixWord ++ tailWord_2164221) baseStart_2164221 baseEnd_2164221 := by
    simpa [prefixWord, tailWord_2164221, baseEnd_2164221] using wordTrace_append hprefix tailTrace_2164221
  have hstable : (prefixWord ++ tailWord_2164221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164221).length < 2 ^ (prefixWord ++ tailWord_2164221).sum := by decide
  have hdescent : baseEnd_2164221 < baseStart_2164221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
