import V185TrunkScan20Chunk081

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_498919 : List Nat := [1, 1, 5, 3, 3, 1, 6]
def baseStart_498919 : Nat := 118140960795 + 498919 * 2 ^ 59
def prefixEnd_498919 : Nat := 4983230072969 + 3 ^ 40 * 498919 * 2
def baseEnd_498919 : Nat := 25302247373890243043755

theorem tailTrace_498919 : CollatzResearch.WordTrace tailWord_498919 prefixEnd_498919 25302247373890243043755 := by
  unfold tailWord_498919
  simp only [CollatzResearch.WordTrace]
  refine ⟨18197070879509146426507811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12131380586339430951005207 18197070879509146426507811)
  ·
    refine ⟨27295606319263719639761717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18197070879509146426507811 27295606319263719639761717)
    ·
      refine ⟨2558963092430973716227661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27295606319263719639761717 2558963092430973716227661)
      ·
        refine ⟨959611159661615143585373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2558963092430973716227661 959611159661615143585373)
        ·
          refine ⟨359854184873105678844515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 959611159661615143585373 359854184873105678844515)
          ·
            refine ⟨539781277309658518266773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359854184873105678844515 539781277309658518266773)
            ·
              refine ⟨25302247373890243043755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 539781277309658518266773 25302247373890243043755)
              ·
                rfl

theorem cell20_498919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 6].length) (baseStart_498919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498919 prefixEnd_498919 := by exact prefixLift 498919
  have htrace : WordTrace (prefixWord ++ tailWord_498919) baseStart_498919 baseEnd_498919 := by
    simpa [prefixWord, tailWord_498919, baseEnd_498919] using wordTrace_append hprefix tailTrace_498919
  have hstable : (prefixWord ++ tailWord_498919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498919).length < 2 ^ (prefixWord ++ tailWord_498919).sum := by decide
  have hdescent : baseEnd_498919 < baseStart_498919 := by decide
  rcases family_descends (prefixWord ++ tailWord_498919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498923 : List Nat := [1, 1, 1, 1, 2, 8, 6]
def baseStart_498923 : Nat := 118140960795 + 498923 * 2 ^ 59
def prefixEnd_498923 : Nat := 4983230072969 + 3 ^ 40 * 498923 * 2
def baseEnd_498923 : Nat := 25302450230445105695605

theorem tailTrace_498923 : CollatzResearch.WordTrace tailWord_498923 prefixEnd_498923 25302450230445105695605 := by
  unfold tailWord_498923
  simp only [CollatzResearch.WordTrace]
  refine ⟨18197216771494655109653423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12131477847663103406435615 18197216771494655109653423)
  ·
    refine ⟨27295825157241982664480135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18197216771494655109653423 27295825157241982664480135)
    ·
      refine ⟨40943737735862973996720203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27295825157241982664480135 40943737735862973996720203)
      ·
        refine ⟨61415606603794460995080305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40943737735862973996720203 61415606603794460995080305)
        ·
          refine ⟨46061704952845845746310229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61415606603794460995080305 46061704952845845746310229)
          ·
            refine ⟨539785604916162254839573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 46061704952845845746310229 539785604916162254839573)
            ·
              refine ⟨25302450230445105695605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 539785604916162254839573 25302450230445105695605)
              ·
                rfl

theorem cell20_498923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_498923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498923 prefixEnd_498923 := by exact prefixLift 498923
  have htrace : WordTrace (prefixWord ++ tailWord_498923) baseStart_498923 baseEnd_498923 := by
    simpa [prefixWord, tailWord_498923, baseEnd_498923] using wordTrace_append hprefix tailTrace_498923
  have hstable : (prefixWord ++ tailWord_498923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498923).length < 2 ^ (prefixWord ++ tailWord_498923).sum := by decide
  have hdescent : baseEnd_498923 < baseStart_498923 := by decide
  rcases family_descends (prefixWord ++ tailWord_498923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498940 : List Nat := [2, 2, 2, 1, 5, 1, 2, 5]
def baseStart_498940 : Nat := 118140960795 + 498940 * 2 ^ 59
def prefixEnd_498940 : Nat := 4983230072969 + 3 ^ 40 * 498940 * 2
def baseEnd_498940 : Nat := 75909937112409815897903

theorem tailTrace_498940 : CollatzResearch.WordTrace tailWord_498940 prefixEnd_498940 75909937112409815897903 := by
  unfold tailWord_498940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098918406216533506511137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12131891208288711342014849 9098918406216533506511137)
  ·
    refine ⟨6824188804662400129883353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9098918406216533506511137 6824188804662400129883353)
    ·
      refine ⟨5118141603496800097412515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6824188804662400129883353 5118141603496800097412515)
      ·
        refine ⟨7677212405245200146118773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118141603496800097412515 7677212405245200146118773)
        ·
          refine ⟨719738662991737513698635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7677212405245200146118773 719738662991737513698635)
          ·
            refine ⟨1079607994487606270547953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719738662991737513698635 1079607994487606270547953)
            ·
              refine ⟨809705995865704702910965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079607994487606270547953 809705995865704702910965)
              ·
                refine ⟨75909937112409815897903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809705995865704702910965 75909937112409815897903)
                ·
                  rfl

theorem cell20_498940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_498940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498940 prefixEnd_498940 := by exact prefixLift 498940
  have htrace : WordTrace (prefixWord ++ tailWord_498940) baseStart_498940 baseEnd_498940 := by
    simpa [prefixWord, tailWord_498940, baseEnd_498940] using wordTrace_append hprefix tailTrace_498940
  have hstable : (prefixWord ++ tailWord_498940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498940).length < 2 ^ (prefixWord ++ tailWord_498940).sum := by decide
  have hdescent : baseEnd_498940 < baseStart_498940 := by decide
  rcases family_descends (prefixWord ++ tailWord_498940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498947 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_498947 : Nat := 118140960795 + 498947 * 2 ^ 59
def prefixEnd_498947 : Nat := 4983230072969 + 3 ^ 40 * 498947 * 2
def baseEnd_498947 : Nat := 227733006327968534460347

theorem tailTrace_498947 : CollatzResearch.WordTrace tailWord_498947 prefixEnd_498947 227733006327968534460347 := by
  unfold tailWord_498947
  simp only [CollatzResearch.WordTrace]
  refine ⟨18198092123407707208527095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12132061415605138139018063 18198092123407707208527095)
  ·
    refine ⟨27297138185111560812790643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18198092123407707208527095 27297138185111560812790643)
    ·
      refine ⟨40945707277667341219185965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27297138185111560812790643 40945707277667341219185965)
      ·
        refine ⟨15354640229125252957194737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40945707277667341219185965 15354640229125252957194737)
        ·
          refine ⟨11515980171843939717896053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15354640229125252957194737 11515980171843939717896053)
          ·
            refine ⟨1079623141110369348552755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11515980171843939717896053 1079623141110369348552755)
            ·
              refine ⟨1619434711665554022829133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079623141110369348552755 1619434711665554022829133)
              ·
                refine ⟨607288016874582758560925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1619434711665554022829133 607288016874582758560925)
                ·
                  refine ⟨227733006327968534460347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607288016874582758560925 227733006327968534460347)
                  ·
                    rfl

theorem cell20_498947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_498947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498947 prefixEnd_498947 := by exact prefixLift 498947
  have htrace : WordTrace (prefixWord ++ tailWord_498947) baseStart_498947 baseEnd_498947 := by
    simpa [prefixWord, tailWord_498947, baseEnd_498947] using wordTrace_append hprefix tailTrace_498947
  have hstable : (prefixWord ++ tailWord_498947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498947).length < 2 ^ (prefixWord ++ tailWord_498947).sum := by decide
  have hdescent : baseEnd_498947 < baseStart_498947 := by decide
  rcases family_descends (prefixWord ++ tailWord_498947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498978 : List Nat := [3, 3, 1, 1, 5, 7]
def baseStart_498978 : Nat := 118140960795 + 498978 * 2 ^ 59
def prefixEnd_498978 : Nat := 4983230072969 + 3 ^ 40 * 498978 * 2
def baseEnd_498978 : Nat := 8435079836024822386181

theorem tailTrace_498978 : CollatzResearch.WordTrace tailWord_498978 prefixEnd_498978 8435079836024822386181 := by
  unfold tailWord_498978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549805696573849875726397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12132815190863599668603725 4549805696573849875726397)
  ·
    refine ⟨1706177136215193703397399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4549805696573849875726397 1706177136215193703397399)
    ·
      refine ⟨2559265704322790555096099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706177136215193703397399 2559265704322790555096099)
      ·
        refine ⟨3838898556484185832644149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559265704322790555096099 3838898556484185832644149)
        ·
          refine ⟨359896739670392421810389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3838898556484185832644149 359896739670392421810389)
          ·
            refine ⟨8435079836024822386181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 359896739670392421810389 8435079836024822386181)
            ·
              rfl

theorem cell20_498978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 7].length) (baseStart_498978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498978 prefixEnd_498978 := by exact prefixLift 498978
  have htrace : WordTrace (prefixWord ++ tailWord_498978) baseStart_498978 baseEnd_498978 := by
    simpa [prefixWord, tailWord_498978, baseEnd_498978] using wordTrace_append hprefix tailTrace_498978
  have hstable : (prefixWord ++ tailWord_498978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498978).length < 2 ^ (prefixWord ++ tailWord_498978).sum := by decide
  have hdescent : baseEnd_498978 < baseStart_498978 := by decide
  rcases family_descends (prefixWord ++ tailWord_498978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499009 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_499009 : Nat := 118140960795 + 499009 * 2 ^ 59
def prefixEnd_499009 : Nat := 4983230072969 + 3 ^ 40 * 499009 * 2
def baseEnd_499009 : Nat := 227761304817371874393427

theorem tailTrace_499009 : CollatzResearch.WordTrace tailWord_499009 prefixEnd_499009 227761304817371874393427 := by
  unfold tailWord_499009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200353449183091797284081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12133568966122061198189387 18200353449183091797284081)
  ·
    refine ⟨13650265086887318847963061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18200353449183091797284081 13650265086887318847963061)
    ·
      refine ⟨1279712351895686141996537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13650265086887318847963061 1279712351895686141996537)
      ·
        refine ⟨959784263921764606497403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1279712351895686141996537 959784263921764606497403)
        ·
          refine ⟨1439676395882646909746105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959784263921764606497403 1439676395882646909746105)
          ·
            refine ⟨1079757296911985182309579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439676395882646909746105 1079757296911985182309579)
            ·
              refine ⟨1619635945367977773464369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079757296911985182309579 1619635945367977773464369)
              ·
                refine ⟨1214726959025983330098277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619635945367977773464369 1214726959025983330098277)
                ·
                  refine ⟨227761304817371874393427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1214726959025983330098277 227761304817371874393427)
                  ·
                    rfl

theorem cell20_499009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_499009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499009 prefixEnd_499009 := by exact prefixLift 499009
  have htrace : WordTrace (prefixWord ++ tailWord_499009) baseStart_499009 baseEnd_499009 := by
    simpa [prefixWord, tailWord_499009, baseEnd_499009] using wordTrace_append hprefix tailTrace_499009
  have hstable : (prefixWord ++ tailWord_499009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499009).length < 2 ^ (prefixWord ++ tailWord_499009).sum := by decide
  have hdescent : baseEnd_499009 < baseStart_499009 := by decide
  rcases family_descends (prefixWord ++ tailWord_499009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499040 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_499040 : Nat := 118140960795 + 499040 * 2 ^ 59
def prefixEnd_499040 : Nat := 4983230072969 + 3 ^ 40 * 499040 * 2
def baseEnd_499040 : Nat := 227775454062073544359967

theorem tailTrace_499040 : CollatzResearch.WordTrace tailWord_499040 prefixEnd_499040 227775454062073544359967 := by
  unfold tailWord_499040
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100742056035392045831287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12134322741380522727775049 9100742056035392045831287)
  ·
    refine ⟨13651113084053088068746931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100742056035392045831287 13651113084053088068746931)
    ·
      refine ⟨20476669626079632103120397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13651113084053088068746931 20476669626079632103120397)
      ·
        refine ⟨7678751109779862038670149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20476669626079632103120397 7678751109779862038670149)
        ·
          refine ⟨1439765833083724132250653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7678751109779862038670149 1439765833083724132250653)
          ·
            refine ⟨539912187406396549593995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1439765833083724132250653 539912187406396549593995)
            ·
              refine ⟨809868281109594824390993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539912187406396549593995 809868281109594824390993)
              ·
                refine ⟨607401210832196118293245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809868281109594824390993 607401210832196118293245)
                ·
                  refine ⟨227775454062073544359967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607401210832196118293245 227775454062073544359967)
                  ·
                    rfl

theorem cell20_499040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_499040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499040 prefixEnd_499040 := by exact prefixLift 499040
  have htrace : WordTrace (prefixWord ++ tailWord_499040) baseStart_499040 baseEnd_499040 := by
    simpa [prefixWord, tailWord_499040, baseEnd_499040] using wordTrace_append hprefix tailTrace_499040
  have hstable : (prefixWord ++ tailWord_499040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499040).length < 2 ^ (prefixWord ++ tailWord_499040).sum := by decide
  have hdescent : baseEnd_499040 < baseStart_499040 := by decide
  rcases family_descends (prefixWord ++ tailWord_499040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499047 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_499047 : Nat := 118140960795 + 499047 * 2 ^ 59
def prefixEnd_499047 : Nat := 4983230072969 + 3 ^ 40 * 499047 * 2
def baseEnd_499047 : Nat := 227778649052812631126605

theorem tailTrace_499047 : CollatzResearch.WordTrace tailWord_499047 prefixEnd_499047 227778649052812631126605 := by
  unfold tailWord_499047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18201739423045424287167395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12134492948696949524778263 18201739423045424287167395)
  ·
    refine ⟨27302609134568136430751093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18201739423045424287167395 27302609134568136430751093)
    ·
      refine ⟨2559619606365762790382915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27302609134568136430751093 2559619606365762790382915)
      ·
        refine ⟨3839429409548644185574373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559619606365762790382915 3839429409548644185574373)
        ·
          refine ⟨719893014290370784795195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3839429409548644185574373 719893014290370784795195)
          ·
            refine ⟨1079839521435556177192793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719893014290370784795195 1079839521435556177192793)
            ·
              refine ⟨809879641076667132894595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079839521435556177192793 809879641076667132894595)
              ·
                refine ⟨1214819461615000699341893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809879641076667132894595 1214819461615000699341893)
                ·
                  refine ⟨227778649052812631126605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1214819461615000699341893 227778649052812631126605)
                  ·
                    rfl

theorem cell20_499047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_499047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499047 prefixEnd_499047 := by exact prefixLift 499047
  have htrace : WordTrace (prefixWord ++ tailWord_499047) baseStart_499047 baseEnd_499047 := by
    simpa [prefixWord, tailWord_499047, baseEnd_499047] using wordTrace_append hprefix tailTrace_499047
  have hstable : (prefixWord ++ tailWord_499047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499047).length < 2 ^ (prefixWord ++ tailWord_499047).sum := by decide
  have hdescent : baseEnd_499047 < baseStart_499047 := by decide
  rcases family_descends (prefixWord ++ tailWord_499047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499075 : List Nat := [1, 1, 1, 3, 5, 2, 1, 6]
def baseStart_499075 : Nat := 118140960795 + 499075 * 2 ^ 59
def prefixEnd_499075 : Nat := 4983230072969 + 3 ^ 40 * 499075 * 2
def baseEnd_499075 : Nat := 75930476338589659397719

theorem tailTrace_499075 : CollatzResearch.WordTrace tailWord_499075 prefixEnd_499075 75930476338589659397719 := by
  unfold tailWord_499075
  simp only [CollatzResearch.WordTrace]
  refine ⟨18202760666943985069186679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12135173777962656712791119 18202760666943985069186679)
  ·
    refine ⟨27304141000415977603780019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18202760666943985069186679 27304141000415977603780019)
    ·
      refine ⟨40956211500623966405670029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27304141000415977603780019 40956211500623966405670029)
      ·
        refine ⟨15358579312733987402126261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40956211500623966405670029 15358579312733987402126261)
        ·
          refine ⟨1439866810568811318949337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15358579312733987402126261 1439866810568811318949337)
          ·
            refine ⟨1079900107926608489212003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439866810568811318949337 1079900107926608489212003)
            ·
              refine ⟨1619850161889912733818005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079900107926608489212003 1619850161889912733818005)
              ·
                refine ⟨75930476338589659397719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1619850161889912733818005 75930476338589659397719)
                ·
                  rfl

theorem cell20_499075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_499075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499075 prefixEnd_499075 := by exact prefixLift 499075
  have htrace : WordTrace (prefixWord ++ tailWord_499075) baseStart_499075 baseEnd_499075 := by
    simpa [prefixWord, tailWord_499075, baseEnd_499075] using wordTrace_append hprefix tailTrace_499075
  have hstable : (prefixWord ++ tailWord_499075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499075).length < 2 ^ (prefixWord ++ tailWord_499075).sum := by decide
  have hdescent : baseEnd_499075 < baseStart_499075 := by decide
  rcases family_descends (prefixWord ++ tailWord_499075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499081 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 2]
def baseStart_499081 : Nat := 118140960795 + 499081 * 2 ^ 59
def prefixEnd_499081 : Nat := 4983230072969 + 3 ^ 40 * 499081 * 2
def baseEnd_499081 : Nat := 227794167579259623993133

theorem tailTrace_499081 : CollatzResearch.WordTrace tailWord_499081 prefixEnd_499081 227794167579259623993133 := by
  unfold tailWord_499081
  simp only [CollatzResearch.WordTrace]
  refine ⟨18202979504922248093905097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12135319669948165395936731 18202979504922248093905097)
  ·
    refine ⟨13652234628691686070428823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18202979504922248093905097 13652234628691686070428823)
    ·
      refine ⟨20478351943037529105643235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13652234628691686070428823 20478351943037529105643235)
      ·
        refine ⟨30717527914556293658464853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20478351943037529105643235 30717527914556293658464853)
        ·
          refine ⟨359971030248706566310135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 30717527914556293658464853 359971030248706566310135)
          ·
            refine ⟨539956545373059849465203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359971030248706566310135 539956545373059849465203)
            ·
              refine ⟨809934818059589774197805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539956545373059849465203 809934818059589774197805)
              ·
                refine ⟨303725556772346165324177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809934818059589774197805 303725556772346165324177)
                ·
                  refine ⟨227794167579259623993133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303725556772346165324177 227794167579259623993133)
                  ·
                    rfl

theorem cell20_499081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_499081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499081 prefixEnd_499081 := by exact prefixLift 499081
  have htrace : WordTrace (prefixWord ++ tailWord_499081) baseStart_499081 baseEnd_499081 := by
    simpa [prefixWord, tailWord_499081, baseEnd_499081] using wordTrace_append hprefix tailTrace_499081
  have hstable : (prefixWord ++ tailWord_499081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499081).length < 2 ^ (prefixWord ++ tailWord_499081).sum := by decide
  have hdescent : baseEnd_499081 < baseStart_499081 := by decide
  rcases family_descends (prefixWord ++ tailWord_499081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499092 : List Nat := [2, 4, 2, 1, 2, 3, 6]
def baseStart_499092 : Nat := 118140960795 + 499092 * 2 ^ 59
def prefixEnd_499092 : Nat := 4983230072969 + 3 ^ 40 * 499092 * 2
def baseEnd_499092 : Nat := 25311020919888052736269

theorem tailTrace_499092 : CollatzResearch.WordTrace tailWord_499092 prefixEnd_499092 25311020919888052736269 := by
  unfold tailWord_499092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101690353941198486277765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12135587138588264648370353 9101690353941198486277765)
  ·
    refine ⟨1706566941363974716177081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9101690353941198486277765 1706566941363974716177081)
    ·
      refine ⟨1279925206022981037132811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1706566941363974716177081 1279925206022981037132811)
      ·
        refine ⟨1919887809034471555699217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279925206022981037132811 1919887809034471555699217)
        ·
          refine ⟨1439915856775853666774413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1919887809034471555699217 1439915856775853666774413)
          ·
            refine ⟨539968446290945125040405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1439915856775853666774413 539968446290945125040405)
            ·
              refine ⟨25311020919888052736269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 539968446290945125040405 25311020919888052736269)
              ·
                rfl

theorem cell20_499092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 6].length) (baseStart_499092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499092 prefixEnd_499092 := by exact prefixLift 499092
  have htrace : WordTrace (prefixWord ++ tailWord_499092) baseStart_499092 baseEnd_499092 := by
    simpa [prefixWord, tailWord_499092, baseEnd_499092] using wordTrace_append hprefix tailTrace_499092
  have hstable : (prefixWord ++ tailWord_499092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499092).length < 2 ^ (prefixWord ++ tailWord_499092).sum := by decide
  have hdescent : baseEnd_499092 < baseStart_499092 := by decide
  rcases family_descends (prefixWord ++ tailWord_499092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499112 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_499112 : Nat := 118140960795 + 499112 * 2 ^ 59
def prefixEnd_499112 : Nat := 4983230072969 + 3 ^ 40 * 499112 * 2
def baseEnd_499112 : Nat := 227808316823961293959673

theorem tailTrace_499112 : CollatzResearch.WordTrace tailWord_499112 prefixEnd_499112 227808316823961293959673 := by
  unfold tailWord_499112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102055083904970194141795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12136073445206626925522393 9102055083904970194141795)
  ·
    refine ⟨13653082625857455291212693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9102055083904970194141795 13653082625857455291212693)
    ·
      refine ⟨639988248087068216775595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13653082625857455291212693 639988248087068216775595)
      ·
        refine ⟨959982372130602325163393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639988248087068216775595 959982372130602325163393)
        ·
          refine ⟨719986779097951743872545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959982372130602325163393 719986779097951743872545)
          ·
            refine ⟨539990084323463807904409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719986779097951743872545 539990084323463807904409)
            ·
              refine ⟨404992563242597855928307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539990084323463807904409 404992563242597855928307)
              ·
                refine ⟨607488844863896783892461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404992563242597855928307 607488844863896783892461)
                ·
                  refine ⟨227808316823961293959673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607488844863896783892461 227808316823961293959673)
                  ·
                    rfl

theorem cell20_499112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_499112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499112 prefixEnd_499112 := by exact prefixLift 499112
  have htrace : WordTrace (prefixWord ++ tailWord_499112) baseStart_499112 baseEnd_499112 := by
    simpa [prefixWord, tailWord_499112, baseEnd_499112] using wordTrace_append hprefix tailTrace_499112
  have hstable : (prefixWord ++ tailWord_499112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499112).length < 2 ^ (prefixWord ++ tailWord_499112).sum := by decide
  have hdescent : baseEnd_499112 < baseStart_499112 := by decide
  rcases family_descends (prefixWord ++ tailWord_499112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499127 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_499127 : Nat := 118140960795 + 499127 * 2 ^ 59
def prefixEnd_499127 : Nat := 4983230072969 + 3 ^ 40 * 499127 * 2
def baseEnd_499127 : Nat := 227815163232687908459611

theorem tailTrace_499127 : CollatzResearch.WordTrace tailWord_499127 prefixEnd_499127 227815163232687908459611 := by
  unfold tailWord_499127
  simp only [CollatzResearch.WordTrace]
  refine ⟨18204657262755597950079635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12136438175170398633386423 18204657262755597950079635)
  ·
    refine ⟨27306985894133396925119453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18204657262755597950079635 27306985894133396925119453)
    ·
      refine ⟨10240119710300023846919795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27306985894133396925119453 10240119710300023846919795)
      ·
        refine ⟨15360179565450035770379693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240119710300023846919795 15360179565450035770379693)
        ·
          refine ⟨5760067337043763413892385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15360179565450035770379693 5760067337043763413892385)
          ·
            refine ⟨4320050502782822560419289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5760067337043763413892385 4320050502782822560419289)
            ·
              refine ⟨3240037877087116920314467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320050502782822560419289 3240037877087116920314467)
              ·
                refine ⟨4860056815630675380471701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240037877087116920314467 4860056815630675380471701)
                ·
                  refine ⟨227815163232687908459611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4860056815630675380471701 227815163232687908459611)
                  ·
                    rfl

theorem cell20_499127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_499127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499127 prefixEnd_499127 := by exact prefixLift 499127
  have htrace : WordTrace (prefixWord ++ tailWord_499127) baseStart_499127 baseEnd_499127 := by
    simpa [prefixWord, tailWord_499127, baseEnd_499127] using wordTrace_append hprefix tailTrace_499127
  have hstable : (prefixWord ++ tailWord_499127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499127).length < 2 ^ (prefixWord ++ tailWord_499127).sum := by decide
  have hdescent : baseEnd_499127 < baseStart_499127 := by decide
  rcases family_descends (prefixWord ++ tailWord_499127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499161 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 2]
def baseStart_499161 : Nat := 118140960795 + 499161 * 2 ^ 59
def prefixEnd_499161 : Nat := 4983230072969 + 3 ^ 40 * 499161 * 2
def baseEnd_499161 : Nat := 227830681759134901326139

theorem tailTrace_499161 : CollatzResearch.WordTrace tailWord_499161 prefixEnd_499161 227830681759134901326139 := by
  unfold tailWord_499161
  simp only [CollatzResearch.WordTrace]
  refine ⟨18205897344632421756817337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12137264896421614504544891 18205897344632421756817337)
  ·
    refine ⟨13654423008474316317613003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18205897344632421756817337 13654423008474316317613003)
    ·
      refine ⟨20481634512711474476419505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13654423008474316317613003 20481634512711474476419505)
      ·
        refine ⟨15361225884533605857314629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20481634512711474476419505 15361225884533605857314629)
        ·
          refine ⟨2880229853350051098246493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15361225884533605857314629 2880229853350051098246493)
          ·
            refine ⟨1080086195006269161842435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2880229853350051098246493 1080086195006269161842435)
            ·
              refine ⟨1620129292509403742763653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080086195006269161842435 1620129292509403742763653)
              ·
                refine ⟨303774242345513201768185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1620129292509403742763653 303774242345513201768185)
                ·
                  refine ⟨227830681759134901326139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303774242345513201768185 227830681759134901326139)
                  ·
                    rfl

theorem cell20_499161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_499161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499161 prefixEnd_499161 := by exact prefixLift 499161
  have htrace : WordTrace (prefixWord ++ tailWord_499161) baseStart_499161 baseEnd_499161 := by
    simpa [prefixWord, tailWord_499161, baseEnd_499161] using wordTrace_append hprefix tailTrace_499161
  have hstable : (prefixWord ++ tailWord_499161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499161).length < 2 ^ (prefixWord ++ tailWord_499161).sum := by decide
  have hdescent : baseEnd_499161 < baseStart_499161 := by decide
  rcases family_descends (prefixWord ++ tailWord_499161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499175 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_499175 : Nat := 118140960795 + 499175 * 2 ^ 59
def prefixEnd_499175 : Nat := 4983230072969 + 3 ^ 40 * 499175 * 2
def baseEnd_499175 : Nat := 227837071740613074859415

theorem tailTrace_499175 : CollatzResearch.WordTrace tailWord_499175 prefixEnd_499175 227837071740613074859415 := by
  unfold tailWord_499175
  simp only [CollatzResearch.WordTrace]
  refine ⟨18206407966581702147826979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12137605311054468098551319 18206407966581702147826979)
  ·
    refine ⟨27309611949872553221740469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18206407966581702147826979 27309611949872553221740469)
    ·
      refine ⟨2560276120300551864538169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27309611949872553221740469 2560276120300551864538169)
      ·
        refine ⟨1920207090225413898403627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2560276120300551864538169 1920207090225413898403627)
        ·
          refine ⟨2880310635338120847605441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920207090225413898403627 2880310635338120847605441)
          ·
            refine ⟨2160232976503590635704081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880310635338120847605441 2160232976503590635704081)
            ·
              refine ⟨1620174732377692976778061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2160232976503590635704081 1620174732377692976778061)
              ·
                refine ⟨607565524641634866291773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1620174732377692976778061 607565524641634866291773)
                ·
                  refine ⟨227837071740613074859415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607565524641634866291773 227837071740613074859415)
                  ·
                    rfl

theorem cell20_499175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_499175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499175 prefixEnd_499175 := by exact prefixLift 499175
  have htrace : WordTrace (prefixWord ++ tailWord_499175) baseStart_499175 baseEnd_499175 := by
    simpa [prefixWord, tailWord_499175, baseEnd_499175] using wordTrace_append hprefix tailTrace_499175
  have hstable : (prefixWord ++ tailWord_499175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499175).length < 2 ^ (prefixWord ++ tailWord_499175).sum := by decide
  have hdescent : baseEnd_499175 < baseStart_499175 := by decide
  rcases family_descends (prefixWord ++ tailWord_499175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499182 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_499182 : Nat := 118140960795 + 499182 * 2 ^ 59
def prefixEnd_499182 : Nat := 4983230072969 + 3 ^ 40 * 499182 * 2
def baseEnd_499182 : Nat := 227840266731352161626053

theorem tailTrace_499182 : CollatzResearch.WordTrace tailWord_499182 prefixEnd_499182 227840266731352161626053 := by
  unfold tailWord_499182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275832909694542792916475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12137775518370894895554533 2275832909694542792916475)
  ·
    refine ⟨3413749364541814189374713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2275832909694542792916475 3413749364541814189374713)
    ·
      refine ⟨2560312023406360642031035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3413749364541814189374713 2560312023406360642031035)
      ·
        refine ⟨3840468035109540963046553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560312023406360642031035 3840468035109540963046553)
        ·
          refine ⟨2880351026332155722284915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840468035109540963046553 2880351026332155722284915)
          ·
            refine ⟨4320526539498233583427373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880351026332155722284915 4320526539498233583427373)
            ·
              refine ⟨1620197452311837593785265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4320526539498233583427373 1620197452311837593785265)
              ·
                refine ⟨1215148089233878195338949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620197452311837593785265 1215148089233878195338949)
                ·
                  refine ⟨227840266731352161626053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215148089233878195338949 227840266731352161626053)
                  ·
                    rfl

theorem cell20_499182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_499182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499182 prefixEnd_499182 := by exact prefixLift 499182
  have htrace : WordTrace (prefixWord ++ tailWord_499182) baseStart_499182 baseEnd_499182 := by
    simpa [prefixWord, tailWord_499182, baseEnd_499182] using wordTrace_append hprefix tailTrace_499182
  have hstable : (prefixWord ++ tailWord_499182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499182).length < 2 ^ (prefixWord ++ tailWord_499182).sum := by decide
  have hdescent : baseEnd_499182 < baseStart_499182 := by decide
  rcases family_descends (prefixWord ++ tailWord_499182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499240 : List Nat := [2, 1, 5, 2, 3, 1, 2, 4]
def baseStart_499240 : Nat := 118140960795 + 499240 * 2 ^ 59
def prefixEnd_499240 : Nat := 4983230072969 + 3 ^ 40 * 499240 * 2
def baseEnd_499240 : Nat := 75955579837253912564161

theorem tailTrace_499240 : CollatzResearch.WordTrace tailWord_499240 prefixEnd_499240 75955579837253912564161 := by
  unfold tailWord_499240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9104389355673109124471587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12139185807564145499295449 9104389355673109124471587)
  ·
    refine ⟨13656584033509663686707381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9104389355673109124471587 13656584033509663686707381)
    ·
      refine ⟨1280304753141530970628817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13656584033509663686707381 1280304753141530970628817)
      ·
        refine ⟨960228564856148227971613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1280304753141530970628817 960228564856148227971613)
        ·
          refine ⟨360085711821055585489355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 960228564856148227971613 360085711821055585489355)
          ·
            refine ⟨540128567731583378234033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360085711821055585489355 540128567731583378234033)
            ·
              refine ⟨405096425798687533675525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540128567731583378234033 405096425798687533675525)
              ·
                refine ⟨75955579837253912564161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405096425798687533675525 75955579837253912564161)
                ·
                  rfl

theorem cell20_499240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_499240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499240 prefixEnd_499240 := by exact prefixLift 499240
  have htrace : WordTrace (prefixWord ++ tailWord_499240) baseStart_499240 baseEnd_499240 := by
    simpa [prefixWord, tailWord_499240, baseEnd_499240] using wordTrace_append hprefix tailTrace_499240
  have hstable : (prefixWord ++ tailWord_499240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499240).length < 2 ^ (prefixWord ++ tailWord_499240).sum := by decide
  have hdescent : baseEnd_499240 < baseStart_499240 := by decide
  rcases family_descends (prefixWord ++ tailWord_499240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499382 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_499382 : Nat := 118140960795 + 499382 * 2 ^ 59
def prefixEnd_499382 : Nat := 4983230072969 + 3 ^ 40 * 499382 * 2
def baseEnd_499382 : Nat := 227931552181040354958569

theorem tailTrace_499382 : CollatzResearch.WordTrace tailWord_499382 prefixEnd_499382 227931552181040354958569 := by
  unfold tailWord_499382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138372367301986031288275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12142638584554517667074933 1138372367301986031288275)
  ·
    refine ⟨1707558550952979046932413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1138372367301986031288275 1707558550952979046932413)
    ·
      refine ⟨640334456607367142599655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1707558550952979046932413 640334456607367142599655)
      ·
        refine ⟨960501684911050713899483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640334456607367142599655 960501684911050713899483)
        ·
          refine ⟨1440752527366576070849225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960501684911050713899483 1440752527366576070849225)
          ·
            refine ⟨1080564395524932053136919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440752527366576070849225 1080564395524932053136919)
            ·
              refine ⟨1620846593287398079705379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080564395524932053136919 1620846593287398079705379)
              ·
                refine ⟨2431269889931097119558069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620846593287398079705379 2431269889931097119558069)
                ·
                  refine ⟨227931552181040354958569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2431269889931097119558069 227931552181040354958569)
                  ·
                    rfl

theorem cell20_499382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_499382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499382 prefixEnd_499382 := by exact prefixLift 499382
  have htrace : WordTrace (prefixWord ++ tailWord_499382) baseStart_499382 baseEnd_499382 := by
    simpa [prefixWord, tailWord_499382, baseEnd_499382] using wordTrace_append hprefix tailTrace_499382
  have hstable : (prefixWord ++ tailWord_499382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499382).length < 2 ^ (prefixWord ++ tailWord_499382).sum := by decide
  have hdescent : baseEnd_499382 < baseStart_499382 := by decide
  rcases family_descends (prefixWord ++ tailWord_499382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499386 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_499386 : Nat := 118140960795 + 499386 * 2 ^ 59
def prefixEnd_499386 : Nat := 4983230072969 + 3 ^ 40 * 499386 * 2
def baseEnd_499386 : Nat := 227933377890034118825219

theorem tailTrace_499386 : CollatzResearch.WordTrace tailWord_499386 prefixEnd_499386 227933377890034118825219 := by
  unfold tailWord_499386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553525942204321295939503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12142735845878190122505341 4553525942204321295939503)
  ·
    refine ⟨6830288913306481943909255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553525942204321295939503 6830288913306481943909255)
    ·
      refine ⟨10245433369959722915863883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830288913306481943909255 10245433369959722915863883)
      ·
        refine ⟨15368150054939584373795825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245433369959722915863883 15368150054939584373795825)
        ·
          refine ⟨11526112541204688280346869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15368150054939584373795825 11526112541204688280346869)
          ·
            refine ⟨1080573050737939526282519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11526112541204688280346869 1080573050737939526282519)
            ·
              refine ⟨1620859576106909289423779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080573050737939526282519 1620859576106909289423779)
              ·
                refine ⟨2431289364160363934135669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620859576106909289423779 2431289364160363934135669)
                ·
                  refine ⟨227933377890034118825219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2431289364160363934135669 227933377890034118825219)
                  ·
                    rfl

theorem cell20_499386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_499386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499386 prefixEnd_499386 := by exact prefixLift 499386
  have htrace : WordTrace (prefixWord ++ tailWord_499386) baseStart_499386 baseEnd_499386 := by
    simpa [prefixWord, tailWord_499386, baseEnd_499386] using wordTrace_append hprefix tailTrace_499386
  have hstable : (prefixWord ++ tailWord_499386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499386).length < 2 ^ (prefixWord ++ tailWord_499386).sum := by decide
  have hdescent : baseEnd_499386 < baseStart_499386 := by decide
  rcases family_descends (prefixWord ++ tailWord_499386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499400 : List Nat := [2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_499400 : Nat := 118140960795 + 499400 * 2 ^ 59
def prefixEnd_499400 : Nat := 4983230072969 + 3 ^ 40 * 499400 * 2
def baseEnd_499400 : Nat := 75979922623837430786165

theorem tailTrace_499400 : CollatzResearch.WordTrace tailWord_499400 prefixEnd_499400 75979922623837430786165 := by
  unfold tailWord_499400
  simp only [CollatzResearch.WordTrace]
  refine ⟨9107307195383282787383827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12143076260511043716511769 9107307195383282787383827)
  ·
    refine ⟨13660960793074924181075741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9107307195383282787383827 13660960793074924181075741)
    ·
      refine ⟨5122860297403096567903403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13660960793074924181075741 5122860297403096567903403)
      ·
        refine ⟨7684290446104644851855105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122860297403096567903403 7684290446104644851855105)
        ·
          refine ⟨5763217834578483638891329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7684290446104644851855105 5763217834578483638891329)
          ·
            refine ⟨4322413375933862729168497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5763217834578483638891329 4322413375933862729168497)
            ·
              refine ⟨3241810031950397046876373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322413375933862729168497 3241810031950397046876373)
              ·
                refine ⟨75979922623837430786165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3241810031950397046876373 75979922623837430786165)
                ·
                  rfl

theorem cell20_499400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_499400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499400 prefixEnd_499400 := by exact prefixLift 499400
  have htrace : WordTrace (prefixWord ++ tailWord_499400) baseStart_499400 baseEnd_499400 := by
    simpa [prefixWord, tailWord_499400, baseEnd_499400] using wordTrace_append hprefix tailTrace_499400
  have hstable : (prefixWord ++ tailWord_499400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499400).length < 2 ^ (prefixWord ++ tailWord_499400).sum := by decide
  have hdescent : baseEnd_499400 < baseStart_499400 := by decide
  rcases family_descends (prefixWord ++ tailWord_499400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499410 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_499410 : Nat := 118140960795 + 499410 * 2 ^ 59
def prefixEnd_499410 : Nat := 4983230072969 + 3 ^ 40 * 499410 * 2
def baseEnd_499410 : Nat := 227944332143996702025121

theorem tailTrace_499410 : CollatzResearch.WordTrace tailWord_499410 prefixEnd_499410 227944332143996702025121 := by
  unfold tailWord_499410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553744780182584320657921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12143319413820224855087789 4553744780182584320657921)
  ·
    refine ⟨3415308585136938240493441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4553744780182584320657921 3415308585136938240493441)
    ·
      refine ⟨2561481438852703680370081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3415308585136938240493441 2561481438852703680370081)
      ·
        refine ⟨1921111079139527760277561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561481438852703680370081 1921111079139527760277561)
        ·
          refine ⟨1440833309354645820208171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1921111079139527760277561 1440833309354645820208171)
          ·
            refine ⟨2161249964031968730312257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440833309354645820208171 2161249964031968730312257)
            ·
              refine ⟨1620937473023976547734193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161249964031968730312257 1620937473023976547734193)
              ·
                refine ⟨1215703104767982410800645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620937473023976547734193 1215703104767982410800645)
                ·
                  refine ⟨227944332143996702025121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215703104767982410800645 227944332143996702025121)
                  ·
                    rfl

theorem cell20_499410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_499410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499410 prefixEnd_499410 := by exact prefixLift 499410
  have htrace : WordTrace (prefixWord ++ tailWord_499410) baseStart_499410 baseEnd_499410 := by
    simpa [prefixWord, tailWord_499410, baseEnd_499410] using wordTrace_append hprefix tailTrace_499410
  have hstable : (prefixWord ++ tailWord_499410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499410).length < 2 ^ (prefixWord ++ tailWord_499410).sum := by decide
  have hdescent : baseEnd_499410 < baseStart_499410 := by decide
  rcases family_descends (prefixWord ++ tailWord_499410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499417 : List Nat := [1, 2, 1, 2, 3, 3, 4, 4]
def baseStart_499417 : Nat := 118140960795 + 499417 * 2 ^ 59
def prefixEnd_499417 : Nat := 4983230072969 + 3 ^ 40 * 499417 * 2
def baseEnd_499417 : Nat := 75982509044911929597253

theorem tailTrace_499417 : CollatzResearch.WordTrace tailWord_499417 prefixEnd_499417 75982509044911929597253 := by
  unfold tailWord_499417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215234431704977478136505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12143489621136651652091003 18215234431704977478136505)
  ·
    refine ⟨13661425823778733108602379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18215234431704977478136505 13661425823778733108602379)
    ·
      refine ⟨20492138735668099662903569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13661425823778733108602379 20492138735668099662903569)
      ·
        refine ⟨15369104051751074747177677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20492138735668099662903569 15369104051751074747177677)
        ·
          refine ⟨5763414019406653030191629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15369104051751074747177677 5763414019406653030191629)
          ·
            refine ⟨2161280257277494886321861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5763414019406653030191629 2161280257277494886321861)
            ·
              refine ⟨405240048239530291185349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2161280257277494886321861 405240048239530291185349)
              ·
                refine ⟨75982509044911929597253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405240048239530291185349 75982509044911929597253)
                ·
                  rfl

theorem cell20_499417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_499417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499417 prefixEnd_499417 := by exact prefixLift 499417
  have htrace : WordTrace (prefixWord ++ tailWord_499417) baseStart_499417 baseEnd_499417 := by
    simpa [prefixWord, tailWord_499417, baseEnd_499417] using wordTrace_append hprefix tailTrace_499417
  have hstable : (prefixWord ++ tailWord_499417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499417).length < 2 ^ (prefixWord ++ tailWord_499417).sum := by decide
  have hdescent : baseEnd_499417 < baseStart_499417 := by decide
  rcases family_descends (prefixWord ++ tailWord_499417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499444 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_499444 : Nat := 118140960795 + 499444 * 2 ^ 59
def prefixEnd_499444 : Nat := 4983230072969 + 3 ^ 40 * 499444 * 2
def baseEnd_499444 : Nat := 227959850670443694891649

theorem tailTrace_499444 : CollatzResearch.WordTrace tailWord_499444 prefixEnd_499444 227959850670443694891649 := by
  unfold tailWord_499444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108109601303580544684693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12144146135071440726246257 9108109601303580544684693)
  ·
    refine ⟨426942637561105338032095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9108109601303580544684693 426942637561105338032095)
    ·
      refine ⟨640413956341658007048143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426942637561105338032095 640413956341658007048143)
      ·
        refine ⟨960620934512487010572215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640413956341658007048143 960620934512487010572215)
        ·
          refine ⟨1440931401768730515858323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960620934512487010572215 1440931401768730515858323)
          ·
            refine ⟨2161397102653095773787485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440931401768730515858323 2161397102653095773787485)
            ·
              refine ⟨810523913494910915170307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2161397102653095773787485 810523913494910915170307)
              ·
                refine ⟨1215785870242366372755461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810523913494910915170307 1215785870242366372755461)
                ·
                  refine ⟨227959850670443694891649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215785870242366372755461 227959850670443694891649)
                  ·
                    rfl

theorem cell20_499444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_499444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499444 prefixEnd_499444 := by exact prefixLift 499444
  have htrace : WordTrace (prefixWord ++ tailWord_499444) baseStart_499444 baseEnd_499444 := by
    simpa [prefixWord, tailWord_499444, baseEnd_499444] using wordTrace_append hprefix tailTrace_499444
  have hstable : (prefixWord ++ tailWord_499444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499444).length < 2 ^ (prefixWord ++ tailWord_499444).sum := by decide
  have hdescent : baseEnd_499444 < baseStart_499444 := by decide
  rcases family_descends (prefixWord ++ tailWord_499444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499454 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_499454 : Nat := 118140960795 + 499454 * 2 ^ 59
def prefixEnd_499454 : Nat := 4983230072969 + 3 ^ 40 * 499454 * 2
def baseEnd_499454 : Nat := 227964414942928104558275

theorem tailTrace_499454 : CollatzResearch.WordTrace tailWord_499454 prefixEnd_499454 227964414942928104558275 := by
  unfold tailWord_499454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277072991571366599654177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12144389288380621864822277 2277072991571366599654177)
  ·
    refine ⟨1707804743678524949740633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2277072991571366599654177 1707804743678524949740633)
    ·
      refine ⟨1280853557758893712305475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1707804743678524949740633 1280853557758893712305475)
      ·
        refine ⟨1921280336638340568458213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280853557758893712305475 1921280336638340568458213)
        ·
          refine ⟨360240063119688856585915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1921280336638340568458213 360240063119688856585915)
          ·
            refine ⟨540360094679533284878873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360240063119688856585915 540360094679533284878873)
            ·
              refine ⟨405270071009649963659155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540360094679533284878873 405270071009649963659155)
              ·
                refine ⟨607905106514474945488733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405270071009649963659155 607905106514474945488733)
                ·
                  refine ⟨227964414942928104558275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607905106514474945488733 227964414942928104558275)
                  ·
                    rfl

theorem cell20_499454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_499454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499454 prefixEnd_499454 := by exact prefixLift 499454
  have htrace : WordTrace (prefixWord ++ tailWord_499454) baseStart_499454 baseEnd_499454 := by
    simpa [prefixWord, tailWord_499454, baseEnd_499454] using wordTrace_append hprefix tailTrace_499454
  have hstable : (prefixWord ++ tailWord_499454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499454).length < 2 ^ (prefixWord ++ tailWord_499454).sum := by decide
  have hdescent : baseEnd_499454 < baseStart_499454 := by decide
  rcases family_descends (prefixWord ++ tailWord_499454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499500 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_499500 : Nat := 118140960795 + 499500 * 2 ^ 59
def prefixEnd_499500 : Nat := 4983230072969 + 3 ^ 40 * 499500 * 2
def baseEnd_499500 : Nat := 227985410596356389024753

theorem tailTrace_499500 : CollatzResearch.WordTrace tailWord_499500 prefixEnd_499500 227985410596356389024753 := by
  unfold tailWord_499500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9109130845202141326703977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12145507793602855102271969 9109130845202141326703977)
  ·
    refine ⟨6831848133901605995027983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9109130845202141326703977 6831848133901605995027983)
    ·
      refine ⟨10247772200852408992541975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6831848133901605995027983 10247772200852408992541975)
      ·
        refine ⟨15371658301278613488812963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247772200852408992541975 15371658301278613488812963)
        ·
          refine ⟨23057487451917920233219445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15371658301278613488812963 23057487451917920233219445)
          ·
            refine ⟨2161639448617305021864323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23057487451917920233219445 2161639448617305021864323)
            ·
              refine ⟨3242459172925957532796485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161639448617305021864323 3242459172925957532796485)
              ·
                refine ⟨607961094923617037399341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3242459172925957532796485 607961094923617037399341)
                ·
                  refine ⟨227985410596356389024753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607961094923617037399341 227985410596356389024753)
                  ·
                    rfl

theorem cell20_499500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_499500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499500 prefixEnd_499500 := by exact prefixLift 499500
  have htrace : WordTrace (prefixWord ++ tailWord_499500) baseStart_499500 baseEnd_499500 := by
    simpa [prefixWord, tailWord_499500, baseEnd_499500] using wordTrace_append hprefix tailTrace_499500
  have hstable : (prefixWord ++ tailWord_499500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499500).length < 2 ^ (prefixWord ++ tailWord_499500).sum := by decide
  have hdescent : baseEnd_499500 < baseStart_499500 := by decide
  rcases family_descends (prefixWord ++ tailWord_499500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499510 : List Nat := [5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_499510 : Nat := 118140960795 + 499510 * 2 ^ 59
def prefixEnd_499510 : Nat := 4983230072969 + 3 ^ 40 * 499510 * 2
def baseEnd_499510 : Nat := 75996658289613599563793

theorem tailTrace_499510 : CollatzResearch.WordTrace tailWord_499510 prefixEnd_499510 75996658289613599563793 := by
  unfold tailWord_499510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138664151273003397579499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12145750946912036240847989 1138664151273003397579499)
  ·
    refine ⟨1707996226909505096369249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1138664151273003397579499 1707996226909505096369249)
    ·
      refine ⟨1280997170182128822276937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1707996226909505096369249 1280997170182128822276937)
      ·
        refine ⟨960747877636596616707703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1280997170182128822276937 960747877636596616707703)
        ·
          refine ⟨1441121816454894925061555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960747877636596616707703 1441121816454894925061555)
          ·
            refine ⟨2161682724682342387592333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441121816454894925061555 2161682724682342387592333)
            ·
              refine ⟨810631021755878395347125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2161682724682342387592333 810631021755878395347125)
              ·
                refine ⟨75996658289613599563793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 810631021755878395347125 75996658289613599563793)
                ·
                  rfl

theorem cell20_499510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_499510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499510 prefixEnd_499510 := by exact prefixLift 499510
  have htrace : WordTrace (prefixWord ++ tailWord_499510) baseStart_499510 baseEnd_499510 := by
    simpa [prefixWord, tailWord_499510, baseEnd_499510] using wordTrace_append hprefix tailTrace_499510
  have hstable : (prefixWord ++ tailWord_499510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499510).length < 2 ^ (prefixWord ++ tailWord_499510).sum := by decide
  have hdescent : baseEnd_499510 < baseStart_499510 := by decide
  rcases family_descends (prefixWord ++ tailWord_499510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499517 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_499517 : Nat := 118140960795 + 499517 * 2 ^ 59
def prefixEnd_499517 : Nat := 4983230072969 + 3 ^ 40 * 499517 * 2
def baseEnd_499517 : Nat := 227993169859579885458017

theorem tailTrace_499517 : CollatzResearch.WordTrace tailWord_499517 prefixEnd_499517 227993169859579885458017 := by
  unfold tailWord_499517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18218881731342694556776805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12145921154228463037851203 18218881731342694556776805)
  ·
    refine ⟨3416040324626755229395651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18218881731342694556776805 3416040324626755229395651)
    ·
      refine ⟨5124060486940132844093477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3416040324626755229395651 5124060486940132844093477)
      ·
        refine ⟨960761341301274908267527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5124060486940132844093477 960761341301274908267527)
        ·
          refine ⟨1441142011951912362401291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960761341301274908267527 1441142011951912362401291)
          ·
            refine ⟨2161713017927868543601937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441142011951912362401291 2161713017927868543601937)
            ·
              refine ⟨1621284763445901407701453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2161713017927868543601937 1621284763445901407701453)
              ·
                refine ⟨607981786292213027888045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621284763445901407701453 607981786292213027888045)
                ·
                  refine ⟨227993169859579885458017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607981786292213027888045 227993169859579885458017)
                  ·
                    rfl

theorem cell20_499517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_499517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499517 prefixEnd_499517 := by exact prefixLift 499517
  have htrace : WordTrace (prefixWord ++ tailWord_499517) baseStart_499517 baseEnd_499517 := by
    simpa [prefixWord, tailWord_499517, baseEnd_499517] using wordTrace_append hprefix tailTrace_499517
  have hstable : (prefixWord ++ tailWord_499517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499517).length < 2 ^ (prefixWord ++ tailWord_499517).sum := by decide
  have hdescent : baseEnd_499517 < baseStart_499517 := by decide
  rcases family_descends (prefixWord ++ tailWord_499517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499541 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 2]
def baseStart_499541 : Nat := 118140960795 + 499541 * 2 ^ 59
def prefixEnd_499541 : Nat := 4983230072969 + 3 ^ 40 * 499541 * 2
def baseEnd_499541 : Nat := 228004124113542468657919

theorem tailTrace_499541 : CollatzResearch.WordTrace tailWord_499541 prefixEnd_499541 228004124113542468657919 := by
  unfold tailWord_499541
  simp only [CollatzResearch.WordTrace]
  refine ⟨18219757083255746655650477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12146504722170497770433651 18219757083255746655650477)
  ·
    refine ⟨6832408906220904995868929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18219757083255746655650477 6832408906220904995868929)
    ·
      refine ⟨5124306679665678746901697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6832408906220904995868929 5124306679665678746901697)
      ·
        refine ⟨3843230009749259060176273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5124306679665678746901697 3843230009749259060176273)
        ·
          refine ⟨2882422507311944295132205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3843230009749259060176273 2882422507311944295132205)
          ·
            refine ⟨1080908440241979110674577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2882422507311944295132205 1080908440241979110674577)
            ·
              refine ⟨810681330181484333005933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080908440241979110674577 810681330181484333005933)
              ·
                refine ⟨304005498818056624877225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810681330181484333005933 304005498818056624877225)
                ·
                  refine ⟨228004124113542468657919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304005498818056624877225 228004124113542468657919)
                  ·
                    rfl

theorem cell20_499541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_499541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499541 prefixEnd_499541 := by exact prefixLift 499541
  have htrace : WordTrace (prefixWord ++ tailWord_499541) baseStart_499541 baseEnd_499541 := by
    simpa [prefixWord, tailWord_499541, baseEnd_499541] using wordTrace_append hprefix tailTrace_499541
  have hstable : (prefixWord ++ tailWord_499541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499541).length < 2 ^ (prefixWord ++ tailWord_499541).sum := by decide
  have hdescent : baseEnd_499541 < baseStart_499541 := by decide
  rcases family_descends (prefixWord ++ tailWord_499541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499552 : List Nat := [2, 1, 1, 3, 3, 3, 7]
def baseStart_499552 : Nat := 118140960795 + 499552 * 2 ^ 59
def prefixEnd_499552 : Nat := 4983230072969 + 3 ^ 40 * 499552 * 2
def baseEnd_499552 : Nat := 25334349423697257699023

theorem tailTrace_499552 : CollatzResearch.WordTrace tailWord_499552 prefixEnd_499552 25334349423697257699023 := by
  unfold tailWord_499552
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110079143107947767150455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12146772190810597022867273 9110079143107947767150455)
  ·
    refine ⟨13665118714661921650725683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110079143107947767150455 13665118714661921650725683)
    ·
      refine ⟨20497678071992882476088525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13665118714661921650725683 20497678071992882476088525)
      ·
        refine ⟨7686629276997330928533197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20497678071992882476088525 7686629276997330928533197)
        ·
          refine ⟨2882485978873999098199949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7686629276997330928533197 2882485978873999098199949)
          ·
            refine ⟨1080932242077749661824981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2882485978873999098199949 1080932242077749661824981)
            ·
              refine ⟨25334349423697257699023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1080932242077749661824981 25334349423697257699023)
              ·
                rfl

theorem cell20_499552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_499552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499552 prefixEnd_499552 := by exact prefixLift 499552
  have htrace : WordTrace (prefixWord ++ tailWord_499552) baseStart_499552 baseEnd_499552 := by
    simpa [prefixWord, tailWord_499552, baseEnd_499552] using wordTrace_append hprefix tailTrace_499552
  have hstable : (prefixWord ++ tailWord_499552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499552).length < 2 ^ (prefixWord ++ tailWord_499552).sum := by decide
  have hdescent : baseEnd_499552 < baseStart_499552 := by decide
  rcases family_descends (prefixWord ++ tailWord_499552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499617 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 4]
def baseStart_499617 : Nat := 118140960795 + 499617 * 2 ^ 59
def prefixEnd_499617 : Nat := 4983230072969 + 3 ^ 40 * 499617 * 2
def baseEnd_499617 : Nat := 228038812584423982124275

theorem tailTrace_499617 : CollatzResearch.WordTrace tailWord_499617 prefixEnd_499617 228038812584423982124275 := by
  unfold tailWord_499617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18222529030980411635417105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12148352687320274423611403 18222529030980411635417105)
  ·
    refine ⟨13666896773235308726562829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18222529030980411635417105 13666896773235308726562829)
    ·
      refine ⟨5125086289963240772461061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13666896773235308726562829 5125086289963240772461061)
      ·
        refine ⟨960953679368107644836449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5125086289963240772461061 960953679368107644836449)
        ·
          refine ⟨720715259526080733627337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960953679368107644836449 720715259526080733627337)
          ·
            refine ⟨540536444644560550220503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720715259526080733627337 540536444644560550220503)
            ·
              refine ⟨810804666966840825330755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540536444644560550220503 810804666966840825330755)
              ·
                refine ⟨1216207000450261237996133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810804666966840825330755 1216207000450261237996133)
                ·
                  refine ⟨228038812584423982124275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216207000450261237996133 228038812584423982124275)
                  ·
                    rfl

theorem cell20_499617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_499617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499617 prefixEnd_499617 := by exact prefixLift 499617
  have htrace : WordTrace (prefixWord ++ tailWord_499617) baseStart_499617 baseEnd_499617 := by
    simpa [prefixWord, tailWord_499617, baseEnd_499617] using wordTrace_append hprefix tailTrace_499617
  have hstable : (prefixWord ++ tailWord_499617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499617).length < 2 ^ (prefixWord ++ tailWord_499617).sum := by decide
  have hdescent : baseEnd_499617 < baseStart_499617 := by decide
  rcases family_descends (prefixWord ++ tailWord_499617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499666 : List Nat := [3, 2, 2, 3, 10]
def baseStart_499666 : Nat := 118140960795 + 499666 * 2 ^ 59
def prefixEnd_499666 : Nat := 4983230072969 + 3 ^ 40 * 499666 * 2
def baseEnd_499666 : Nat := 2815570092834538141861

theorem tailTrace_499666 : CollatzResearch.WordTrace tailWord_499666 prefixEnd_499666 2815570092834538141861 := by
  unfold tailWord_499666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556079051950723250987713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12149544138535262002633901 4556079051950723250987713)
  ·
    refine ⟨3417059288963042438240785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4556079051950723250987713 3417059288963042438240785)
    ·
      refine ⟨2562794466722281828680589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3417059288963042438240785 2562794466722281828680589)
      ·
        refine ⟨961047925020855685755221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2562794466722281828680589 961047925020855685755221)
        ·
          refine ⟨2815570092834538141861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 961047925020855685755221 2815570092834538141861)
          ·
            rfl

theorem cell20_499666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 10].length) (baseStart_499666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499666 prefixEnd_499666 := by exact prefixLift 499666
  have htrace : WordTrace (prefixWord ++ tailWord_499666) baseStart_499666 baseEnd_499666 := by
    simpa [prefixWord, tailWord_499666, baseEnd_499666] using wordTrace_append hprefix tailTrace_499666
  have hstable : (prefixWord ++ tailWord_499666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499666).length < 2 ^ (prefixWord ++ tailWord_499666).sum := by decide
  have hdescent : baseEnd_499666 < baseStart_499666 := by decide
  rcases family_descends (prefixWord ++ tailWord_499666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499669 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_499669 : Nat := 118140960795 + 499669 * 2 ^ 59
def prefixEnd_499669 : Nat := 4983230072969 + 3 ^ 40 * 499669 * 2
def baseEnd_499669 : Nat := 228062546801342912390729

theorem tailTrace_499669 : CollatzResearch.WordTrace tailWord_499669 prefixEnd_499669 228062546801342912390729 := by
  unfold tailWord_499669
  simp only [CollatzResearch.WordTrace]
  refine ⟨18224425626792024516310061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12149617084528016344206707 18224425626792024516310061)
  ·
    refine ⟨6834159610047009193616273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18224425626792024516310061 6834159610047009193616273)
    ·
      refine ⟨5125619707535256895212205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6834159610047009193616273 5125619707535256895212205)
      ·
        refine ⟨1922107390325721335704577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5125619707535256895212205 1922107390325721335704577)
        ·
          refine ⟨1441580542744291001778433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1922107390325721335704577 1441580542744291001778433)
          ·
            refine ⟨1081185407058218251333825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1441580542744291001778433 1081185407058218251333825)
            ·
              refine ⟨810889055293663688500369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081185407058218251333825 810889055293663688500369)
              ·
                refine ⟨608166791470247766375277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810889055293663688500369 608166791470247766375277)
                ·
                  refine ⟨228062546801342912390729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608166791470247766375277 228062546801342912390729)
                  ·
                    rfl

theorem cell20_499669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_499669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499669 prefixEnd_499669 := by exact prefixLift 499669
  have htrace : WordTrace (prefixWord ++ tailWord_499669) baseStart_499669 baseEnd_499669 := by
    simpa [prefixWord, tailWord_499669, baseEnd_499669] using wordTrace_append hprefix tailTrace_499669
  have hstable : (prefixWord ++ tailWord_499669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499669).length < 2 ^ (prefixWord ++ tailWord_499669).sum := by decide
  have hdescent : baseEnd_499669 < baseStart_499669 := by decide
  rcases family_descends (prefixWord ++ tailWord_499669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499680 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_499680 : Nat := 118140960795 + 499680 * 2 ^ 59
def prefixEnd_499680 : Nat := 4983230072969 + 3 ^ 40 * 499680 * 2
def baseEnd_499680 : Nat := 228067567501075763024017

theorem tailTrace_499680 : CollatzResearch.WordTrace tailWord_499680 prefixEnd_499680 228067567501075763024017 := by
  unfold tailWord_499680
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112413414876086697480247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12149884553168115596640329 9112413414876086697480247)
  ·
    refine ⟨13668620122314130046220371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9112413414876086697480247 13668620122314130046220371)
    ·
      refine ⟨20502930183471195069330557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13668620122314130046220371 20502930183471195069330557)
      ·
        refine ⟨7688598818801698150998959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20502930183471195069330557 7688598818801698150998959)
        ·
          refine ⟨11532898228202547226498439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688598818801698150998959 11532898228202547226498439)
          ·
            refine ⟨17299347342303820839747659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532898228202547226498439 17299347342303820839747659)
            ·
              refine ⟨25949021013455731259621489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299347342303820839747659 25949021013455731259621489)
              ·
                refine ⟨19461765760091798444716117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25949021013455731259621489 19461765760091798444716117)
                ·
                  refine ⟨228067567501075763024017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19461765760091798444716117 228067567501075763024017)
                  ·
                    rfl

theorem cell20_499680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_499680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499680 prefixEnd_499680 := by exact prefixLift 499680
  have htrace : WordTrace (prefixWord ++ tailWord_499680) baseStart_499680 baseEnd_499680 := by
    simpa [prefixWord, tailWord_499680, baseEnd_499680] using wordTrace_append hprefix tailTrace_499680
  have hstable : (prefixWord ++ tailWord_499680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499680).length < 2 ^ (prefixWord ++ tailWord_499680).sum := by decide
  have hdescent : baseEnd_499680 < baseStart_499680 := by decide
  rcases family_descends (prefixWord ++ tailWord_499680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499683 : List Nat := [1, 1, 1, 6, 1, 4, 1, 5]
def baseStart_499683 : Nat := 118140960795 + 499683 * 2 ^ 59
def prefixEnd_499683 : Nat := 4983230072969 + 3 ^ 40 * 499683 * 2
def baseEnd_499683 : Nat := 76022978927607028641335

theorem tailTrace_499683 : CollatzResearch.WordTrace tailWord_499683 prefixEnd_499683 76022978927607028641335 := by
  unfold tailWord_499683
  simp only [CollatzResearch.WordTrace]
  refine ⟨18224936248741304907319703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12149957499160869938213135 18224936248741304907319703)
  ·
    refine ⟨27337404373111957360979555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18224936248741304907319703 27337404373111957360979555)
    ·
      refine ⟨41006106559667936041469333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27337404373111957360979555 41006106559667936041469333)
      ·
        refine ⟨1922161244984434501943875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41006106559667936041469333 1922161244984434501943875)
        ·
          refine ⟨2883241867476651752915813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922161244984434501943875 2883241867476651752915813)
          ·
            refine ⟨540607850151872203671715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2883241867476651752915813 540607850151872203671715)
            ·
              refine ⟨810911775227808305507573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540607850151872203671715 810911775227808305507573)
              ·
                refine ⟨76022978927607028641335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 810911775227808305507573 76022978927607028641335)
                ·
                  rfl

theorem cell20_499683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_499683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499683 prefixEnd_499683 := by exact prefixLift 499683
  have htrace : WordTrace (prefixWord ++ tailWord_499683) baseStart_499683 baseEnd_499683 := by
    simpa [prefixWord, tailWord_499683, baseEnd_499683] using wordTrace_append hprefix tailTrace_499683
  have hstable : (prefixWord ++ tailWord_499683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499683).length < 2 ^ (prefixWord ++ tailWord_499683).sum := by decide
  have hdescent : baseEnd_499683 < baseStart_499683 := by decide
  rcases family_descends (prefixWord ++ tailWord_499683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499690 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_499690 : Nat := 118140960795 + 499690 * 2 ^ 59
def prefixEnd_499690 : Nat := 4983230072969 + 3 ^ 40 * 499690 * 2
def baseEnd_499690 : Nat := 228072131773560172690643

theorem tailTrace_499690 : CollatzResearch.WordTrace tailWord_499690 prefixEnd_499690 228072131773560172690643 := by
  unfold tailWord_499690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556297889928986275706131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12150127706477296735216349 4556297889928986275706131)
  ·
    refine ⟨6834446834893479413559197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4556297889928986275706131 6834446834893479413559197)
    ·
      refine ⟨2562917563085054780084699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6834446834893479413559197 2562917563085054780084699)
      ·
        refine ⟨3844376344627582170127049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562917563085054780084699 3844376344627582170127049)
        ·
          refine ⟨2883282258470686627595287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3844376344627582170127049 2883282258470686627595287)
          ·
            refine ⟨4324923387706029941392931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883282258470686627595287 4324923387706029941392931)
            ·
              refine ⟨6487385081559044912089397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324923387706029941392931 6487385081559044912089397)
              ·
                refine ⟨608192351396160460508381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6487385081559044912089397 608192351396160460508381)
                ·
                  refine ⟨228072131773560172690643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608192351396160460508381 228072131773560172690643)
                  ·
                    rfl

theorem cell20_499690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_499690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499690 prefixEnd_499690 := by exact prefixLift 499690
  have htrace : WordTrace (prefixWord ++ tailWord_499690) baseStart_499690 baseEnd_499690 := by
    simpa [prefixWord, tailWord_499690, baseEnd_499690] using wordTrace_append hprefix tailTrace_499690
  have hstable : (prefixWord ++ tailWord_499690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499690).length < 2 ^ (prefixWord ++ tailWord_499690).sum := by decide
  have hdescent : baseEnd_499690 < baseStart_499690 := by decide
  rcases family_descends (prefixWord ++ tailWord_499690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499693 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 4]
def baseStart_499693 : Nat := 118140960795 + 499693 * 2 ^ 59
def prefixEnd_499693 : Nat := 4983230072969 + 3 ^ 40 * 499693 * 2
def baseEnd_499693 : Nat := 228073501055305495590631

theorem tailTrace_499693 : CollatzResearch.WordTrace tailWord_499693 prefixEnd_499693 228073501055305495590631 := by
  unfold tailWord_499693
  simp only [CollatzResearch.WordTrace]
  refine ⟨18225300978705076615183733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12150200652470051076789155 18225300978705076615183733)
  ·
    refine ⟨1708621966753600932673475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18225300978705076615183733 1708621966753600932673475)
    ·
      refine ⟨2562932950130401399010213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708621966753600932673475 2562932950130401399010213)
      ·
        refine ⟨480549928149450262314415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2562932950130401399010213 480549928149450262314415)
        ·
          refine ⟨720824892224175393471623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480549928149450262314415 720824892224175393471623)
          ·
            refine ⟨1081237338336263090207435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720824892224175393471623 1081237338336263090207435)
            ·
              refine ⟨1621856007504394635311153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081237338336263090207435 1621856007504394635311153)
              ·
                refine ⟨1216392005628295976483365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621856007504394635311153 1216392005628295976483365)
                ·
                  refine ⟨228073501055305495590631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216392005628295976483365 228073501055305495590631)
                  ·
                    rfl

theorem cell20_499693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_499693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499693 prefixEnd_499693 := by exact prefixLift 499693
  have htrace : WordTrace (prefixWord ++ tailWord_499693) baseStart_499693 baseEnd_499693 := by
    simpa [prefixWord, tailWord_499693, baseEnd_499693] using wordTrace_append hprefix tailTrace_499693
  have hstable : (prefixWord ++ tailWord_499693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499693).length < 2 ^ (prefixWord ++ tailWord_499693).sum := by decide
  have hdescent : baseEnd_499693 < baseStart_499693 := by decide
  rcases family_descends (prefixWord ++ tailWord_499693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499710 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_499710 : Nat := 118140960795 + 499710 * 2 ^ 59
def prefixEnd_499710 : Nat := 4983230072969 + 3 ^ 40 * 499710 * 2
def baseEnd_499710 : Nat := 228081260318528992023895

theorem tailTrace_499710 : CollatzResearch.WordTrace tailWord_499710 prefixEnd_499710 228081260318528992023895 := by
  unfold tailWord_499710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278240127455436064819073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12150614013095659012368389 2278240127455436064819073)
  ·
    refine ⟨1708680095591577048614305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2278240127455436064819073 1708680095591577048614305)
    ·
      refine ⟨1281510071693682786460729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708680095591577048614305 1281510071693682786460729)
      ·
        refine ⟨961132553770262089845547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1281510071693682786460729 961132553770262089845547)
        ·
          refine ⟨1441698830655393134768321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961132553770262089845547 1441698830655393134768321)
          ·
            refine ⟨1081274122991544851076241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1441698830655393134768321 1081274122991544851076241)
            ·
              refine ⟨810955592243658638307181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081274122991544851076241 810955592243658638307181)
              ·
                refine ⟨304108347091371989365193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810955592243658638307181 304108347091371989365193)
                ·
                  refine ⟨228081260318528992023895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304108347091371989365193 228081260318528992023895)
                  ·
                    rfl

theorem cell20_499710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_499710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499710 prefixEnd_499710 := by exact prefixLift 499710
  have htrace : WordTrace (prefixWord ++ tailWord_499710) baseStart_499710 baseEnd_499710 := by
    simpa [prefixWord, tailWord_499710, baseEnd_499710] using wordTrace_append hprefix tailTrace_499710
  have hstable : (prefixWord ++ tailWord_499710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499710).length < 2 ^ (prefixWord ++ tailWord_499710).sum := by decide
  have hdescent : baseEnd_499710 < baseStart_499710 := by decide
  rcases family_descends (prefixWord ++ tailWord_499710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499756 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_499756 : Nat := 118140960795 + 499756 * 2 ^ 59
def prefixEnd_499756 : Nat := 4983230072969 + 3 ^ 40 * 499756 * 2
def baseEnd_499756 : Nat := 228102255971957276490373

theorem tailTrace_499756 : CollatzResearch.WordTrace tailWord_499756 prefixEnd_499756 228102255971957276490373 := by
  unfold tailWord_499756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113799388738419187363561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12151732518317892249818081 9113799388738419187363561)
  ·
    refine ⟨6835349541553814390522671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9113799388738419187363561 6835349541553814390522671)
    ·
      refine ⟨10253024312330721585784007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835349541553814390522671 10253024312330721585784007)
      ·
        refine ⟨15379536468496082378676011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253024312330721585784007 15379536468496082378676011)
        ·
          refine ⟨23069304702744123568014017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15379536468496082378676011 23069304702744123568014017)
          ·
            refine ⟨17301978527058092676010513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23069304702744123568014017 17301978527058092676010513)
            ·
              refine ⟨12976483895293569507007885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301978527058092676010513 12976483895293569507007885)
              ·
                refine ⟨4866181460735088565127957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12976483895293569507007885 4866181460735088565127957)
                ·
                  refine ⟨228102255971957276490373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4866181460735088565127957 228102255971957276490373)
                  ·
                    rfl

theorem cell20_499756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_499756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499756 prefixEnd_499756 := by exact prefixLift 499756
  have htrace : WordTrace (prefixWord ++ tailWord_499756) baseStart_499756 baseEnd_499756 := by
    simpa [prefixWord, tailWord_499756, baseEnd_499756] using wordTrace_append hprefix tailTrace_499756
  have hstable : (prefixWord ++ tailWord_499756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499756).length < 2 ^ (prefixWord ++ tailWord_499756).sum := by decide
  have hdescent : baseEnd_499756 < baseStart_499756 := by decide
  rcases family_descends (prefixWord ++ tailWord_499756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499766 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_499766 : Nat := 118140960795 + 499766 * 2 ^ 59
def prefixEnd_499766 : Nat := 4983230072969 + 3 ^ 40 * 499766 * 2
def baseEnd_499766 : Nat := 228106820244441686156999

theorem tailTrace_499766 : CollatzResearch.WordTrace tailWord_499766 prefixEnd_499766 228106820244441686156999 := by
  unfold tailWord_499766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139247719215038130161947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12151975671627073388394101 1139247719215038130161947)
  ·
    refine ⟨1708871578822557195242921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139247719215038130161947 1708871578822557195242921)
    ·
      refine ⟨1281653684116917896432191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708871578822557195242921 1281653684116917896432191)
      ·
        refine ⟨1922480526175376844648287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281653684116917896432191 1922480526175376844648287)
        ·
          refine ⟨2883720789263065266972431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922480526175376844648287 2883720789263065266972431)
          ·
            refine ⟨4325581183894597900458647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883720789263065266972431 4325581183894597900458647)
            ·
              refine ⟨6488371775841896850687971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325581183894597900458647 6488371775841896850687971)
              ·
                refine ⟨9732557663762845276031957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488371775841896850687971 9732557663762845276031957)
                ·
                  refine ⟨228106820244441686156999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9732557663762845276031957 228106820244441686156999)
                  ·
                    rfl

theorem cell20_499766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_499766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499766 prefixEnd_499766 := by exact prefixLift 499766
  have htrace : WordTrace (prefixWord ++ tailWord_499766) baseStart_499766 baseEnd_499766 := by
    simpa [prefixWord, tailWord_499766, baseEnd_499766] using wordTrace_append hprefix tailTrace_499766
  have hstable : (prefixWord ++ tailWord_499766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499766).length < 2 ^ (prefixWord ++ tailWord_499766).sum := by decide
  have hdescent : baseEnd_499766 < baseStart_499766 := by decide
  rcases family_descends (prefixWord ++ tailWord_499766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499790 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_499790 : Nat := 118140960795 + 499790 * 2 ^ 59
def prefixEnd_499790 : Nat := 4983230072969 + 3 ^ 40 * 499790 * 2
def baseEnd_499790 : Nat := 228117774498404269356901

theorem tailTrace_499790 : CollatzResearch.WordTrace tailWord_499790 prefixEnd_499790 228117774498404269356901 := by
  unfold tailWord_499790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278604857419207772683103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12152559239569108120976549 2278604857419207772683103)
  ·
    refine ⟨3417907286128811659024655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278604857419207772683103 3417907286128811659024655)
    ·
      refine ⟨5126860929193217488536983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417907286128811659024655 5126860929193217488536983)
      ·
        refine ⟨7690291393789826232805475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126860929193217488536983 7690291393789826232805475)
        ·
          refine ⟨11535437090684739349208213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690291393789826232805475 11535437090684739349208213)
          ·
            refine ⟨540723613625847156994135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11535437090684739349208213 540723613625847156994135)
            ·
              refine ⟨811085420438770735491203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540723613625847156994135 811085420438770735491203)
              ·
                refine ⟨1216628130658156103236805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811085420438770735491203 1216628130658156103236805)
                ·
                  refine ⟨228117774498404269356901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216628130658156103236805 228117774498404269356901)
                  ·
                    rfl

theorem cell20_499790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_499790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499790 prefixEnd_499790 := by exact prefixLift 499790
  have htrace : WordTrace (prefixWord ++ tailWord_499790) baseStart_499790 baseEnd_499790 := by
    simpa [prefixWord, tailWord_499790, baseEnd_499790] using wordTrace_append hprefix tailTrace_499790
  have hstable : (prefixWord ++ tailWord_499790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499790).length < 2 ^ (prefixWord ++ tailWord_499790).sum := by decide
  have hdescent : baseEnd_499790 < baseStart_499790 := by decide
  rcases family_descends (prefixWord ++ tailWord_499790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499841 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 2]
def baseStart_499841 : Nat := 118140960795 + 499841 * 2 ^ 59
def prefixEnd_499841 : Nat := 4983230072969 + 3 ^ 40 * 499841 * 2
def baseEnd_499841 : Nat := 228141052288074758656693

theorem tailTrace_499841 : CollatzResearch.WordTrace tailWord_499841 prefixEnd_499841 228141052288074758656693 := by
  unfold tailWord_499841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18230698982168897891571377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12153799321445931927714251 18230698982168897891571377)
  ·
    refine ⟨13673024236626673418678533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18230698982168897891571377 13673024236626673418678533)
    ·
      refine ⟨2563692044367501266002225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13673024236626673418678533 2563692044367501266002225)
      ·
        refine ⟨1922769033275625949501669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2563692044367501266002225 1922769033275625949501669)
        ·
          refine ⟨360519193739179865531563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1922769033275625949501669 360519193739179865531563)
          ·
            refine ⟨540778790608769798297345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360519193739179865531563 540778790608769798297345)
            ·
              refine ⟨405584092956577348723009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540778790608769798297345 405584092956577348723009)
              ·
                refine ⟨304188069717433011542257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405584092956577348723009 304188069717433011542257)
                ·
                  refine ⟨228141052288074758656693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304188069717433011542257 228141052288074758656693)
                  ·
                    rfl

theorem cell20_499841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_499841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499841 prefixEnd_499841 := by exact prefixLift 499841
  have htrace : WordTrace (prefixWord ++ tailWord_499841) baseStart_499841 baseEnd_499841 := by
    simpa [prefixWord, tailWord_499841, baseEnd_499841] using wordTrace_append hprefix tailTrace_499841
  have hstable : (prefixWord ++ tailWord_499841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499841).length < 2 ^ (prefixWord ++ tailWord_499841).sum := by decide
  have hdescent : baseEnd_499841 < baseStart_499841 := by decide
  rcases family_descends (prefixWord ++ tailWord_499841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499845 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 2]
def baseStart_499845 : Nat := 118140960795 + 499845 * 2 ^ 59
def prefixEnd_499845 : Nat := 4983230072969 + 3 ^ 40 * 499845 * 2
def baseEnd_499845 : Nat := 228142877997068522523343

theorem tailTrace_499845 : CollatzResearch.WordTrace tailWord_499845 prefixEnd_499845 228142877997068522523343 := by
  unfold tailWord_499845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18230844874154406574716989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12153896582769604383144659 18230844874154406574716989)
  ·
    refine ⟨6836566827807902465518871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18230844874154406574716989 6836566827807902465518871)
    ·
      refine ⟨10254850241711853698278307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6836566827807902465518871 10254850241711853698278307)
      ·
        refine ⟨15382275362567780547417461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10254850241711853698278307 15382275362567780547417461)
        ·
          refine ⟨1442088315240729426320387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15382275362567780547417461 1442088315240729426320387)
          ·
            refine ⟨2163132472861094139480581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442088315240729426320387 2163132472861094139480581)
            ·
              refine ⟨405587338661455151152609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2163132472861094139480581 405587338661455151152609)
              ·
                refine ⟨304190503996091363364457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405587338661455151152609 304190503996091363364457)
                ·
                  refine ⟨228142877997068522523343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304190503996091363364457 228142877997068522523343)
                  ·
                    rfl

theorem cell20_499845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_499845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499845 prefixEnd_499845 := by exact prefixLift 499845
  have htrace : WordTrace (prefixWord ++ tailWord_499845) baseStart_499845 baseEnd_499845 := by
    simpa [prefixWord, tailWord_499845, baseEnd_499845] using wordTrace_append hprefix tailTrace_499845
  have hstable : (prefixWord ++ tailWord_499845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499845).length < 2 ^ (prefixWord ++ tailWord_499845).sum := by decide
  have hdescent : baseEnd_499845 < baseStart_499845 := by decide
  rcases family_descends (prefixWord ++ tailWord_499845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499866 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_499866 : Nat := 118140960795 + 499866 * 2 ^ 59
def prefixEnd_499866 : Nat := 4983230072969 + 3 ^ 40 * 499866 * 2
def baseEnd_499866 : Nat := 228152462969285782823257

theorem tailTrace_499866 : CollatzResearch.WordTrace tailWord_499866 prefixEnd_499866 228152462969285782823257 := by
  unfold tailWord_499866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557902701769581790307863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12154407204718884774154301 4557902701769581790307863)
  ·
    refine ⟨6836854052654372685461795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4557902701769581790307863 6836854052654372685461795)
    ·
      refine ⟨10255281078981559028192693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6836854052654372685461795 10255281078981559028192693)
      ·
        refine ⟨961432601154521158893065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10255281078981559028192693 961432601154521158893065)
        ·
          refine ⟨721074450865890869169799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 961432601154521158893065 721074450865890869169799)
          ·
            refine ⟨1081611676298836303754699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721074450865890869169799 1081611676298836303754699)
            ·
              refine ⟨1622417514448254455632049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081611676298836303754699 1622417514448254455632049)
              ·
                refine ⟨1216813135836190841724037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622417514448254455632049 1216813135836190841724037)
                ·
                  refine ⟨228152462969285782823257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1216813135836190841724037 228152462969285782823257)
                  ·
                    rfl

theorem cell20_499866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_499866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499866 prefixEnd_499866 := by exact prefixLift 499866
  have htrace : WordTrace (prefixWord ++ tailWord_499866) baseStart_499866 baseEnd_499866 := by
    simpa [prefixWord, tailWord_499866, baseEnd_499866] using wordTrace_append hprefix tailTrace_499866
  have hstable : (prefixWord ++ tailWord_499866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499866).length < 2 ^ (prefixWord ++ tailWord_499866).sum := by decide
  have hdescent : baseEnd_499866 < baseStart_499866 := by decide
  rcases family_descends (prefixWord ++ tailWord_499866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499873 : List Nat := [1, 2, 3, 3, 1, 3, 3, 4]
def baseStart_499873 : Nat := 118140960795 + 499873 * 2 ^ 59
def prefixEnd_499873 : Nat := 4983230072969 + 3 ^ 40 * 499873 * 2
def baseEnd_499873 : Nat := 76051885986674956529965

theorem tailTrace_499873 : CollatzResearch.WordTrace tailWord_499873 prefixEnd_499873 76051885986674956529965 := by
  unfold tailWord_499873
  simp only [CollatzResearch.WordTrace]
  refine ⟨18231866118052967356736273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12154577412035311571157515 18231866118052967356736273)
  ·
    refine ⟨13673899588539725517552205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18231866118052967356736273 13673899588539725517552205)
    ·
      refine ⟨5127712345702397069082077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13673899588539725517552205 5127712345702397069082077)
      ·
        refine ⟨1922892129638398900905779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5127712345702397069082077 1922892129638398900905779)
        ·
          refine ⟨2884338194457598351358669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922892129638398900905779 2884338194457598351358669)
          ·
            refine ⟨1081626822921599381759501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2884338194457598351358669 1081626822921599381759501)
            ·
              refine ⟨405610058595599768159813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1081626822921599381759501 405610058595599768159813)
              ·
                refine ⟨76051885986674956529965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405610058595599768159813 76051885986674956529965)
                ·
                  rfl

theorem cell20_499873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 4].length) (baseStart_499873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499873 prefixEnd_499873 := by exact prefixLift 499873
  have htrace : WordTrace (prefixWord ++ tailWord_499873) baseStart_499873 baseEnd_499873 := by
    simpa [prefixWord, tailWord_499873, baseEnd_499873] using wordTrace_append hprefix tailTrace_499873
  have hstable : (prefixWord ++ tailWord_499873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499873).length < 2 ^ (prefixWord ++ tailWord_499873).sum := by decide
  have hdescent : baseEnd_499873 < baseStart_499873 := by decide
  rcases family_descends (prefixWord ++ tailWord_499873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499893 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 3]
def baseStart_499893 : Nat := 118140960795 + 499893 * 2 ^ 59
def prefixEnd_499893 : Nat := 4983230072969 + 3 ^ 40 * 499893 * 2
def baseEnd_499893 : Nat := 228164786504993688923147

theorem tailTrace_499893 : CollatzResearch.WordTrace tailWord_499893 prefixEnd_499893 228164786504993688923147 := by
  unfold tailWord_499893
  simp only [CollatzResearch.WordTrace]
  refine ⟨18232595577980510772464333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12155063718653673848309555 18232595577980510772464333)
  ·
    refine ⟨6837223341742691539674125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18232595577980510772464333 6837223341742691539674125)
    ·
      refine ⟨2563958753153509327377797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6837223341742691539674125 2563958753153509327377797)
      ·
        refine ⟨480742266216282998883337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2563958753153509327377797 480742266216282998883337)
        ·
          refine ⟨360556699662212249162503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480742266216282998883337 360556699662212249162503)
          ·
            refine ⟨540835049493318373743755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360556699662212249162503 540835049493318373743755)
            ·
              refine ⟨811252574239977560615633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540835049493318373743755 811252574239977560615633)
              ·
                refine ⟨608439430679983170461725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811252574239977560615633 608439430679983170461725)
                ·
                  refine ⟨228164786504993688923147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608439430679983170461725 228164786504993688923147)
                  ·
                    rfl

theorem cell20_499893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_499893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499893 prefixEnd_499893 := by exact prefixLift 499893
  have htrace : WordTrace (prefixWord ++ tailWord_499893) baseStart_499893 baseEnd_499893 := by
    simpa [prefixWord, tailWord_499893, baseEnd_499893] using wordTrace_append hprefix tailTrace_499893
  have hstable : (prefixWord ++ tailWord_499893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499893).length < 2 ^ (prefixWord ++ tailWord_499893).sum := by decide
  have hdescent : baseEnd_499893 < baseStart_499893 := by decide
  rcases family_descends (prefixWord ++ tailWord_499893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499904 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 2]
def baseStart_499904 : Nat := 118140960795 + 499904 * 2 ^ 59
def prefixEnd_499904 : Nat := 4983230072969 + 3 ^ 40 * 499904 * 2
def baseEnd_499904 : Nat := 228169807204726539556435

theorem tailTrace_499904 : CollatzResearch.WordTrace tailWord_499904 prefixEnd_499904 228169807204726539556435 := by
  unfold tailWord_499904
  simp only [CollatzResearch.WordTrace]
  refine ⟨9116498390470329825557383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12155331187293773100743177 9116498390470329825557383)
  ·
    refine ⟨13674747585705494738336075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9116498390470329825557383 13674747585705494738336075)
    ·
      refine ⟨20512121378558242107504113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13674747585705494738336075 20512121378558242107504113)
      ·
        refine ⟨15384091033918681580628085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20512121378558242107504113 15384091033918681580628085)
        ·
          refine ⟨1442258534429876398183883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15384091033918681580628085 1442258534429876398183883)
          ·
            refine ⟨2163387801644814597275825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442258534429876398183883 2163387801644814597275825)
            ·
              refine ⟨1622540851233610947956869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163387801644814597275825 1622540851233610947956869)
              ·
                refine ⟨304226409606302052741913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1622540851233610947956869 304226409606302052741913)
                ·
                  refine ⟨228169807204726539556435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304226409606302052741913 228169807204726539556435)
                  ·
                    rfl

theorem cell20_499904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_499904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499904 prefixEnd_499904 := by exact prefixLift 499904
  have htrace : WordTrace (prefixWord ++ tailWord_499904) baseStart_499904 baseEnd_499904 := by
    simpa [prefixWord, tailWord_499904, baseEnd_499904] using wordTrace_append hprefix tailTrace_499904
  have hstable : (prefixWord ++ tailWord_499904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499904).length < 2 ^ (prefixWord ++ tailWord_499904).sum := by decide
  have hdescent : baseEnd_499904 < baseStart_499904 := by decide
  rcases family_descends (prefixWord ++ tailWord_499904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499915 : List Nat := [1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_499915 : Nat := 118140960795 + 499915 * 2 ^ 59
def prefixEnd_499915 : Nat := 4983230072969 + 3 ^ 40 * 499915 * 2
def baseEnd_499915 : Nat := 76058275968153130063241

theorem tailTrace_499915 : CollatzResearch.WordTrace tailWord_499915 prefixEnd_499915 76058275968153130063241 := by
  unfold tailWord_499915
  simp only [CollatzResearch.WordTrace]
  refine ⟨18233397983900808529765199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12155598655933872353176799 18233397983900808529765199)
  ·
    refine ⟨27350096975851212794647799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18233397983900808529765199 27350096975851212794647799)
    ·
      refine ⟨41025145463776819191971699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27350096975851212794647799 41025145463776819191971699)
      ·
        refine ⟨61537718195665228787957549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41025145463776819191971699 61537718195665228787957549)
        ·
          refine ⟨23076644323374460795484081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61537718195665228787957549 23076644323374460795484081)
          ·
            refine ⟨17307483242530845596613061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23076644323374460795484081 17307483242530845596613061)
            ·
              refine ⟨3245153107974533549364949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17307483242530845596613061 3245153107974533549364949)
              ·
                refine ⟨76058275968153130063241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3245153107974533549364949 76058275968153130063241)
                ·
                  rfl

theorem cell20_499915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_499915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499915 prefixEnd_499915 := by exact prefixLift 499915
  have htrace : WordTrace (prefixWord ++ tailWord_499915) baseStart_499915 baseEnd_499915 := by
    simpa [prefixWord, tailWord_499915, baseEnd_499915] using wordTrace_append hprefix tailTrace_499915
  have hstable : (prefixWord ++ tailWord_499915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499915).length < 2 ^ (prefixWord ++ tailWord_499915).sum := by decide
  have hdescent : baseEnd_499915 < baseStart_499915 := by decide
  rcases family_descends (prefixWord ++ tailWord_499915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499949 : List Nat := [1, 5, 1, 2, 3, 2, 6]
def baseStart_499949 : Nat := 118140960795 + 499949 * 2 ^ 59
def prefixEnd_499949 : Nat := 4983230072969 + 3 ^ 40 * 499949 * 2
def baseEnd_499949 : Nat := 25354482936767375895139

theorem tailTrace_499949 : CollatzResearch.WordTrace tailWord_499949 prefixEnd_499949 25354482936767375895139 := by
  unfold tailWord_499949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18234638065777632336502901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12156425377185088224335267 18234638065777632336502901)
  ·
    refine ⟨1709497318666653031547147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18234638065777632336502901 1709497318666653031547147)
    ·
      refine ⟨2564245977999979547320721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709497318666653031547147 2564245977999979547320721)
      ·
        refine ⟨1923184483499984660490541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2564245977999979547320721 1923184483499984660490541)
        ·
          refine ⟨721194181312494247683953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1923184483499984660490541 721194181312494247683953)
          ·
            refine ⟨540895635984370685762965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721194181312494247683953 540895635984370685762965)
            ·
              refine ⟨25354482936767375895139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 540895635984370685762965 25354482936767375895139)
              ·
                rfl

theorem cell20_499949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_499949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499949 prefixEnd_499949 := by exact prefixLift 499949
  have htrace : WordTrace (prefixWord ++ tailWord_499949) baseStart_499949 baseEnd_499949 := by
    simpa [prefixWord, tailWord_499949, baseEnd_499949] using wordTrace_append hprefix tailTrace_499949
  have hstable : (prefixWord ++ tailWord_499949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499949).length < 2 ^ (prefixWord ++ tailWord_499949).sum := by decide
  have hdescent : baseEnd_499949 < baseStart_499949 := by decide
  rcases family_descends (prefixWord ++ tailWord_499949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499953 : List Nat := [1, 2, 2, 2, 2, 1, 10]
def baseStart_499953 : Nat := 118140960795 + 499953 * 2 ^ 59
def prefixEnd_499953 : Nat := 4983230072969 + 3 ^ 40 * 499953 * 2
def baseEnd_499953 : Nat := 25354685793322238546989

theorem tailTrace_499953 : CollatzResearch.WordTrace tailWord_499953 prefixEnd_499953 25354685793322238546989 := by
  unfold tailWord_499953
  simp only [CollatzResearch.WordTrace]
  refine ⟨18234783957763141019648513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12156522638508760679765675 18234783957763141019648513)
  ·
    refine ⟨13676087968322355764736385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18234783957763141019648513 13676087968322355764736385)
    ·
      refine ⟨10257065976241766823552289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13676087968322355764736385 10257065976241766823552289)
      ·
        refine ⟨7692799482181325117664217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10257065976241766823552289 7692799482181325117664217)
        ·
          refine ⟨5769599611635993838248163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7692799482181325117664217 5769599611635993838248163)
          ·
            refine ⟨8654399417453990757372245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769599611635993838248163 8654399417453990757372245)
            ·
              refine ⟨25354685793322238546989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8654399417453990757372245 25354685793322238546989)
              ·
                rfl

theorem cell20_499953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_499953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_499953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_499953 prefixEnd_499953 := by exact prefixLift 499953
  have htrace : WordTrace (prefixWord ++ tailWord_499953) baseStart_499953 baseEnd_499953 := by
    simpa [prefixWord, tailWord_499953, baseEnd_499953] using wordTrace_append hprefix tailTrace_499953
  have hstable : (prefixWord ++ tailWord_499953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499953).length < 2 ^ (prefixWord ++ tailWord_499953).sum := by decide
  have hdescent : baseEnd_499953 < baseStart_499953 := by decide
  rcases family_descends (prefixWord ++ tailWord_499953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500007 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 3]
def baseStart_500007 : Nat := 118140960795 + 500007 * 2 ^ 59
def prefixEnd_500007 : Nat := 4983230072969 + 3 ^ 40 * 500007 * 2
def baseEnd_500007 : Nat := 228216819211315959122681

theorem tailTrace_500007 : CollatzResearch.WordTrace tailWord_500007 prefixEnd_500007 228216819211315959122681 := by
  unfold tailWord_500007
  simp only [CollatzResearch.WordTrace]
  refine ⟨18236753499567508242114275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12157835666378338828076183 18236753499567508242114275)
  ·
    refine ⟨27355130249351262363171413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18236753499567508242114275 27355130249351262363171413)
    ·
      refine ⟨320567932609585105818415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 27355130249351262363171413 320567932609585105818415)
      ·
        refine ⟨480851898914377658727623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320567932609585105818415 480851898914377658727623)
        ·
          refine ⟨721277848371566488091435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480851898914377658727623 721277848371566488091435)
          ·
            refine ⟨1081916772557349732137153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721277848371566488091435 1081916772557349732137153)
            ·
              refine ⟨811437579418012299102865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081916772557349732137153 811437579418012299102865)
              ·
                refine ⟨608578184563509224327149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811437579418012299102865 608578184563509224327149)
                ·
                  refine ⟨228216819211315959122681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608578184563509224327149 228216819211315959122681)
                  ·
                    rfl

theorem cell20_500007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 3].length) (baseStart_500007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500007 prefixEnd_500007 := by exact prefixLift 500007
  have htrace : WordTrace (prefixWord ++ tailWord_500007) baseStart_500007 baseEnd_500007 := by
    simpa [prefixWord, tailWord_500007, baseEnd_500007] using wordTrace_append hprefix tailTrace_500007
  have hstable : (prefixWord ++ tailWord_500007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500007).length < 2 ^ (prefixWord ++ tailWord_500007).sum := by decide
  have hdescent : baseEnd_500007 < baseStart_500007 := by decide
  rcases family_descends (prefixWord ++ tailWord_500007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500008 : List Nat := [2, 1, 5, 1, 3, 8]
def baseStart_500008 : Nat := 118140960795 + 500008 * 2 ^ 59
def prefixEnd_500008 : Nat := 4983230072969 + 3 ^ 40 * 500008 * 2
def baseEnd_500008 : Nat := 8452491690317200003309

theorem tailTrace_500008 : CollatzResearch.WordTrace tailWord_500008 prefixEnd_500008 8452491690317200003309 := by
  unfold tailWord_500008
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118394986281942706450339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12157859981709256941933785 9118394986281942706450339)
  ·
    refine ⟨13677592479422914059675509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9118394986281942706450339 13677592479422914059675509)
    ·
      refine ⟨1282274294945898193094579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13677592479422914059675509 1282274294945898193094579)
      ·
        refine ⟨1923411442418847289641869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282274294945898193094579 1923411442418847289641869)
        ·
          refine ⟨721279290907067733615701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1923411442418847289641869 721279290907067733615701)
          ·
            refine ⟨8452491690317200003309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 721279290907067733615701 8452491690317200003309)
            ·
              rfl

theorem cell20_500008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 8].length) (baseStart_500008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500008 prefixEnd_500008 := by exact prefixLift 500008
  have htrace : WordTrace (prefixWord ++ tailWord_500008) baseStart_500008 baseEnd_500008 := by
    simpa [prefixWord, tailWord_500008, baseEnd_500008] using wordTrace_append hprefix tailTrace_500008
  have hstable : (prefixWord ++ tailWord_500008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500008).length < 2 ^ (prefixWord ++ tailWord_500008).sum := by decide
  have hdescent : baseEnd_500008 < baseStart_500008 := by decide
  rcases family_descends (prefixWord ++ tailWord_500008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500014 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_500014 : Nat := 118140960795 + 500014 * 2 ^ 59
def prefixEnd_500014 : Nat := 4983230072969 + 3 ^ 40 * 500014 * 2
def baseEnd_500014 : Nat := 228220014202055045889319

theorem tailTrace_500014 : CollatzResearch.WordTrace tailWord_500014 prefixEnd_500014 228220014202055045889319 := by
  unfold tailWord_500014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2279626101317768554702387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12158005873694765625079397 2279626101317768554702387)
  ·
    refine ⟨3419439151976652832053581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2279626101317768554702387 3419439151976652832053581)
    ·
      refine ⟨1282289681991244812020093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3419439151976652832053581 1282289681991244812020093)
      ·
        refine ⟨480858630746716804507535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1282289681991244812020093 480858630746716804507535)
        ·
          refine ⟨721287946120075206761303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480858630746716804507535 721287946120075206761303)
          ·
            refine ⟨1081931919180112810141955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721287946120075206761303 1081931919180112810141955)
            ·
              refine ⟨1622897878770169215212933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081931919180112810141955 1622897878770169215212933)
              ·
                refine ⟨304293352269406727852425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1622897878770169215212933 304293352269406727852425)
                ·
                  refine ⟨228220014202055045889319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304293352269406727852425 228220014202055045889319)
                  ·
                    rfl

theorem cell20_500014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_500014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500014 prefixEnd_500014 := by exact prefixLift 500014
  have htrace : WordTrace (prefixWord ++ tailWord_500014) baseStart_500014 baseEnd_500014 := by
    simpa [prefixWord, tailWord_500014, baseEnd_500014] using wordTrace_append hprefix tailTrace_500014
  have hstable : (prefixWord ++ tailWord_500014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500014).length < 2 ^ (prefixWord ++ tailWord_500014).sum := by decide
  have hdescent : baseEnd_500014 < baseStart_500014 := by decide
  rcases family_descends (prefixWord ++ tailWord_500014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500015 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_500015 : Nat := 118140960795 + 500015 * 2 ^ 59
def prefixEnd_500015 : Nat := 4983230072969 + 3 ^ 40 * 500015 * 2
def baseEnd_500015 : Nat := 228220470629303486855981

theorem tailTrace_500015 : CollatzResearch.WordTrace tailWord_500015 prefixEnd_500015 228220470629303486855981 := by
  unfold tailWord_500015
  simp only [CollatzResearch.WordTrace]
  refine ⟨18237045283538525608405499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12158030189025683738936999 18237045283538525608405499)
  ·
    refine ⟨27355567925307788412608249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18237045283538525608405499 27355567925307788412608249)
    ·
      refine ⟨20516675943980841309456187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27355567925307788412608249 20516675943980841309456187)
      ·
        refine ⟨30775013915971261964184281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20516675943980841309456187 30775013915971261964184281)
        ·
          refine ⟨23081260436978446473138211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30775013915971261964184281 23081260436978446473138211)
          ·
            refine ⟨34621890655467669709707317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23081260436978446473138211 34621890655467669709707317)
            ·
              refine ⟨3245802248950094035285061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34621890655467669709707317 3245802248950094035285061)
              ·
                refine ⟨608587921678142631615949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3245802248950094035285061 608587921678142631615949)
                ·
                  refine ⟨228220470629303486855981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608587921678142631615949 228220470629303486855981)
                  ·
                    rfl

theorem cell20_500015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_500015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500015 prefixEnd_500015 := by exact prefixLift 500015
  have htrace : WordTrace (prefixWord ++ tailWord_500015) baseStart_500015 baseEnd_500015 := by
    simpa [prefixWord, tailWord_500015, baseEnd_500015] using wordTrace_append hprefix tailTrace_500015
  have hstable : (prefixWord ++ tailWord_500015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500015).length < 2 ^ (prefixWord ++ tailWord_500015).sum := by decide
  have hdescent : baseEnd_500015 < baseStart_500015 := by decide
  rcases family_descends (prefixWord ++ tailWord_500015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500025 : List Nat := [1, 2, 1, 6, 1, 3, 1, 5]
def baseStart_500025 : Nat := 118140960795 + 500025 * 2 ^ 59
def prefixEnd_500025 : Nat := 4983230072969 + 3 ^ 40 * 500025 * 2
def baseEnd_500025 : Nat := 76075011633929298840869

theorem tailTrace_500025 : CollatzResearch.WordTrace tailWord_500025 prefixEnd_500025 76075011633929298840869 := by
  unfold tailWord_500025
  simp only [CollatzResearch.WordTrace]
  refine ⟨18237410013502297316269529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12158273342334864877513019 18237410013502297316269529)
  ·
    refine ⟨13678057510126722987202147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18237410013502297316269529 13678057510126722987202147)
    ·
      refine ⟨20517086265190084480803221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13678057510126722987202147 20517086265190084480803221)
      ·
        refine ⟨961738418680785210037651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20517086265190084480803221 961738418680785210037651)
        ·
          refine ⟨1442607628021177815056477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961738418680785210037651 1442607628021177815056477)
          ·
            refine ⟨540977860507941680646179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1442607628021177815056477 540977860507941680646179)
            ·
              refine ⟨811466790761912520969269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540977860507941680646179 811466790761912520969269)
              ·
                refine ⟨76075011633929298840869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 811466790761912520969269 76075011633929298840869)
                ·
                  rfl

theorem cell20_500025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_500025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500025 prefixEnd_500025 := by exact prefixLift 500025
  have htrace : WordTrace (prefixWord ++ tailWord_500025) baseStart_500025 baseEnd_500025 := by
    simpa [prefixWord, tailWord_500025, baseEnd_500025] using wordTrace_append hprefix tailTrace_500025
  have hstable : (prefixWord ++ tailWord_500025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500025).length < 2 ^ (prefixWord ++ tailWord_500025).sum := by decide
  have hdescent : baseEnd_500025 < baseStart_500025 := by decide
  rcases family_descends (prefixWord ++ tailWord_500025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500067 : List Nat := [1, 1, 1, 5, 2, 1, 9]
def baseStart_500067 : Nat := 118140960795 + 500067 * 2 ^ 59
def prefixEnd_500067 : Nat := 4983230072969 + 3 ^ 40 * 500067 * 2
def baseEnd_500067 : Nat := 25360467205135824124715

theorem tailTrace_500067 : CollatzResearch.WordTrace tailWord_500067 prefixEnd_500067 25360467205135824124715 := by
  unfold tailWord_500067
  simp only [CollatzResearch.WordTrace]
  refine ⟨18238941879350138489298455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12159294586233425659532303 18238941879350138489298455)
  ·
    refine ⟨27358412819025207733947683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18238941879350138489298455 27358412819025207733947683)
    ·
      refine ⟨41037619228537811600921525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27358412819025207733947683 41037619228537811600921525)
      ·
        refine ⟨3847276802675419837586393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41037619228537811600921525 3847276802675419837586393)
        ·
          refine ⟨2885457602006564878189795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3847276802675419837586393 2885457602006564878189795)
          ·
            refine ⟨4328186403009847317284693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885457602006564878189795 4328186403009847317284693)
            ·
              refine ⟨25360467205135824124715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4328186403009847317284693 25360467205135824124715)
              ·
                rfl

theorem cell20_500067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_500067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500067 prefixEnd_500067 := by exact prefixLift 500067
  have htrace : WordTrace (prefixWord ++ tailWord_500067) baseStart_500067 baseEnd_500067 := by
    simpa [prefixWord, tailWord_500067, baseEnd_500067] using wordTrace_append hprefix tailTrace_500067
  have hstable : (prefixWord ++ tailWord_500067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500067).length < 2 ^ (prefixWord ++ tailWord_500067).sum := by decide
  have hdescent : baseEnd_500067 < baseStart_500067 := by decide
  rcases family_descends (prefixWord ++ tailWord_500067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500077 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_500077 : Nat := 118140960795 + 500077 * 2 ^ 59
def prefixEnd_500077 : Nat := 4983230072969 + 3 ^ 40 * 500077 * 2
def baseEnd_500077 : Nat := 228248769118706826789061

theorem tailTrace_500077 : CollatzResearch.WordTrace tailWord_500077 prefixEnd_500077 228248769118706826789061 := by
  unfold tailWord_500077
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239306609313910197162485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12159537739542606798108323 18239306609313910197162485)
  ·
    refine ⟨1709934994623179080983983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18239306609313910197162485 1709934994623179080983983)
    ·
      refine ⟨2564902491934768621475975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709934994623179080983983 2564902491934768621475975)
      ·
        refine ⟨3847353737902152932213963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564902491934768621475975 3847353737902152932213963)
        ·
          refine ⟨5771030606853229398320945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847353737902152932213963 5771030606853229398320945)
          ·
            refine ⟨4328272955139922048740709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771030606853229398320945 4328272955139922048740709)
            ·
              refine ⟨811551179088735384138883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4328272955139922048740709 811551179088735384138883)
              ·
                refine ⟨1217326768633103076208325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811551179088735384138883 1217326768633103076208325)
                ·
                  refine ⟨228248769118706826789061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217326768633103076208325 228248769118706826789061)
                  ·
                    rfl

theorem cell20_500077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_500077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500077 prefixEnd_500077 := by exact prefixLift 500077
  have htrace : WordTrace (prefixWord ++ tailWord_500077) baseStart_500077 baseEnd_500077 := by
    simpa [prefixWord, tailWord_500077, baseEnd_500077] using wordTrace_append hprefix tailTrace_500077
  have hstable : (prefixWord ++ tailWord_500077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500077).length < 2 ^ (prefixWord ++ tailWord_500077).sum := by decide
  have hdescent : baseEnd_500077 < baseStart_500077 := by decide
  rcases family_descends (prefixWord ++ tailWord_500077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500122 : List Nat := [3, 1, 1, 4, 1, 4, 6]
def baseStart_500122 : Nat := 118140960795 + 500122 * 2 ^ 59
def prefixEnd_500122 : Nat := 4983230072969 + 3 ^ 40 * 500122 * 2
def baseEnd_500122 : Nat := 25363256482765185587653

theorem tailTrace_500122 : CollatzResearch.WordTrace tailWord_500122 prefixEnd_500122 25363256482765185587653 := by
  unfold tailWord_500122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560236973537720720637655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12160631929433921921700413 4560236973537720720637655)
  ·
    refine ⟨6840355460306581080956483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4560236973537720720637655 6840355460306581080956483)
    ·
      refine ⟨10260533190459871621434725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840355460306581080956483 10260533190459871621434725)
      ·
        refine ⟨1923849973211225929019011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10260533190459871621434725 1923849973211225929019011)
        ·
          refine ⟨2885774959816838893528517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923849973211225929019011 2885774959816838893528517)
          ·
            refine ⟨541082804965657292536597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2885774959816838893528517 541082804965657292536597)
            ·
              refine ⟨25363256482765185587653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 541082804965657292536597 25363256482765185587653)
              ·
                rfl

theorem cell20_500122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 6].length) (baseStart_500122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500122 prefixEnd_500122 := by exact prefixLift 500122
  have htrace : WordTrace (prefixWord ++ tailWord_500122) baseStart_500122 baseEnd_500122 := by
    simpa [prefixWord, tailWord_500122, baseEnd_500122] using wordTrace_append hprefix tailTrace_500122
  have hstable : (prefixWord ++ tailWord_500122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500122).length < 2 ^ (prefixWord ++ tailWord_500122).sum := by decide
  have hdescent : baseEnd_500122 < baseStart_500122 := by decide
  rcases family_descends (prefixWord ++ tailWord_500122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500138 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_500138 : Nat := 118140960795 + 500138 * 2 ^ 59
def prefixEnd_500138 : Nat := 4983230072969 + 3 ^ 40 * 500138 * 2
def baseEnd_500138 : Nat := 228276611180861725755479

theorem tailTrace_500138 : CollatzResearch.WordTrace tailWord_500138 prefixEnd_500138 228276611180861725755479 := by
  unfold tailWord_500138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560382865523229403783267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12161020974728611743422045 4560382865523229403783267)
  ·
    refine ⟨6840574298284844105674901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4560382865523229403783267 6840574298284844105674901)
    ·
      refine ⟨320651920232102067453511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6840574298284844105674901 320651920232102067453511)
      ·
        refine ⟨480977880348153101180267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320651920232102067453511 480977880348153101180267)
        ·
          refine ⟨721466820522229651770401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480977880348153101180267 721466820522229651770401)
          ·
            refine ⟨541100115391672238827801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721466820522229651770401 541100115391672238827801)
            ·
              refine ⟨405825086543754179120851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541100115391672238827801 405825086543754179120851)
              ·
                refine ⟨608737629815631268681277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405825086543754179120851 608737629815631268681277)
                ·
                  refine ⟨228276611180861725755479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608737629815631268681277 228276611180861725755479)
                  ·
                    rfl

theorem cell20_500138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_500138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500138 prefixEnd_500138 := by exact prefixLift 500138
  have htrace : WordTrace (prefixWord ++ tailWord_500138) baseStart_500138 baseEnd_500138 := by
    simpa [prefixWord, tailWord_500138, baseEnd_500138] using wordTrace_append hprefix tailTrace_500138
  have hstable : (prefixWord ++ tailWord_500138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500138).length < 2 ^ (prefixWord ++ tailWord_500138).sum := by decide
  have hdescent : baseEnd_500138 < baseStart_500138 := by decide
  rcases family_descends (prefixWord ++ tailWord_500138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500181 : List Nat := [1, 3, 2, 3, 1, 10]
def baseStart_500181 : Nat := 118140960795 + 500181 * 2 ^ 59
def prefixEnd_500181 : Nat := 4983230072969 + 3 ^ 40 * 500181 * 2
def baseEnd_500181 : Nat := 8455416205649803234147

theorem tailTrace_500181 : CollatzResearch.WordTrace tailWord_500181 prefixEnd_500181 8455416205649803234147 := by
  unfold tailWord_500181
  simp only [CollatzResearch.WordTrace]
  refine ⟨18243099800937135958948397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12162066533958090639298931 18243099800937135958948397)
  ·
    refine ⟨6841162425351425984605649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18243099800937135958948397 6841162425351425984605649)
    ·
      refine ⟨5130871819013569488454237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6841162425351425984605649 5130871819013569488454237)
      ·
        refine ⟨1924076932130088558170339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5130871819013569488454237 1924076932130088558170339)
        ·
          refine ⟨2886115398195132837255509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924076932130088558170339 2886115398195132837255509)
          ·
            refine ⟨8455416205649803234147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2886115398195132837255509 8455416205649803234147)
            ·
              rfl

theorem cell20_500181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 10].length) (baseStart_500181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500181 prefixEnd_500181 := by exact prefixLift 500181
  have htrace : WordTrace (prefixWord ++ tailWord_500181) baseStart_500181 baseEnd_500181 := by
    simpa [prefixWord, tailWord_500181, baseEnd_500181] using wordTrace_append hprefix tailTrace_500181
  have hstable : (prefixWord ++ tailWord_500181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500181).length < 2 ^ (prefixWord ++ tailWord_500181).sum := by decide
  have hdescent : baseEnd_500181 < baseStart_500181 := by decide
  rcases family_descends (prefixWord ++ tailWord_500181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500229 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 2]
def baseStart_500229 : Nat := 118140960795 + 500229 * 2 ^ 59
def prefixEnd_500229 : Nat := 4983230072969 + 3 ^ 40 * 500229 * 2
def baseEnd_500229 : Nat := 228318146060469853721773

theorem tailTrace_500229 : CollatzResearch.WordTrace tailWord_500229 prefixEnd_500229 228318146060469853721773 := by
  unfold tailWord_500229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18244850504763240156695741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12163233669842160104463827 18244850504763240156695741)
  ·
    refine ⟨6841818939286215058760903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18244850504763240156695741 6841818939286215058760903)
    ·
      refine ⟨10262728408929322588141355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841818939286215058760903 10262728408929322588141355)
      ·
        refine ⟨15394092613393983882212033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10262728408929322588141355 15394092613393983882212033)
        ·
          refine ⟨11545569460045487911659025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15394092613393983882212033 11545569460045487911659025)
          ·
            refine ⟨8659177095034115933744269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11545569460045487911659025 8659177095034115933744269)
            ·
              refine ⟨3247191410637793475154101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8659177095034115933744269 3247191410637793475154101)
              ·
                refine ⟨304424194747293138295697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3247191410637793475154101 304424194747293138295697)
                ·
                  refine ⟨228318146060469853721773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304424194747293138295697 228318146060469853721773)
                  ·
                    rfl

theorem cell20_500229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_500229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500229 prefixEnd_500229 := by exact prefixLift 500229
  have htrace : WordTrace (prefixWord ++ tailWord_500229) baseStart_500229 baseEnd_500229 := by
    simpa [prefixWord, tailWord_500229, baseEnd_500229] using wordTrace_append hprefix tailTrace_500229
  have hstable : (prefixWord ++ tailWord_500229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500229).length < 2 ^ (prefixWord ++ tailWord_500229).sum := by decide
  have hdescent : baseEnd_500229 < baseStart_500229 := by decide
  rcases family_descends (prefixWord ++ tailWord_500229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500250 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_500250 : Nat := 118140960795 + 500250 * 2 ^ 59
def prefixEnd_500250 : Nat := 4983230072969 + 3 ^ 40 * 500250 * 2
def baseEnd_500250 : Nat := 228327731032687114021687

theorem tailTrace_500250 : CollatzResearch.WordTrace tailWord_500250 prefixEnd_500250 228327731032687114021687 := by
  unfold tailWord_500250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561404109421790185802551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12163744291791440495473469 4561404109421790185802551)
  ·
    refine ⟨6842106164132685278703827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561404109421790185802551 6842106164132685278703827)
    ·
      refine ⟨10263159246199027918055741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842106164132685278703827 10263159246199027918055741)
      ·
        refine ⟨3848684717324635469270903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10263159246199027918055741 3848684717324635469270903)
        ·
          refine ⟨5773027075986953203906355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848684717324635469270903 5773027075986953203906355)
          ·
            refine ⟨8659540613980429805859533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773027075986953203906355 8659540613980429805859533)
            ·
              refine ⟨3247327730242661177197325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8659540613980429805859533 3247327730242661177197325)
              ·
                refine ⟨1217747898840997941448997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3247327730242661177197325 1217747898840997941448997)
                ·
                  refine ⟨228327731032687114021687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217747898840997941448997 228327731032687114021687)
                  ·
                    rfl

theorem cell20_500250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_500250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500250 prefixEnd_500250 := by exact prefixLift 500250
  have htrace : WordTrace (prefixWord ++ tailWord_500250) baseStart_500250 baseEnd_500250 := by
    simpa [prefixWord, tailWord_500250, baseEnd_500250] using wordTrace_append hprefix tailTrace_500250
  have hstable : (prefixWord ++ tailWord_500250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500250).length < 2 ^ (prefixWord ++ tailWord_500250).sum := by decide
  have hdescent : baseEnd_500250 < baseStart_500250 := by decide
  rcases family_descends (prefixWord ++ tailWord_500250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500257 : List Nat := [1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_500257 : Nat := 118140960795 + 500257 * 2 ^ 59
def prefixEnd_500257 : Nat := 4983230072969 + 3 ^ 40 * 500257 * 2
def baseEnd_500257 : Nat := 76110308674475400262775

theorem tailTrace_500257 : CollatzResearch.WordTrace tailWord_500257 prefixEnd_500257 76110308674475400262775 := by
  unfold tailWord_500257
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245871748661800938715025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12163914499107867292476683 18245871748661800938715025)
  ·
    refine ⟨13684403811496350704036269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18245871748661800938715025 13684403811496350704036269)
    ·
      refine ⟨5131651429311131514013601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13684403811496350704036269 5131651429311131514013601)
      ·
        refine ⟨3848738571983348635510201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5131651429311131514013601 3848738571983348635510201)
        ·
          refine ⟨2886553928987511476632651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848738571983348635510201 2886553928987511476632651)
          ·
            refine ⟨4329830893481267214948977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886553928987511476632651 4329830893481267214948977)
            ·
              refine ⟨3247373170110950411211733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329830893481267214948977 3247373170110950411211733)
              ·
                refine ⟨76110308674475400262775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3247373170110950411211733 76110308674475400262775)
                ·
                  rfl

theorem cell20_500257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_500257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500257 prefixEnd_500257 := by exact prefixLift 500257
  have htrace : WordTrace (prefixWord ++ tailWord_500257) baseStart_500257 baseEnd_500257 := by
    simpa [prefixWord, tailWord_500257, baseEnd_500257] using wordTrace_append hprefix tailTrace_500257
  have hstable : (prefixWord ++ tailWord_500257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500257).length < 2 ^ (prefixWord ++ tailWord_500257).sum := by decide
  have hdescent : baseEnd_500257 < baseStart_500257 := by decide
  rcases family_descends (prefixWord ++ tailWord_500257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500270 : List Nat := [4, 1, 3, 1, 3, 2, 2, 4]
def baseStart_500270 : Nat := 118140960795 + 500270 * 2 ^ 59
def prefixEnd_500270 : Nat := 4983230072969 + 3 ^ 40 * 500270 * 2
def baseEnd_500270 : Nat := 76112286525885311118313

theorem tailTrace_500270 : CollatzResearch.WordTrace tailWord_500270 prefixEnd_500270 76112286525885311118313 := by
  unfold tailWord_500270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280793237201838019867283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12164230598409802772625509 2280793237201838019867283)
  ·
    refine ⟨3421189855802757029800925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2280793237201838019867283 3421189855802757029800925)
    ·
      refine ⟨1282946195926033886175347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3421189855802757029800925 1282946195926033886175347)
      ·
        refine ⟨1924419293889050829263021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282946195926033886175347 1924419293889050829263021)
        ·
          refine ⟨721657235208394060973633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1924419293889050829263021 721657235208394060973633)
          ·
            refine ⟨541242926406295545730225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721657235208394060973633 541242926406295545730225)
            ·
              refine ⟨405932194804721659297669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541242926406295545730225 405932194804721659297669)
              ·
                refine ⟨76112286525885311118313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405932194804721659297669 76112286525885311118313)
                ·
                  rfl

theorem cell20_500270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_500270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500270 prefixEnd_500270 := by exact prefixLift 500270
  have htrace : WordTrace (prefixWord ++ tailWord_500270) baseStart_500270 baseEnd_500270 := by
    simpa [prefixWord, tailWord_500270, baseEnd_500270] using wordTrace_append hprefix tailTrace_500270
  have hstable : (prefixWord ++ tailWord_500270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500270).length < 2 ^ (prefixWord ++ tailWord_500270).sum := by decide
  have hdescent : baseEnd_500270 < baseStart_500270 := by decide
  rcases family_descends (prefixWord ++ tailWord_500270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500274 : List Nat := [3, 2, 1, 1, 2, 1, 6, 4]
def baseStart_500274 : Nat := 118140960795 + 500274 * 2 ^ 59
def prefixEnd_500274 : Nat := 4983230072969 + 3 ^ 40 * 500274 * 2
def baseEnd_500274 : Nat := 76112895095549899073863

theorem tailTrace_500274 : CollatzResearch.WordTrace tailWord_500274 prefixEnd_500274 76112895095549899073863 := by
  unfold tailWord_500274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561622947400053210520969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12164327859733475228055917 4561622947400053210520969)
  ·
    refine ⟨3421217210550039907890727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4561622947400053210520969 3421217210550039907890727)
    ·
      refine ⟨5131825815825059861836091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421217210550039907890727 5131825815825059861836091)
      ·
        refine ⟨7697738723737589792754137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131825815825059861836091 7697738723737589792754137)
        ·
          refine ⟨5773304042803192344565603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697738723737589792754137 5773304042803192344565603)
          ·
            refine ⟨8659956064204788516848405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773304042803192344565603 8659956064204788516848405)
            ·
              refine ⟨405935440509599461727269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8659956064204788516848405 405935440509599461727269)
              ·
                refine ⟨76112895095549899073863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405935440509599461727269 76112895095549899073863)
                ·
                  rfl

theorem cell20_500274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_500274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500274 prefixEnd_500274 := by exact prefixLift 500274
  have htrace : WordTrace (prefixWord ++ tailWord_500274) baseStart_500274 baseEnd_500274 := by
    simpa [prefixWord, tailWord_500274, baseEnd_500274] using wordTrace_append hprefix tailTrace_500274
  have hstable : (prefixWord ++ tailWord_500274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500274).length < 2 ^ (prefixWord ++ tailWord_500274).sum := by decide
  have hdescent : baseEnd_500274 < baseStart_500274 := by decide
  rcases family_descends (prefixWord ++ tailWord_500274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500284 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 2]
def baseStart_500284 : Nat := 118140960795 + 500284 * 2 ^ 59
def prefixEnd_500284 : Nat := 4983230072969 + 3 ^ 40 * 500284 * 2
def baseEnd_500284 : Nat := 228343249559134106888215

theorem tailTrace_500284 : CollatzResearch.WordTrace tailWord_500284 prefixEnd_500284 228343249559134106888215 := by
  unfold tailWord_500284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9123428259781992274973953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12164571013042656366631937 9123428259781992274973953)
  ·
    refine ⟨6842571194836494206230465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9123428259781992274973953 6842571194836494206230465)
    ·
      refine ⟨5131928396127370654672849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6842571194836494206230465 5131928396127370654672849)
      ·
        refine ⟨3848946297095527991004637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5131928396127370654672849 3848946297095527991004637)
        ·
          refine ⟨1443354861410822996626739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3848946297095527991004637 1443354861410822996626739)
          ·
            refine ⟨2165032292116234494940109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443354861410822996626739 2165032292116234494940109)
            ·
              refine ⟨811887109543587935602541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2165032292116234494940109 811887109543587935602541)
              ·
                refine ⟨304457666078845475850953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811887109543587935602541 304457666078845475850953)
                ·
                  refine ⟨228343249559134106888215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304457666078845475850953 228343249559134106888215)
                  ·
                    rfl

theorem cell20_500284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_500284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500284 prefixEnd_500284 := by exact prefixLift 500284
  have htrace : WordTrace (prefixWord ++ tailWord_500284) baseStart_500284 baseEnd_500284 := by
    simpa [prefixWord, tailWord_500284, baseEnd_500284] using wordTrace_append hprefix tailTrace_500284
  have hstable : (prefixWord ++ tailWord_500284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500284).length < 2 ^ (prefixWord ++ tailWord_500284).sum := by decide
  have hdescent : baseEnd_500284 < baseStart_500284 := by decide
  rcases family_descends (prefixWord ++ tailWord_500284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500295 : List Nat := [1, 1, 4, 1, 4, 1, 8]
def baseStart_500295 : Nat := 118140960795 + 500295 * 2 ^ 59
def prefixEnd_500295 : Nat := 4983230072969 + 3 ^ 40 * 500295 * 2
def baseEnd_500295 : Nat := 25372030028762995280167

theorem tailTrace_500295 : CollatzResearch.WordTrace tailWord_500295 prefixEnd_500295 25372030028762995280167 := by
  unfold tailWord_500295
  simp only [CollatzResearch.WordTrace]
  refine ⟨18247257722524133428598339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12164838481682755619065559 18247257722524133428598339)
  ·
    refine ⟨27370886583786200142897509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18247257722524133428598339 27370886583786200142897509)
    ·
      refine ⟨5132041234459912526793283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27370886583786200142897509 5132041234459912526793283)
      ·
        refine ⟨7698061851689868790189925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132041234459912526793283 7698061851689868790189925)
        ·
          refine ⟨1443386597191850398160611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7698061851689868790189925 1443386597191850398160611)
          ·
            refine ⟨2165079895787775597240917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443386597191850398160611 2165079895787775597240917)
            ·
              refine ⟨25372030028762995280167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2165079895787775597240917 25372030028762995280167)
              ·
                rfl

theorem cell20_500295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_500295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500295 prefixEnd_500295 := by exact prefixLift 500295
  have htrace : WordTrace (prefixWord ++ tailWord_500295) baseStart_500295 baseEnd_500295 := by
    simpa [prefixWord, tailWord_500295, baseEnd_500295] using wordTrace_append hprefix tailTrace_500295
  have hstable : (prefixWord ++ tailWord_500295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500295).length < 2 ^ (prefixWord ++ tailWord_500295).sum := by decide
  have hdescent : baseEnd_500295 < baseStart_500295 := by decide
  rcases family_descends (prefixWord ++ tailWord_500295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500305 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 4]
def baseStart_500305 : Nat := 118140960795 + 500305 * 2 ^ 59
def prefixEnd_500305 : Nat := 4983230072969 + 3 ^ 40 * 500305 * 2
def baseEnd_500305 : Nat := 228352834531351367188129

theorem tailTrace_500305 : CollatzResearch.WordTrace tailWord_500305 prefixEnd_500305 228352834531351367188129 := by
  unfold tailWord_500305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18247622452487905136462369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12165081634991936757641579 18247622452487905136462369)
  ·
    refine ⟨13685716839365928852346777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18247622452487905136462369 13685716839365928852346777)
    ·
      refine ⟨10264287629524446639260083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13685716839365928852346777 10264287629524446639260083)
      ·
        refine ⟨15396431444286669958890125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264287629524446639260083 15396431444286669958890125)
        ·
          refine ⟨5773661791607501234583797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15396431444286669958890125 5773661791607501234583797)
          ·
            refine ⟨541280792963203240742231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5773661791607501234583797 541280792963203240742231)
            ·
              refine ⟨811921189444804861113347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541280792963203240742231 811921189444804861113347)
              ·
                refine ⟨1217881784167207291670021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811921189444804861113347 1217881784167207291670021)
                ·
                  refine ⟨228352834531351367188129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1217881784167207291670021 228352834531351367188129)
                  ·
                    rfl

theorem cell20_500305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_500305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500305 prefixEnd_500305 := by exact prefixLift 500305
  have htrace : WordTrace (prefixWord ++ tailWord_500305) baseStart_500305 baseEnd_500305 := by
    simpa [prefixWord, tailWord_500305, baseEnd_500305] using wordTrace_append hprefix tailTrace_500305
  have hstable : (prefixWord ++ tailWord_500305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500305).length < 2 ^ (prefixWord ++ tailWord_500305).sum := by decide
  have hdescent : baseEnd_500305 < baseStart_500305 := by decide
  rcases family_descends (prefixWord ++ tailWord_500305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500347 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_500347 : Nat := 118140960795 + 500347 * 2 ^ 59
def prefixEnd_500347 : Nat := 4983230072969 + 3 ^ 40 * 500347 * 2
def baseEnd_500347 : Nat := 228372004475785887787957

theorem tailTrace_500347 : CollatzResearch.WordTrace tailWord_500347 prefixEnd_500347 228372004475785887787957 := by
  unfold tailWord_500347
  simp only [CollatzResearch.WordTrace]
  refine ⟨18249154318335746309491295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12166102878890497539660863 18249154318335746309491295)
  ·
    refine ⟨27373731477503619464236943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18249154318335746309491295 27373731477503619464236943)
    ·
      refine ⟨41060597216255429196355415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27373731477503619464236943 41060597216255429196355415)
      ·
        refine ⟨61590895824383143794533123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41060597216255429196355415 61590895824383143794533123)
        ·
          refine ⟨92386343736574715691799685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61590895824383143794533123 92386343736574715691799685)
          ·
            refine ⟨17322439450607759192212441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92386343736574715691799685 17322439450607759192212441)
            ·
              refine ⟨12991829587955819394159331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17322439450607759192212441 12991829587955819394159331)
              ·
                refine ⟨19487744381933729091238997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12991829587955819394159331 19487744381933729091238997)
                ·
                  refine ⟨228372004475785887787957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19487744381933729091238997 228372004475785887787957)
                  ·
                    rfl

theorem cell20_500347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_500347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500347 prefixEnd_500347 := by exact prefixLift 500347
  have htrace : WordTrace (prefixWord ++ tailWord_500347) baseStart_500347 baseEnd_500347 := by
    simpa [prefixWord, tailWord_500347, baseEnd_500347] using wordTrace_append hprefix tailTrace_500347
  have hstable : (prefixWord ++ tailWord_500347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500347).length < 2 ^ (prefixWord ++ tailWord_500347).sum := by decide
  have hdescent : baseEnd_500347 < baseStart_500347 := by decide
  rcases family_descends (prefixWord ++ tailWord_500347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500357 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_500357 : Nat := 118140960795 + 500357 * 2 ^ 59
def prefixEnd_500357 : Nat := 4983230072969 + 3 ^ 40 * 500357 * 2
def baseEnd_500357 : Nat := 228376568748270297454583

theorem tailTrace_500357 : CollatzResearch.WordTrace tailWord_500357 prefixEnd_500357 228376568748270297454583 := by
  unfold tailWord_500357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18249519048299518017355325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12166346032199678678236883 18249519048299518017355325)
  ·
    refine ⟨6843569643112319256508247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18249519048299518017355325 6843569643112319256508247)
    ·
      refine ⟨10265354464668478884762371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843569643112319256508247 10265354464668478884762371)
      ·
        refine ⟨15398031697002718327143557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10265354464668478884762371 15398031697002718327143557)
        ·
          refine ⟨2887130943188009686339417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15398031697002718327143557 2887130943188009686339417)
          ·
            refine ⟨2165348207391007264754563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887130943188009686339417 2165348207391007264754563)
            ·
              refine ⟨3248022311086510897131845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165348207391007264754563 3248022311086510897131845)
              ·
                refine ⟨609004183328720793212221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3248022311086510897131845 609004183328720793212221)
                ·
                  refine ⟨228376568748270297454583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609004183328720793212221 228376568748270297454583)
                  ·
                    rfl

theorem cell20_500357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_500357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500357 prefixEnd_500357 := by exact prefixLift 500357
  have htrace : WordTrace (prefixWord ++ tailWord_500357) baseStart_500357 baseEnd_500357 := by
    simpa [prefixWord, tailWord_500357, baseEnd_500357] using wordTrace_append hprefix tailTrace_500357
  have hstable : (prefixWord ++ tailWord_500357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500357).length < 2 ^ (prefixWord ++ tailWord_500357).sum := by decide
  have hdescent : baseEnd_500357 < baseStart_500357 := by decide
  rcases family_descends (prefixWord ++ tailWord_500357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500388 : List Nat := [2, 3, 1, 2, 2, 1, 5, 4]
def baseStart_500388 : Nat := 118140960795 + 500388 * 2 ^ 59
def prefixEnd_500388 : Nat := 4983230072969 + 3 ^ 40 * 500388 * 2
def baseEnd_500388 : Nat := 76130239330990655807041

theorem tailTrace_500388 : CollatzResearch.WordTrace tailWord_500388 prefixEnd_500388 76130239330990655807041 := by
  unfold tailWord_500388
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125324855593605155866909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12167099807458140207822545 9125324855593605155866909)
  ·
    refine ⟨3421996820847601933450091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9125324855593605155866909 3421996820847601933450091)
    ·
      refine ⟨5132995231271402900175137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421996820847601933450091 5132995231271402900175137)
      ·
        refine ⟨3849746423453552175131353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5132995231271402900175137 3849746423453552175131353)
        ·
          refine ⟨2887309817590164131348515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849746423453552175131353 2887309817590164131348515)
          ·
            refine ⟨4330964726385246197022773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887309817590164131348515 4330964726385246197022773)
            ·
              refine ⟨406027943098616830970885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4330964726385246197022773 406027943098616830970885)
              ·
                refine ⟨76130239330990655807041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406027943098616830970885 76130239330990655807041)
                ·
                  rfl

theorem cell20_500388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_500388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500388 prefixEnd_500388 := by exact prefixLift 500388
  have htrace : WordTrace (prefixWord ++ tailWord_500388) baseStart_500388 baseEnd_500388 := by
    simpa [prefixWord, tailWord_500388, baseEnd_500388] using wordTrace_append hprefix tailTrace_500388
  have hstable : (prefixWord ++ tailWord_500388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500388).length < 2 ^ (prefixWord ++ tailWord_500388).sum := by decide
  have hdescent : baseEnd_500388 < baseStart_500388 := by decide
  rcases family_descends (prefixWord ++ tailWord_500388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500394 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_500394 : Nat := 118140960795 + 500394 * 2 ^ 59
def prefixEnd_500394 : Nat := 4983230072969 + 3 ^ 40 * 500394 * 2
def baseEnd_500394 : Nat := 228393456556462613221099

theorem tailTrace_500394 : CollatzResearch.WordTrace tailWord_500394 prefixEnd_500394 228393456556462613221099 := by
  unfold tailWord_500394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562717137291368334113059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12167245699443648890968157 4562717137291368334113059)
  ·
    refine ⟨6844075705937052501169589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4562717137291368334113059 6844075705937052501169589)
    ·
      refine ⟨641632097431598671984649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6844075705937052501169589 641632097431598671984649)
      ·
        refine ⟨481224073073699003988487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641632097431598671984649 481224073073699003988487)
        ·
          refine ⟨721836109610548505982731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481224073073699003988487 721836109610548505982731)
          ·
            refine ⟨1082754164415822758974097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721836109610548505982731 1082754164415822758974097)
            ·
              refine ⟨812065623311867069230573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082754164415822758974097 812065623311867069230573)
              ·
                refine ⟨304524608741950150961465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812065623311867069230573 304524608741950150961465)
                ·
                  refine ⟨228393456556462613221099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304524608741950150961465 228393456556462613221099)
                  ·
                    rfl

theorem cell20_500394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_500394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500394 prefixEnd_500394 := by exact prefixLift 500394
  have htrace : WordTrace (prefixWord ++ tailWord_500394) baseStart_500394 baseEnd_500394 := by
    simpa [prefixWord, tailWord_500394, baseEnd_500394] using wordTrace_append hprefix tailTrace_500394
  have hstable : (prefixWord ++ tailWord_500394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500394).length < 2 ^ (prefixWord ++ tailWord_500394).sum := by decide
  have hdescent : baseEnd_500394 < baseStart_500394 := by decide
  rcases family_descends (prefixWord ++ tailWord_500394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500440 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_500440 : Nat := 118140960795 + 500440 * 2 ^ 59
def prefixEnd_500440 : Nat := 4983230072969 + 3 ^ 40 * 500440 * 2
def baseEnd_500440 : Nat := 228414452209890897687577

theorem tailTrace_500440 : CollatzResearch.WordTrace tailWord_500440 prefixEnd_500440 228414452209890897687577 := by
  unfold tailWord_500440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126273153499411596313387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12168364204665882128417849 9126273153499411596313387)
  ·
    refine ⟨13689409730249117394470081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9126273153499411596313387 13689409730249117394470081)
    ·
      refine ⟨10267057297686838045852561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13689409730249117394470081 10267057297686838045852561)
      ·
        refine ⟨7700292973265128534389421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10267057297686838045852561 7700292973265128534389421)
        ·
          refine ⟨2887609864974423200396033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7700292973265128534389421 2887609864974423200396033)
          ·
            refine ⟨2165707398730817400297025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887609864974423200396033 2165707398730817400297025)
            ·
              refine ⟨1624280549048113050222769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165707398730817400297025 1624280549048113050222769)
              ·
                refine ⟨1218210411786084787667077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624280549048113050222769 1218210411786084787667077)
                ·
                  refine ⟨228414452209890897687577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1218210411786084787667077 228414452209890897687577)
                  ·
                    rfl

theorem cell20_500440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_500440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500440 prefixEnd_500440 := by exact prefixLift 500440
  have htrace : WordTrace (prefixWord ++ tailWord_500440) baseStart_500440 baseEnd_500440 := by
    simpa [prefixWord, tailWord_500440, baseEnd_500440] using wordTrace_append hprefix tailTrace_500440
  have hstable : (prefixWord ++ tailWord_500440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500440).length < 2 ^ (prefixWord ++ tailWord_500440).sum := by decide
  have hdescent : baseEnd_500440 < baseStart_500440 := by decide
  rcases family_descends (prefixWord ++ tailWord_500440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500447 : List Nat := [1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_500447 : Nat := 118140960795 + 500447 * 2 ^ 59
def prefixEnd_500447 : Nat := 4983230072969 + 3 ^ 40 * 500447 * 2
def baseEnd_500447 : Nat := 76139215733543328151405

theorem tailTrace_500447 : CollatzResearch.WordTrace tailWord_500447 prefixEnd_500447 76139215733543328151405 := by
  unfold tailWord_500447
  simp only [CollatzResearch.WordTrace]
  refine ⟨18252801617973463388131595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12168534411982308925421063 18252801617973463388131595)
  ·
    refine ⟨27379202426960195082197393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18252801617973463388131595 27379202426960195082197393)
    ·
      refine ⟨20534401820220146311648045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27379202426960195082197393 20534401820220146311648045)
      ·
        refine ⟨7700400682582554866868017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20534401820220146311648045 7700400682582554866868017)
        ·
          refine ⟨5775300511936916150151013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7700400682582554866868017 5775300511936916150151013)
          ·
            refine ⟨1082868845988171778153315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5775300511936916150151013 1082868845988171778153315)
            ·
              refine ⟨1624303268982257667229973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082868845988171778153315 1624303268982257667229973)
              ·
                refine ⟨76139215733543328151405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1624303268982257667229973 76139215733543328151405)
                ·
                  rfl

theorem cell20_500447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_500447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500447 prefixEnd_500447 := by exact prefixLift 500447
  have htrace : WordTrace (prefixWord ++ tailWord_500447) baseStart_500447 baseEnd_500447 := by
    simpa [prefixWord, tailWord_500447, baseEnd_500447] using wordTrace_append hprefix tailTrace_500447
  have hstable : (prefixWord ++ tailWord_500447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500447).length < 2 ^ (prefixWord ++ tailWord_500447).sum := by decide
  have hdescent : baseEnd_500447 < baseStart_500447 := by decide
  rcases family_descends (prefixWord ++ tailWord_500447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500457 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 2]
def baseStart_500457 : Nat := 118140960795 + 500457 * 2 ^ 59
def prefixEnd_500457 : Nat := 4983230072969 + 3 ^ 40 * 500457 * 2
def baseEnd_500457 : Nat := 228422211473114394120841

theorem tailTrace_500457 : CollatzResearch.WordTrace tailWord_500457 prefixEnd_500457 228422211473114394120841 := by
  unfold tailWord_500457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18253166347937235095995625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12168777565291490063997083 18253166347937235095995625)
  ·
    refine ⟨13689874760952926321996719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18253166347937235095995625 13689874760952926321996719)
    ·
      refine ⟨20534812141429389482995079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13689874760952926321996719 20534812141429389482995079)
      ·
        refine ⟨30802218212144084224492619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20534812141429389482995079 30802218212144084224492619)
        ·
          refine ⟨46203327318216126336738929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30802218212144084224492619 46203327318216126336738929)
          ·
            refine ⟨34652495488662094752554197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46203327318216126336738929 34652495488662094752554197)
            ·
              refine ⟨812167863015517845762989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34652495488662094752554197 812167863015517845762989)
              ·
                refine ⟨304562948630819192161121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812167863015517845762989 304562948630819192161121)
                ·
                  refine ⟨228422211473114394120841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304562948630819192161121 228422211473114394120841)
                  ·
                    rfl

theorem cell20_500457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_500457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500457 prefixEnd_500457 := by exact prefixLift 500457
  have htrace : WordTrace (prefixWord ++ tailWord_500457) baseStart_500457 baseEnd_500457 := by
    simpa [prefixWord, tailWord_500457, baseEnd_500457] using wordTrace_append hprefix tailTrace_500457
  have hstable : (prefixWord ++ tailWord_500457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500457).length < 2 ^ (prefixWord ++ tailWord_500457).sum := by decide
  have hdescent : baseEnd_500457 < baseStart_500457 := by decide
  rcases family_descends (prefixWord ++ tailWord_500457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500488 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_500488 : Nat := 118140960795 + 500488 * 2 ^ 59
def prefixEnd_500488 : Nat := 4983230072969 + 3 ^ 40 * 500488 * 2
def baseEnd_500488 : Nat := 228436360717816064087381

theorem tailTrace_500488 : CollatzResearch.WordTrace tailWord_500488 prefixEnd_500488 228436360717816064087381 := by
  unfold tailWord_500488
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127148505412463695187059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12169531340549951593582745 9127148505412463695187059)
  ·
    refine ⟨13690722758118695542780589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9127148505412463695187059 13690722758118695542780589)
    ·
      refine ⟨5134021034294510828542721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13690722758118695542780589 5134021034294510828542721)
      ·
        refine ⟨3850515775720883121407041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5134021034294510828542721 3850515775720883121407041)
        ·
          refine ⟨2887886831790662341055281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3850515775720883121407041 2887886831790662341055281)
          ·
            refine ⟨2165915123842996755791461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887886831790662341055281 2165915123842996755791461)
            ·
              refine ⟨406109085720561891710899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2165915123842996755791461 406109085720561891710899)
              ·
                refine ⟨609163628580842837566349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406109085720561891710899 609163628580842837566349)
                ·
                  refine ⟨228436360717816064087381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609163628580842837566349 228436360717816064087381)
                  ·
                    rfl

theorem cell20_500488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_500488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500488 prefixEnd_500488 := by exact prefixLift 500488
  have htrace : WordTrace (prefixWord ++ tailWord_500488) baseStart_500488 baseEnd_500488 := by
    simpa [prefixWord, tailWord_500488, baseEnd_500488] using wordTrace_append hprefix tailTrace_500488
  have hstable : (prefixWord ++ tailWord_500488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500488).length < 2 ^ (prefixWord ++ tailWord_500488).sum := by decide
  have hdescent : baseEnd_500488 < baseStart_500488 := by decide
  rcases family_descends (prefixWord ++ tailWord_500488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500499 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_500499 : Nat := 118140960795 + 500499 * 2 ^ 59
def prefixEnd_500499 : Nat := 4983230072969 + 3 ^ 40 * 500499 * 2
def baseEnd_500499 : Nat := 228441381417548914720669

theorem tailTrace_500499 : CollatzResearch.WordTrace tailWord_500499 prefixEnd_500499 228441381417548914720669 := by
  unfold tailWord_500499
  simp only [CollatzResearch.WordTrace]
  refine ⟨18254698213785076269024551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12169798809190050846016367 18254698213785076269024551)
  ·
    refine ⟨27382047320677614403536827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18254698213785076269024551 27382047320677614403536827)
    ·
      refine ⟨41073070981016421605305241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27382047320677614403536827 41073070981016421605305241)
      ·
        refine ⟨30804803235762316203978931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41073070981016421605305241 30804803235762316203978931)
        ·
          refine ⟨46207204853643474305968397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30804803235762316203978931 46207204853643474305968397)
          ·
            refine ⟨17327701820116302864738149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46207204853643474305968397 17327701820116302864738149)
            ·
              refine ⟨3248944091271806787138403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17327701820116302864738149 3248944091271806787138403)
              ·
                refine ⟨4873416136907710180707605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248944091271806787138403 4873416136907710180707605)
                ·
                  refine ⟨228441381417548914720669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4873416136907710180707605 228441381417548914720669)
                  ·
                    rfl

theorem cell20_500499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_500499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500499 prefixEnd_500499 := by exact prefixLift 500499
  have htrace : WordTrace (prefixWord ++ tailWord_500499) baseStart_500499 baseEnd_500499 := by
    simpa [prefixWord, tailWord_500499, baseEnd_500499] using wordTrace_append hprefix tailTrace_500499
  have hstable : (prefixWord ++ tailWord_500499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500499).length < 2 ^ (prefixWord ++ tailWord_500499).sum := by decide
  have hdescent : baseEnd_500499 < baseStart_500499 := by decide
  rcases family_descends (prefixWord ++ tailWord_500499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500525 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 2]
def baseStart_500525 : Nat := 118140960795 + 500525 * 2 ^ 59
def prefixEnd_500525 : Nat := 4983230072969 + 3 ^ 40 * 500525 * 2
def baseEnd_500525 : Nat := 228453248526008379853897

theorem tailTrace_500525 : CollatzResearch.WordTrace tailWord_500525 prefixEnd_500525 228453248526008379853897 := by
  unfold tailWord_500525
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255646511690882709471029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12170431007793921806314019 18255646511690882709471029)
  ·
    refine ⟨1711466860471020254012909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18255646511690882709471029 1711466860471020254012909)
    ·
      refine ⟨641800072676632595254841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1711466860471020254012909 641800072676632595254841)
      ·
        refine ⟨481350054507474446441131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641800072676632595254841 481350054507474446441131)
        ·
          refine ⟨722025081761211669661697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481350054507474446441131 722025081761211669661697)
          ·
            refine ⟨541518811320908752246273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722025081761211669661697 541518811320908752246273)
            ·
              refine ⟨406139108490681564184705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541518811320908752246273 406139108490681564184705)
              ·
                refine ⟨304604331368011173138529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406139108490681564184705 304604331368011173138529)
                ·
                  refine ⟨228453248526008379853897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304604331368011173138529 228453248526008379853897)
                  ·
                    rfl

theorem cell20_500525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_500525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500525 prefixEnd_500525 := by exact prefixLift 500525
  have htrace : WordTrace (prefixWord ++ tailWord_500525) baseStart_500525 baseEnd_500525 := by
    simpa [prefixWord, tailWord_500525, baseEnd_500525] using wordTrace_append hprefix tailTrace_500525
  have hstable : (prefixWord ++ tailWord_500525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500525).length < 2 ^ (prefixWord ++ tailWord_500525).sum := by decide
  have hdescent : baseEnd_500525 < baseStart_500525 := by decide
  rcases family_descends (prefixWord ++ tailWord_500525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500526 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_500526 : Nat := 118140960795 + 500526 * 2 ^ 59
def prefixEnd_500526 : Nat := 4983230072969 + 3 ^ 40 * 500526 * 2
def baseEnd_500526 : Nat := 228453704953256820820559

theorem tailTrace_500526 : CollatzResearch.WordTrace tailWord_500526 prefixEnd_500526 228453704953256820820559 := by
  unfold tailWord_500526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281960373085907485032179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12170455323124839920171621 2281960373085907485032179)
  ·
    refine ⟨3422940559628861227548269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281960373085907485032179 3422940559628861227548269)
    ·
      refine ⟨1283602709860822960330601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3422940559628861227548269 1283602709860822960330601)
      ·
        refine ⟨962702032395617220247951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1283602709860822960330601 962702032395617220247951)
        ·
          refine ⟨1444053048593425830371927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962702032395617220247951 1444053048593425830371927)
          ·
            refine ⟨2166079572890138745557891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444053048593425830371927 2166079572890138745557891)
            ·
              refine ⟨3249119359335208118336837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166079572890138745557891 3249119359335208118336837)
              ·
                refine ⟨609209879875351522188157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3249119359335208118336837 609209879875351522188157)
                ·
                  refine ⟨228453704953256820820559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609209879875351522188157 228453704953256820820559)
                  ·
                    rfl

theorem cell20_500526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_500526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500526 prefixEnd_500526 := by exact prefixLift 500526
  have htrace : WordTrace (prefixWord ++ tailWord_500526) baseStart_500526 baseEnd_500526 := by
    simpa [prefixWord, tailWord_500526, baseEnd_500526] using wordTrace_append hprefix tailTrace_500526
  have hstable : (prefixWord ++ tailWord_500526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500526).length < 2 ^ (prefixWord ++ tailWord_500526).sum := by decide
  have hdescent : baseEnd_500526 < baseStart_500526 := by decide
  rcases family_descends (prefixWord ++ tailWord_500526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500575 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_500575 : Nat := 118140960795 + 500575 * 2 ^ 59
def prefixEnd_500575 : Nat := 4983230072969 + 3 ^ 40 * 500575 * 2
def baseEnd_500575 : Nat := 228476069888430428187025

theorem tailTrace_500575 : CollatzResearch.WordTrace tailWord_500575 prefixEnd_500575 228476069888430428187025 := by
  unfold tailWord_500575
  simp only [CollatzResearch.WordTrace]
  refine ⟨18257470161509741248791179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12171646774339827499194119 18257470161509741248791179)
  ·
    refine ⟨27386205242264611873186769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18257470161509741248791179 27386205242264611873186769)
    ·
      refine ⟨20539653931698458904890077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27386205242264611873186769 20539653931698458904890077)
      ·
        refine ⟨7702370224386922089333779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20539653931698458904890077 7702370224386922089333779)
        ·
          refine ⟨11553555336580383134000669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702370224386922089333779 11553555336580383134000669)
          ·
            refine ⟨4332583251217643675250251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11553555336580383134000669 4332583251217643675250251)
            ·
              refine ⟨6498874876826465512875377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332583251217643675250251 6498874876826465512875377)
              ·
                refine ⟨4874156157619849134656533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498874876826465512875377 4874156157619849134656533)
                ·
                  refine ⟨228476069888430428187025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4874156157619849134656533 228476069888430428187025)
                  ·
                    rfl

theorem cell20_500575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_500575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500575 prefixEnd_500575 := by exact prefixLift 500575
  have htrace : WordTrace (prefixWord ++ tailWord_500575) baseStart_500575 baseEnd_500575 := by
    simpa [prefixWord, tailWord_500575, baseEnd_500575] using wordTrace_append hprefix tailTrace_500575
  have hstable : (prefixWord ++ tailWord_500575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500575).length < 2 ^ (prefixWord ++ tailWord_500575).sum := by decide
  have hdescent : baseEnd_500575 < baseStart_500575 := by decide
  rcases family_descends (prefixWord ++ tailWord_500575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500578 : List Nat := [3, 3, 2, 1, 3, 1, 7]
def baseStart_500578 : Nat := 118140960795 + 500578 * 2 ^ 59
def prefixEnd_500578 : Nat := 4983230072969 + 3 ^ 40 * 500578 * 2
def baseEnd_500578 : Nat := 25386382130019527898557

theorem tailTrace_500578 : CollatzResearch.WordTrace tailWord_500578 prefixEnd_500578 25386382130019527898557 := by
  unfold tailWord_500578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564394895124718190287597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12171719720332581840766925 4564394895124718190287597)
  ·
    refine ⟨1711648085671769321357849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4564394895124718190287597 1711648085671769321357849)
    ·
      refine ⟨1283736064253826991018387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1711648085671769321357849 1283736064253826991018387)
      ·
        refine ⟨1925604096380740486527581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283736064253826991018387 1925604096380740486527581)
        ·
          refine ⟨722101536142777682447843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1925604096380740486527581 722101536142777682447843)
          ·
            refine ⟨1083152304214166523671765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722101536142777682447843 1083152304214166523671765)
            ·
              refine ⟨25386382130019527898557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1083152304214166523671765 25386382130019527898557)
              ·
                rfl

theorem cell20_500578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 7].length) (baseStart_500578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500578 prefixEnd_500578 := by exact prefixLift 500578
  have htrace : WordTrace (prefixWord ++ tailWord_500578) baseStart_500578 baseEnd_500578 := by
    simpa [prefixWord, tailWord_500578, baseEnd_500578] using wordTrace_append hprefix tailTrace_500578
  have hstable : (prefixWord ++ tailWord_500578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500578).length < 2 ^ (prefixWord ++ tailWord_500578).sum := by decide
  have hdescent : baseEnd_500578 < baseStart_500578 := by decide
  rcases family_descends (prefixWord ++ tailWord_500578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500616 : List Nat := [2, 1, 3, 3, 2, 1, 4, 4]
def baseStart_500616 : Nat := 118140960795 + 500616 * 2 ^ 59
def prefixEnd_500616 : Nat := 4983230072969 + 3 ^ 40 * 500616 * 2
def baseEnd_500616 : Nat := 76164927801872169273397

theorem tailTrace_500616 : CollatzResearch.WordTrace tailWord_500616 prefixEnd_500616 76164927801872169273397 := by
  unfold tailWord_500616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129482777180602625516851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12172643702907470167355801 9129482777180602625516851)
  ·
    refine ⟨13694224165770903938275277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9129482777180602625516851 13694224165770903938275277)
    ·
      refine ⟨5135334062164088976853229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13694224165770903938275277 5135334062164088976853229)
      ·
        refine ⟨1925750273311533366319961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5135334062164088976853229 1925750273311533366319961)
        ·
          refine ⟨1444312704983650024739971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1925750273311533366319961 1444312704983650024739971)
          ·
            refine ⟨2166469057475475037109957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444312704983650024739971 2166469057475475037109957)
            ·
              refine ⟨406212948276651569458117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2166469057475475037109957 406212948276651569458117)
              ·
                refine ⟨76164927801872169273397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406212948276651569458117 76164927801872169273397)
                ·
                  rfl

theorem cell20_500616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_500616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500616 prefixEnd_500616 := by exact prefixLift 500616
  have htrace : WordTrace (prefixWord ++ tailWord_500616) baseStart_500616 baseEnd_500616 := by
    simpa [prefixWord, tailWord_500616, baseEnd_500616] using wordTrace_append hprefix tailTrace_500616
  have hstable : (prefixWord ++ tailWord_500616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500616).length < 2 ^ (prefixWord ++ tailWord_500616).sum := by decide
  have hdescent : baseEnd_500616 < baseStart_500616 := by decide
  rcases family_descends (prefixWord ++ tailWord_500616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500644 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_500644 : Nat := 118140960795 + 500644 * 2 ^ 59
def prefixEnd_500644 : Nat := 4983230072969 + 3 ^ 40 * 500644 * 2
def baseEnd_500644 : Nat := 228507563368572854886743

theorem tailTrace_500644 : CollatzResearch.WordTrace tailWord_500644 prefixEnd_500644 228507563368572854886743 := by
  unfold tailWord_500644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129993399129883016526493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12173324532173177355368657 9129993399129883016526493)
  ·
    refine ⟨3423747524673706131197435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9129993399129883016526493 3423747524673706131197435)
    ·
      refine ⟨5135621287010559196796153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3423747524673706131197435 5135621287010559196796153)
      ·
        refine ⟨3851715965257919397597115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5135621287010559196796153 3851715965257919397597115)
        ·
          refine ⟨5777573947886879096395673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851715965257919397597115 5777573947886879096395673)
          ·
            refine ⟨4333180460915159322296755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5777573947886879096395673 4333180460915159322296755)
            ·
              refine ⟨6499770691372738983445133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333180460915159322296755 6499770691372738983445133)
              ·
                refine ⟨2437414009264777118791925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6499770691372738983445133 2437414009264777118791925)
                ·
                  refine ⟨228507563368572854886743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2437414009264777118791925 228507563368572854886743)
                  ·
                    rfl

theorem cell20_500644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_500644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500644 prefixEnd_500644 := by exact prefixLift 500644
  have htrace : WordTrace (prefixWord ++ tailWord_500644) baseStart_500644 baseEnd_500644 := by
    simpa [prefixWord, tailWord_500644, baseEnd_500644] using wordTrace_append hprefix tailTrace_500644
  have hstable : (prefixWord ++ tailWord_500644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500644).length < 2 ^ (prefixWord ++ tailWord_500644).sum := by decide
  have hdescent : baseEnd_500644 < baseStart_500644 := by decide
  rcases family_descends (prefixWord ++ tailWord_500644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500653 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 3]
def baseStart_500653 : Nat := 118140960795 + 500653 * 2 ^ 59
def prefixEnd_500653 : Nat := 4983230072969 + 3 ^ 40 * 500653 * 2
def baseEnd_500653 : Nat := 228511671213808823586707

theorem tailTrace_500653 : CollatzResearch.WordTrace tailWord_500653 prefixEnd_500653 228511671213808823586707 := by
  unfold tailWord_500653
  simp only [CollatzResearch.WordTrace]
  refine ⟨18260315055227160570130613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12173543370151440380087075 18260315055227160570130613)
  ·
    refine ⟨1711904536427546303449745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18260315055227160570130613 1711904536427546303449745)
    ·
      refine ⟨1283928402320659727587309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1711904536427546303449745 1283928402320659727587309)
      ·
        refine ⟨481473150870247397845241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1283928402320659727587309 481473150870247397845241)
        ·
          refine ⟨361104863152685548383931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481473150870247397845241 361104863152685548383931)
          ·
            refine ⟨541657294729028322575897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361104863152685548383931 541657294729028322575897)
            ·
              refine ⟨406242971046771241931923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541657294729028322575897 406242971046771241931923)
              ·
                refine ⟨609364456570156862897885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406242971046771241931923 609364456570156862897885)
                ·
                  refine ⟨228511671213808823586707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609364456570156862897885 228511671213808823586707)
                  ·
                    rfl

theorem cell20_500653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_500653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500653 prefixEnd_500653 := by exact prefixLift 500653
  have htrace : WordTrace (prefixWord ++ tailWord_500653) baseStart_500653 baseEnd_500653 := by
    simpa [prefixWord, tailWord_500653, baseEnd_500653] using wordTrace_append hprefix tailTrace_500653
  have hstable : (prefixWord ++ tailWord_500653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500653).length < 2 ^ (prefixWord ++ tailWord_500653).sum := by decide
  have hdescent : baseEnd_500653 < baseStart_500653 := by decide
  rcases family_descends (prefixWord ++ tailWord_500653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500657 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 3]
def baseStart_500657 : Nat := 118140960795 + 500657 * 2 ^ 59
def prefixEnd_500657 : Nat := 4983230072969 + 3 ^ 40 * 500657 * 2
def baseEnd_500657 : Nat := 228513496922802587453357

theorem tailTrace_500657 : CollatzResearch.WordTrace tailWord_500657 prefixEnd_500657 228513496922802587453357 := by
  unfold tailWord_500657
  simp only [CollatzResearch.WordTrace]
  refine ⟨18260460947212669253276225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12173640631475112835517483 18260460947212669253276225)
  ·
    refine ⟨13695345710409501939957169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18260460947212669253276225 13695345710409501939957169)
    ·
      refine ⟨10271509282807126454967877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13695345710409501939957169 10271509282807126454967877)
      ·
        refine ⟨1925907990526336210306477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10271509282807126454967877 1925907990526336210306477)
        ·
          refine ⟨722215496447376078864929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1925907990526336210306477 722215496447376078864929)
          ·
            refine ⟨541661622335532059148697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722215496447376078864929 541661622335532059148697)
            ·
              refine ⟨406246216751649044361523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541661622335532059148697 406246216751649044361523)
              ·
                refine ⟨609369325127473566542285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406246216751649044361523 609369325127473566542285)
                ·
                  refine ⟨228513496922802587453357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609369325127473566542285 228513496922802587453357)
                  ·
                    rfl

theorem cell20_500657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_500657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500657 prefixEnd_500657 := by exact prefixLift 500657
  have htrace : WordTrace (prefixWord ++ tailWord_500657) baseStart_500657 baseEnd_500657 := by
    simpa [prefixWord, tailWord_500657, baseEnd_500657] using wordTrace_append hprefix tailTrace_500657
  have hstable : (prefixWord ++ tailWord_500657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500657).length < 2 ^ (prefixWord ++ tailWord_500657).sum := by decide
  have hdescent : baseEnd_500657 < baseStart_500657 := by decide
  rcases family_descends (prefixWord ++ tailWord_500657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500661 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_500661 : Nat := 118140960795 + 500661 * 2 ^ 59
def prefixEnd_500661 : Nat := 4983230072969 + 3 ^ 40 * 500661 * 2
def baseEnd_500661 : Nat := 228515322631796351320007

theorem tailTrace_500661 : CollatzResearch.WordTrace tailWord_500661 prefixEnd_500661 228515322631796351320007 := by
  unfold tailWord_500661
  simp only [CollatzResearch.WordTrace]
  refine ⟨18260606839198177936421837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12173737892798785290947891 18260606839198177936421837)
  ·
    refine ⟨6847727564699316726158189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18260606839198177936421837 6847727564699316726158189)
    ·
      refine ⟨2567897836762243772309321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6847727564699316726158189 2567897836762243772309321)
      ·
        refine ⟨1925923377571682829231991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2567897836762243772309321 1925923377571682829231991)
        ·
          refine ⟨2888885066357524243847987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925923377571682829231991 2888885066357524243847987)
          ·
            refine ⟨4333327599536286365771981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888885066357524243847987 4333327599536286365771981)
            ·
              refine ⟨1624997849826107387164493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4333327599536286365771981 1624997849826107387164493)
              ·
                refine ⟨609374193684790270186685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1624997849826107387164493 609374193684790270186685)
                ·
                  refine ⟨228515322631796351320007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609374193684790270186685 228515322631796351320007)
                  ·
                    rfl

theorem cell20_500661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_500661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500661 prefixEnd_500661 := by exact prefixLift 500661
  have htrace : WordTrace (prefixWord ++ tailWord_500661) baseStart_500661 baseEnd_500661 := by
    simpa [prefixWord, tailWord_500661, baseEnd_500661] using wordTrace_append hprefix tailTrace_500661
  have hstable : (prefixWord ++ tailWord_500661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500661).length < 2 ^ (prefixWord ++ tailWord_500661).sum := by decide
  have hdescent : baseEnd_500661 < baseStart_500661 := by decide
  rcases family_descends (prefixWord ++ tailWord_500661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500696 : List Nat := [2, 1, 2, 2, 2, 11]
def baseStart_500696 : Nat := 118140960795 + 500696 * 2 ^ 59
def prefixEnd_500696 : Nat := 4983230072969 + 3 ^ 40 * 500696 * 2
def baseEnd_500696 : Nat := 8464122132795992042711

theorem tailTrace_500696 : CollatzResearch.WordTrace tailWord_500696 prefixEnd_500696 8464122132795992042711 := by
  unfold tailWord_500696
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130941697035689456972971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12174588929380919275963961 9130941697035689456972971)
  ·
    refine ⟨13696412545553534185459457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9130941697035689456972971 13696412545553534185459457)
    ·
      refine ⟨10272309409165150639094593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13696412545553534185459457 10272309409165150639094593)
      ·
        refine ⟨7704232056873862979320945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10272309409165150639094593 7704232056873862979320945)
        ·
          refine ⟨5778174042655397234490709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704232056873862979320945 5778174042655397234490709)
          ·
            refine ⟨8464122132795992042711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5778174042655397234490709 8464122132795992042711)
            ·
              rfl

theorem cell20_500696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 11].length) (baseStart_500696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500696 prefixEnd_500696 := by exact prefixLift 500696
  have htrace : WordTrace (prefixWord ++ tailWord_500696) baseStart_500696 baseEnd_500696 := by
    simpa [prefixWord, tailWord_500696, baseEnd_500696] using wordTrace_append hprefix tailTrace_500696
  have hstable : (prefixWord ++ tailWord_500696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500696).length < 2 ^ (prefixWord ++ tailWord_500696).sum := by decide
  have hdescent : baseEnd_500696 < baseStart_500696 := by decide
  rcases family_descends (prefixWord ++ tailWord_500696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500709 : List Nat := [1, 3, 1, 6, 1, 2, 1, 5]
def baseStart_500709 : Nat := 118140960795 + 500709 * 2 ^ 59
def prefixEnd_500709 : Nat := 4983230072969 + 3 ^ 40 * 500709 * 2
def baseEnd_500709 : Nat := 76179077046573839239937

theorem tailTrace_500709 : CollatzResearch.WordTrace tailWord_500709 prefixEnd_500709 76179077046573839239937 := by
  unfold tailWord_500709
  simp only [CollatzResearch.WordTrace]
  refine ⟨18262357543024282134169181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12174905028682854756112787 18262357543024282134169181)
  ·
    refine ⟨6848384078634105800313443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18262357543024282134169181 6848384078634105800313443)
    ·
      refine ⟨10272576117951158700470165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6848384078634105800313443 10272576117951158700470165)
      ·
        refine ⟨481527005528960564084539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10272576117951158700470165 481527005528960564084539)
        ·
          refine ⟨722290508293440846126809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481527005528960564084539 722290508293440846126809)
          ·
            refine ⟨541717881220080634595107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722290508293440846126809 541717881220080634595107)
            ·
              refine ⟨812576821830120951892661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541717881220080634595107 812576821830120951892661)
              ·
                refine ⟨76179077046573839239937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 812576821830120951892661 76179077046573839239937)
                ·
                  rfl

theorem cell20_500709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_500709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500709 prefixEnd_500709 := by exact prefixLift 500709
  have htrace : WordTrace (prefixWord ++ tailWord_500709) baseStart_500709 baseEnd_500709 := by
    simpa [prefixWord, tailWord_500709, baseEnd_500709] using wordTrace_append hprefix tailTrace_500709
  have hstable : (prefixWord ++ tailWord_500709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500709).length < 2 ^ (prefixWord ++ tailWord_500709).sum := by decide
  have hdescent : baseEnd_500709 < baseStart_500709 := by decide
  rcases family_descends (prefixWord ++ tailWord_500709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500782 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_500782 : Nat := 118140960795 + 500782 * 2 ^ 59
def prefixEnd_500782 : Nat := 4983230072969 + 3 ^ 40 * 500782 * 2
def baseEnd_500782 : Nat := 228570550328857708286179

theorem tailTrace_500782 : CollatzResearch.WordTrace tailWord_500782 prefixEnd_500782 228570550328857708286179 := by
  unfold tailWord_500782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283127508969976950197075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12176680047839877067717733 2283127508969976950197075)
  ·
    refine ⟨3424691263454965425295613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283127508969976950197075 3424691263454965425295613)
    ·
      refine ⟨1284259223795612034485855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3424691263454965425295613 1284259223795612034485855)
      ·
        refine ⟨1926388835693418051728783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284259223795612034485855 1926388835693418051728783)
        ·
          refine ⟨2889583253540127077593175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926388835693418051728783 2889583253540127077593175)
          ·
            refine ⟨4334374880310190616389763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889583253540127077593175 4334374880310190616389763)
            ·
              refine ⟨6501562320465285924584645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334374880310190616389763 6501562320465285924584645)
              ·
                refine ⟨1219042935087241110859621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6501562320465285924584645 1219042935087241110859621)
                ·
                  refine ⟨228570550328857708286179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219042935087241110859621 228570550328857708286179)
                  ·
                    rfl

theorem cell20_500782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_500782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500782 prefixEnd_500782 := by exact prefixLift 500782
  have htrace : WordTrace (prefixWord ++ tailWord_500782) baseStart_500782 baseEnd_500782 := by
    simpa [prefixWord, tailWord_500782, baseEnd_500782] using wordTrace_append hprefix tailTrace_500782
  have hstable : (prefixWord ++ tailWord_500782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500782).length < 2 ^ (prefixWord ++ tailWord_500782).sum := by decide
  have hdescent : baseEnd_500782 < baseStart_500782 := by decide
  rcases family_descends (prefixWord ++ tailWord_500782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500796 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_500796 : Nat := 118140960795 + 500796 * 2 ^ 59
def prefixEnd_500796 : Nat := 4983230072969 + 3 ^ 40 * 500796 * 2
def baseEnd_500796 : Nat := 228576940310335881819455

theorem tailTrace_500796 : CollatzResearch.WordTrace tailWord_500796 prefixEnd_500796 228576940310335881819455 := by
  unfold tailWord_500796
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132765346854547996293121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12177020462472730661724161 9132765346854547996293121)
  ·
    refine ⟨6849574010140910997219841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9132765346854547996293121 6849574010140910997219841)
    ·
      refine ⟨5137180507605683247914881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6849574010140910997219841 5137180507605683247914881)
      ·
        refine ⟨3852885380704262435936161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5137180507605683247914881 3852885380704262435936161)
        ·
          refine ⟨2889664035528196826952121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3852885380704262435936161 2889664035528196826952121)
          ·
            refine ⟨2167248026646147620214091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889664035528196826952121 2167248026646147620214091)
            ·
              refine ⟨3250872039969221430321137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167248026646147620214091 3250872039969221430321137)
              ·
                refine ⟨2438154029976916072740853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3250872039969221430321137 2438154029976916072740853)
                ·
                  refine ⟨228576940310335881819455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2438154029976916072740853 228576940310335881819455)
                  ·
                    rfl

theorem cell20_500796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_500796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500796 prefixEnd_500796 := by exact prefixLift 500796
  have htrace : WordTrace (prefixWord ++ tailWord_500796) baseStart_500796 baseEnd_500796 := by
    simpa [prefixWord, tailWord_500796, baseEnd_500796] using wordTrace_append hprefix tailTrace_500796
  have hstable : (prefixWord ++ tailWord_500796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500796).length < 2 ^ (prefixWord ++ tailWord_500796).sum := by decide
  have hdescent : baseEnd_500796 < baseStart_500796 := by decide
  rcases family_descends (prefixWord ++ tailWord_500796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500806 : List Nat := [6, 1, 1, 1, 1, 2, 8]
def baseStart_500806 : Nat := 118140960795 + 500806 * 2 ^ 59
def prefixEnd_500806 : Nat := 4983230072969 + 3 ^ 40 * 500806 * 2
def baseEnd_500806 : Nat := 25397944953646699054009

theorem tailTrace_500806 : CollatzResearch.WordTrace tailWord_500806 prefixEnd_500806 25397944953646699054009 := by
  unfold tailWord_500806
  simp only [CollatzResearch.WordTrace]
  refine ⟨570809231989777115639071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12177263615781911800300181 570809231989777115639071)
  ·
    refine ⟨856213847984665673458607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 570809231989777115639071 856213847984665673458607)
    ·
      refine ⟨1284320771976998510187911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856213847984665673458607 1284320771976998510187911)
      ·
        refine ⟨1926481157965497765281867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284320771976998510187911 1926481157965497765281867)
        ·
          refine ⟨2889721736948246647922801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926481157965497765281867 2889721736948246647922801)
          ·
            refine ⟨2167291302711184985942101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889721736948246647922801 2167291302711184985942101)
            ·
              refine ⟨25397944953646699054009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2167291302711184985942101 25397944953646699054009)
              ·
                rfl

theorem cell20_500806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 8].length) (baseStart_500806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500806 prefixEnd_500806 := by exact prefixLift 500806
  have htrace : WordTrace (prefixWord ++ tailWord_500806) baseStart_500806 baseEnd_500806 := by
    simpa [prefixWord, tailWord_500806, baseEnd_500806] using wordTrace_append hprefix tailTrace_500806
  have hstable : (prefixWord ++ tailWord_500806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500806).length < 2 ^ (prefixWord ++ tailWord_500806).sum := by decide
  have hdescent : baseEnd_500806 < baseStart_500806 := by decide
  rcases family_descends (prefixWord ++ tailWord_500806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500810 : List Nat := [3, 1, 2, 1, 1, 2, 10]
def baseStart_500810 : Nat := 118140960795 + 500810 * 2 ^ 59
def prefixEnd_500810 : Nat := 4983230072969 + 3 ^ 40 * 500810 * 2
def baseEnd_500810 : Nat := 25398147810201561705859

theorem tailTrace_500810 : CollatzResearch.WordTrace tailWord_500810 prefixEnd_500810 25398147810201561705859 := by
  unfold tailWord_500810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4566510328914594095898971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12177360877105584255730589 4566510328914594095898971)
  ·
    refine ⟨6849765493371891143848457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4566510328914594095898971 6849765493371891143848457)
    ·
      refine ⟨5137324120028918357886343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6849765493371891143848457 5137324120028918357886343)
      ·
        refine ⟨7705986180043377536829515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137324120028918357886343 7705986180043377536829515)
        ·
          refine ⟨11558979270065066305244273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705986180043377536829515 11558979270065066305244273)
          ·
            refine ⟨8669234452548799728933205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11558979270065066305244273 8669234452548799728933205)
            ·
              refine ⟨25398147810201561705859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8669234452548799728933205 25398147810201561705859)
              ·
                rfl

theorem cell20_500810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_500810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500810 prefixEnd_500810 := by exact prefixLift 500810
  have htrace : WordTrace (prefixWord ++ tailWord_500810) baseStart_500810 baseEnd_500810 := by
    simpa [prefixWord, tailWord_500810, baseEnd_500810] using wordTrace_append hprefix tailTrace_500810
  have hstable : (prefixWord ++ tailWord_500810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500810).length < 2 ^ (prefixWord ++ tailWord_500810).sum := by decide
  have hdescent : baseEnd_500810 < baseStart_500810 := by decide
  rcases family_descends (prefixWord ++ tailWord_500810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500813 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_500813 : Nat := 118140960795 + 500813 * 2 ^ 59
def prefixEnd_500813 : Nat := 4983230072969 + 3 ^ 40 * 500813 * 2
def baseEnd_500813 : Nat := 228584699573559378252719

theorem tailTrace_500813 : CollatzResearch.WordTrace tailWord_500813 prefixEnd_500813 228584699573559378252719 := by
  unfold tailWord_500813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18266150734647507895955093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12177433823098338597303395 18266150734647507895955093)
  ·
    refine ⟨856225815686601932622895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18266150734647507895955093 856225815686601932622895)
    ·
      refine ⟨1284338723529902898934343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856225815686601932622895 1284338723529902898934343)
      ·
        refine ⟨1926508085294854348401515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284338723529902898934343 1926508085294854348401515)
        ·
          refine ⟨2889762127942281522602273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926508085294854348401515 2889762127942281522602273)
          ·
            refine ⟨2167321595956711141951705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889762127942281522602273 2167321595956711141951705)
            ·
              refine ⟨1625491196967533356463779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167321595956711141951705 1625491196967533356463779)
              ·
                refine ⟨2438236795451300034695669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625491196967533356463779 2438236795451300034695669)
                ·
                  refine ⟨228584699573559378252719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2438236795451300034695669 228584699573559378252719)
                  ·
                    rfl

theorem cell20_500813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_500813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500813 prefixEnd_500813 := by exact prefixLift 500813
  have htrace : WordTrace (prefixWord ++ tailWord_500813) baseStart_500813 baseEnd_500813 := by
    simpa [prefixWord, tailWord_500813, baseEnd_500813] using wordTrace_append hprefix tailTrace_500813
  have hstable : (prefixWord ++ tailWord_500813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500813).length < 2 ^ (prefixWord ++ tailWord_500813).sum := by decide
  have hdescent : baseEnd_500813 < baseStart_500813 := by decide
  rcases family_descends (prefixWord ++ tailWord_500813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500820 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_500820 : Nat := 118140960795 + 500820 * 2 ^ 59
def prefixEnd_500820 : Nat := 4983230072969 + 3 ^ 40 * 500820 * 2
def baseEnd_500820 : Nat := 228587894564298465019357

theorem tailTrace_500820 : CollatzResearch.WordTrace tailWord_500820 prefixEnd_500820 228587894564298465019357 := by
  unfold tailWord_500820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133203022811074045729957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12177604030414765394306609 9133203022811074045729957)
  ·
    refine ⟨1712475566777076383574367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9133203022811074045729957 1712475566777076383574367)
    ·
      refine ⟨2568713350165614575361551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712475566777076383574367 2568713350165614575361551)
      ·
        refine ⟨3853070025248421863042327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568713350165614575361551 3853070025248421863042327)
        ·
          refine ⟨5779605037872632794563491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853070025248421863042327 5779605037872632794563491)
          ·
            refine ⟨8669407556808949191845237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779605037872632794563491 8669407556808949191845237)
            ·
              refine ⟨812756958450838986735491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8669407556808949191845237 812756958450838986735491)
              ·
                refine ⟨1219135437676258480103237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812756958450838986735491 1219135437676258480103237)
                ·
                  refine ⟨228587894564298465019357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1219135437676258480103237 228587894564298465019357)
                  ·
                    rfl

theorem cell20_500820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_500820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500820 prefixEnd_500820 := by exact prefixLift 500820
  have htrace : WordTrace (prefixWord ++ tailWord_500820) baseStart_500820 baseEnd_500820 := by
    simpa [prefixWord, tailWord_500820, baseEnd_500820] using wordTrace_append hprefix tailTrace_500820
  have hstable : (prefixWord ++ tailWord_500820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500820).length < 2 ^ (prefixWord ++ tailWord_500820).sum := by decide
  have hdescent : baseEnd_500820 < baseStart_500820 := by decide
  rcases family_descends (prefixWord ++ tailWord_500820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500848 : List Nat := [2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_500848 : Nat := 118140960795 + 500848 * 2 ^ 59
def prefixEnd_500848 : Nat := 4983230072969 + 3 ^ 40 * 500848 * 2
def baseEnd_500848 : Nat := 76200224842418270695303

theorem tailTrace_500848 : CollatzResearch.WordTrace tailWord_500848 prefixEnd_500848 76200224842418270695303 := by
  unfold tailWord_500848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133713644760354436739599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12178284859680472582319465 9133713644760354436739599)
  ·
    refine ⟨13700570467140531655109399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133713644760354436739599 13700570467140531655109399)
    ·
      refine ⟨20550855700710797482664099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13700570467140531655109399 20550855700710797482664099)
      ·
        refine ⟨30826283551066196223996149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20550855700710797482664099 30826283551066196223996149)
        ·
          refine ⟨2889964082912455895999639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30826283551066196223996149 2889964082912455895999639)
          ·
            refine ⟨4334946124368683843999459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889964082912455895999639 4334946124368683843999459)
            ·
              refine ⟨6502419186553025765999189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334946124368683843999459 6502419186553025765999189)
              ·
                refine ⟨76200224842418270695303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6502419186553025765999189 76200224842418270695303)
                ·
                  rfl

theorem cell20_500848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_500848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500848 prefixEnd_500848 := by exact prefixLift 500848
  have htrace : WordTrace (prefixWord ++ tailWord_500848) baseStart_500848 baseEnd_500848 := by
    simpa [prefixWord, tailWord_500848, baseEnd_500848] using wordTrace_append hprefix tailTrace_500848
  have hstable : (prefixWord ++ tailWord_500848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500848).length < 2 ^ (prefixWord ++ tailWord_500848).sum := by decide
  have hdescent : baseEnd_500848 < baseStart_500848 := by decide
  rcases family_descends (prefixWord ++ tailWord_500848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500882 : List Nat := [3, 2, 3, 1, 1, 4, 1, 5]
def baseStart_500882 : Nat := 118140960795 + 500882 * 2 ^ 59
def prefixEnd_500882 : Nat := 4983230072969 + 3 ^ 40 * 500882 * 2
def baseEnd_500882 : Nat := 76205397684567268317479

theorem tailTrace_500882 : CollatzResearch.WordTrace tailWord_500882 prefixEnd_500882 76205397684567268317479 := by
  unfold tailWord_500882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567166842849383170054225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12179111580931688453477933 4567166842849383170054225)
  ·
    refine ⟨3425375132137037377540669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4567166842849383170054225 3425375132137037377540669)
    ·
      refine ⟨1284515674551389016577751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3425375132137037377540669 1284515674551389016577751)
      ·
        refine ⟨1926773511827083524866627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284515674551389016577751 1926773511827083524866627)
        ·
          refine ⟨2890160267740625287299941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926773511827083524866627 2890160267740625287299941)
          ·
            refine ⟨541905050201367241368739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2890160267740625287299941 541905050201367241368739)
            ·
              refine ⟨812857575302050862053109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541905050201367241368739 812857575302050862053109)
              ·
                refine ⟨76205397684567268317479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 812857575302050862053109 76205397684567268317479)
                ·
                  rfl

theorem cell20_500882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_500882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500882 prefixEnd_500882 := by exact prefixLift 500882
  have htrace : WordTrace (prefixWord ++ tailWord_500882) baseStart_500882 baseEnd_500882 := by
    simpa [prefixWord, tailWord_500882, baseEnd_500882] using wordTrace_append hprefix tailTrace_500882
  have hstable : (prefixWord ++ tailWord_500882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500882).length < 2 ^ (prefixWord ++ tailWord_500882).sum := by decide
  have hdescent : baseEnd_500882 < baseStart_500882 := by decide
  rcases family_descends (prefixWord ++ tailWord_500882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500913 : List Nat := [1, 2, 2, 5, 1, 1, 1, 5, 2]
def baseStart_500913 : Nat := 118140960795 + 500913 * 2 ^ 59
def prefixEnd_500913 : Nat := 4983230072969 + 3 ^ 40 * 500913 * 2
def baseEnd_500913 : Nat := 228630342298403474918977

theorem tailTrace_500913 : CollatzResearch.WordTrace tailWord_500913 prefixEnd_500913 228630342298403474918977 := by
  unfold tailWord_500913
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269798034285224974595393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12179865356190149983063595 18269798034285224974595393)
  ·
    refine ⟨13702348525713918730946545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18269798034285224974595393 13702348525713918730946545)
    ·
      refine ⟨10276761394285439048209909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13702348525713918730946545 10276761394285439048209909)
      ·
        refine ⟨963446380714259910769679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10276761394285439048209909 963446380714259910769679)
        ·
          refine ⟨1445169571071389866154519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963446380714259910769679 1445169571071389866154519)
          ·
            refine ⟨2167754356607084799231779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445169571071389866154519 2167754356607084799231779)
            ·
              refine ⟨3251631534910627198847669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167754356607084799231779 3251631534910627198847669)
              ·
                refine ⟨304840456397871299891969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3251631534910627198847669 304840456397871299891969)
                ·
                  refine ⟨228630342298403474918977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304840456397871299891969 228630342298403474918977)
                  ·
                    rfl

theorem cell20_500913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_500913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500913 prefixEnd_500913 := by exact prefixLift 500913
  have htrace : WordTrace (prefixWord ++ tailWord_500913) baseStart_500913 baseEnd_500913 := by
    simpa [prefixWord, tailWord_500913, baseEnd_500913] using wordTrace_append hprefix tailTrace_500913
  have hstable : (prefixWord ++ tailWord_500913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500913).length < 2 ^ (prefixWord ++ tailWord_500913).sum := by decide
  have hdescent : baseEnd_500913 < baseStart_500913 := by decide
  rcases family_descends (prefixWord ++ tailWord_500913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500986 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_500986 : Nat := 118140960795 + 500986 * 2 ^ 59
def prefixEnd_500986 : Nat := 4983230072969 + 3 ^ 40 * 500986 * 2
def baseEnd_500986 : Nat := 228663661487539665485345

theorem tailTrace_500986 : CollatzResearch.WordTrace tailWord_500986 prefixEnd_500986 228663661487539665485345 := by
  unfold tailWord_500986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568115140755189610500703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12181640375347172294668541 4568115140755189610500703)
  ·
    refine ⟨6852172711132784415751055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4568115140755189610500703 6852172711132784415751055)
    ·
      refine ⟨10278259066699176623626583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6852172711132784415751055 10278259066699176623626583)
      ·
        refine ⟨15417388600048764935439875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10278259066699176623626583 15417388600048764935439875)
        ·
          refine ⟨23126082900073147403159813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15417388600048764935439875 23126082900073147403159813)
          ·
            refine ⟨4336140543763715138092465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23126082900073147403159813 4336140543763715138092465)
            ·
              refine ⟨3252105407822786353569349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4336140543763715138092465 3252105407822786353569349)
              ·
                refine ⟨609769763966772441294253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3252105407822786353569349 609769763966772441294253)
                ·
                  refine ⟨228663661487539665485345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609769763966772441294253 228663661487539665485345)
                  ·
                    rfl

theorem cell20_500986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_500986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_500986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_500986 prefixEnd_500986 := by exact prefixLift 500986
  have htrace : WordTrace (prefixWord ++ tailWord_500986) baseStart_500986 baseEnd_500986 := by
    simpa [prefixWord, tailWord_500986, baseEnd_500986] using wordTrace_append hprefix tailTrace_500986
  have hstable : (prefixWord ++ tailWord_500986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500986).length < 2 ^ (prefixWord ++ tailWord_500986).sum := by decide
  have hdescent : baseEnd_500986 < baseStart_500986 := by decide
  rcases family_descends (prefixWord ++ tailWord_500986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501003 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 3]
def baseStart_501003 : Nat := 118140960795 + 501003 * 2 ^ 59
def prefixEnd_501003 : Nat := 4983230072969 + 3 ^ 40 * 501003 * 2
def baseEnd_501003 : Nat := 228671420750763161918609

theorem tailTrace_501003 : CollatzResearch.WordTrace tailWord_501003 prefixEnd_501003 228671420750763161918609 := by
  unfold tailWord_501003
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273080603959170345371663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12182053735972780230247775 18273080603959170345371663)
  ·
    refine ⟨27409620905938755518057495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273080603959170345371663 27409620905938755518057495)
    ·
      refine ⟨41114431358908133277086243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27409620905938755518057495 41114431358908133277086243)
      ·
        refine ⟨61671647038362199915629365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41114431358908133277086243 61671647038362199915629365)
        ·
          refine ⟨5781716909846456242090253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61671647038362199915629365 5781716909846456242090253)
          ·
            refine ⟨2168143841192421090783845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5781716909846456242090253 2168143841192421090783845)
            ·
              refine ⟨406526970223578954521971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2168143841192421090783845 406526970223578954521971)
              ·
                refine ⟨609790455335368431782957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406526970223578954521971 609790455335368431782957)
                ·
                  refine ⟨228671420750763161918609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609790455335368431782957 228671420750763161918609)
                  ·
                    rfl

theorem cell20_501003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_501003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501003 prefixEnd_501003 := by exact prefixLift 501003
  have htrace : WordTrace (prefixWord ++ tailWord_501003) baseStart_501003 baseEnd_501003 := by
    simpa [prefixWord, tailWord_501003, baseEnd_501003] using wordTrace_append hprefix tailTrace_501003
  have hstable : (prefixWord ++ tailWord_501003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501003).length < 2 ^ (prefixWord ++ tailWord_501003).sum := by decide
  have hdescent : baseEnd_501003 < baseStart_501003 := by decide
  rcases family_descends (prefixWord ++ tailWord_501003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501038 : List Nat := [4, 1, 3, 12]
def baseStart_501038 : Nat := 118140960795 + 501038 * 2 ^ 59
def prefixEnd_501038 : Nat := 4983230072969 + 3 ^ 40 * 501038 * 2
def baseEnd_501038 : Nat := 941100393845508624493

theorem tailTrace_501038 : CollatzResearch.WordTrace tailWord_501038 prefixEnd_501038 941100393845508624493 := by
  unfold tailWord_501038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284294644854046415361971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12182904772554914215263845 2284294644854046415361971)
  ·
    refine ⟨3426441967281069623042957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2284294644854046415361971 3426441967281069623042957)
    ·
      refine ⟨1284915737730401108641109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3426441967281069623042957 1284915737730401108641109)
      ·
        refine ⟨941100393845508624493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1284915737730401108641109 941100393845508624493)
        ·
          rfl

theorem cell20_501038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 12].length) (baseStart_501038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501038 prefixEnd_501038 := by exact prefixLift 501038
  have htrace : WordTrace (prefixWord ++ tailWord_501038) baseStart_501038 baseEnd_501038 := by
    simpa [prefixWord, tailWord_501038, baseEnd_501038] using wordTrace_append hprefix tailTrace_501038
  have hstable : (prefixWord ++ tailWord_501038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501038).length < 2 ^ (prefixWord ++ tailWord_501038).sum := by decide
  have hdescent : baseEnd_501038 < baseStart_501038 := by decide
  rcases family_descends (prefixWord ++ tailWord_501038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501041 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_501041 : Nat := 118140960795 + 501041 * 2 ^ 59
def prefixEnd_501041 : Nat := 4983230072969 + 3 ^ 40 * 501041 * 2
def baseEnd_501041 : Nat := 228688764986203918651787

theorem tailTrace_501041 : CollatzResearch.WordTrace tailWord_501041 prefixEnd_501041 228688764986203918651787 := by
  unfold tailWord_501041
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274466577821502835254977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12182977718547668556836651 18274466577821502835254977)
  ·
    refine ⟨13705849933366127126441233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18274466577821502835254977 13705849933366127126441233)
    ·
      refine ⟨10279387450024595344830925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13705849933366127126441233 10279387450024595344830925)
      ·
        refine ⟨3854770293759223254311597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10279387450024595344830925 3854770293759223254311597)
        ·
          refine ⟨1445538860159708720366849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3854770293759223254311597 1445538860159708720366849)
          ·
            refine ⟨1084154145119781540275137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445538860159708720366849 1084154145119781540275137)
            ·
              refine ⟨813115608839836155206353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084154145119781540275137 813115608839836155206353)
              ·
                refine ⟨609836706629877116404765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813115608839836155206353 609836706629877116404765)
                ·
                  refine ⟨228688764986203918651787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609836706629877116404765 228688764986203918651787)
                  ·
                    rfl

theorem cell20_501041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_501041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501041 prefixEnd_501041 := by exact prefixLift 501041
  have htrace : WordTrace (prefixWord ++ tailWord_501041) baseStart_501041 baseEnd_501041 := by
    simpa [prefixWord, tailWord_501041, baseEnd_501041] using wordTrace_append hprefix tailTrace_501041
  have hstable : (prefixWord ++ tailWord_501041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501041).length < 2 ^ (prefixWord ++ tailWord_501041).sum := by decide
  have hdescent : baseEnd_501041 < baseStart_501041 := by decide
  rcases family_descends (prefixWord ++ tailWord_501041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501055 : List Nat := [1, 1, 2, 2, 4, 4, 1, 5]
def baseStart_501055 : Nat := 118140960795 + 501055 * 2 ^ 59
def prefixEnd_501055 : Nat := 4983230072969 + 3 ^ 40 * 501055 * 2
def baseEnd_501055 : Nat := 76231718322560697395021

theorem tailTrace_501055 : CollatzResearch.WordTrace tailWord_501055 prefixEnd_501055 76231718322560697395021 := by
  unfold tailWord_501055
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274977199770783226264619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12183318133180522150843079 18274977199770783226264619)
  ·
    refine ⟨27412465799656174839396929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18274977199770783226264619 27412465799656174839396929)
    ·
      refine ⟨20559349349742131129547697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27412465799656174839396929 20559349349742131129547697)
      ·
        refine ⟨15419512012306598347160773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20559349349742131129547697 15419512012306598347160773)
        ·
          refine ⟨2891158502307487190092645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15419512012306598347160773 2891158502307487190092645)
          ·
            refine ⟨542092219182653848142371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2891158502307487190092645 542092219182653848142371)
            ·
              refine ⟨813138328773980772213557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542092219182653848142371 813138328773980772213557)
              ·
                refine ⟨76231718322560697395021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 813138328773980772213557 76231718322560697395021)
                ·
                  rfl

theorem cell20_501055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_501055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501055 prefixEnd_501055 := by exact prefixLift 501055
  have htrace : WordTrace (prefixWord ++ tailWord_501055) baseStart_501055 baseEnd_501055 := by
    simpa [prefixWord, tailWord_501055, baseEnd_501055] using wordTrace_append hprefix tailTrace_501055
  have hstable : (prefixWord ++ tailWord_501055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501055).length < 2 ^ (prefixWord ++ tailWord_501055).sum := by decide
  have hdescent : baseEnd_501055 < baseStart_501055 := by decide
  rcases family_descends (prefixWord ++ tailWord_501055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501096 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_501096 : Nat := 118140960795 + 501096 * 2 ^ 59
def prefixEnd_501096 : Nat := 4983230072969 + 3 ^ 40 * 501096 * 2
def baseEnd_501096 : Nat := 228713868484868171818229

theorem tailTrace_501096 : CollatzResearch.WordTrace tailWord_501096 prefixEnd_501096 228713868484868171818229 := by
  unfold tailWord_501096
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138236296311123614253571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12184315061748164819004761 9138236296311123614253571)
  ·
    refine ⟨13707354444466685421380357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138236296311123614253571 13707354444466685421380357)
    ·
      refine ⟨2570128958337503516508817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13707354444466685421380357 2570128958337503516508817)
      ·
        refine ⟨1927596718753127637381613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2570128958337503516508817 1927596718753127637381613)
        ·
          refine ⟨722848769532422864018105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1927596718753127637381613 722848769532422864018105)
          ·
            refine ⟨542136577149317148013579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722848769532422864018105 542136577149317148013579)
            ·
              refine ⟨813204865723975722020369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542136577149317148013579 813204865723975722020369)
              ·
                refine ⟨609903649292981791515277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813204865723975722020369 609903649292981791515277)
                ·
                  refine ⟨228713868484868171818229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609903649292981791515277 228713868484868171818229)
                  ·
                    rfl

theorem cell20_501096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_501096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501096 prefixEnd_501096 := by exact prefixLift 501096
  have htrace : WordTrace (prefixWord ++ tailWord_501096) baseStart_501096 baseEnd_501096 := by
    simpa [prefixWord, tailWord_501096, baseEnd_501096] using wordTrace_append hprefix tailTrace_501096
  have hstable : (prefixWord ++ tailWord_501096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501096).length < 2 ^ (prefixWord ++ tailWord_501096).sum := by decide
  have hdescent : baseEnd_501096 < baseStart_501096 := by decide
  rcases family_descends (prefixWord ++ tailWord_501096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501100 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_501100 : Nat := 118140960795 + 501100 * 2 ^ 59
def prefixEnd_501100 : Nat := 4983230072969 + 3 ^ 40 * 501100 * 2
def baseEnd_501100 : Nat := 228715694193861935684879

theorem tailTrace_501100 : CollatzResearch.WordTrace tailWord_501100 prefixEnd_501100 228715694193861935684879 := by
  unfold tailWord_501100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138309242303877955826377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12184412323071837274435169 9138309242303877955826377)
  ·
    refine ⟨6853731931727908466869783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9138309242303877955826377 6853731931727908466869783)
    ·
      refine ⟨10280597897591862700304675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853731931727908466869783 10280597897591862700304675)
      ·
        refine ⟨15420896846387794050457013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280597897591862700304675 15420896846387794050457013)
        ·
          refine ⟨1445709079348855692230345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15420896846387794050457013 1445709079348855692230345)
          ·
            refine ⟨1084281809511641769172759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445709079348855692230345 1084281809511641769172759)
            ·
              refine ⟨1626422714267462653759139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084281809511641769172759 1626422714267462653759139)
              ·
                refine ⟨2439634071401193980638709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626422714267462653759139 2439634071401193980638709)
                ·
                  refine ⟨228715694193861935684879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2439634071401193980638709 228715694193861935684879)
                  ·
                    rfl

theorem cell20_501100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_501100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501100 prefixEnd_501100 := by exact prefixLift 501100
  have htrace : WordTrace (prefixWord ++ tailWord_501100) baseStart_501100 baseEnd_501100 := by
    simpa [prefixWord, tailWord_501100, baseEnd_501100] using wordTrace_append hprefix tailTrace_501100
  have hstable : (prefixWord ++ tailWord_501100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501100).length < 2 ^ (prefixWord ++ tailWord_501100).sum := by decide
  have hdescent : baseEnd_501100 < baseStart_501100 := by decide
  rcases family_descends (prefixWord ++ tailWord_501100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501117 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 3]
def baseStart_501117 : Nat := 118140960795 + 501117 * 2 ^ 59
def prefixEnd_501117 : Nat := 4983230072969 + 3 ^ 40 * 501117 * 2
def baseEnd_501117 : Nat := 228723453457085432118143

theorem tailTrace_501117 : CollatzResearch.WordTrace tailWord_501117 prefixEnd_501117 228723453457085432118143 := by
  unfold tailWord_501117
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277238525546167815021605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12184825683697445210014403 18277238525546167815021605)
  ·
    refine ⟨3426982223539906465316551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18277238525546167815021605 3426982223539906465316551)
    ·
      refine ⟨5140473335309859697974827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426982223539906465316551 5140473335309859697974827)
      ·
        refine ⟨7710710002964789546962241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140473335309859697974827 7710710002964789546962241)
        ·
          refine ⟨5783032502223592160221681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710710002964789546962241 5783032502223592160221681)
          ·
            refine ⟨4337274376667694120166261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5783032502223592160221681 4337274376667694120166261)
            ·
              refine ⟨406619472812596323765587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4337274376667694120166261 406619472812596323765587)
              ·
                refine ⟨609929209218894485648381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406619472812596323765587 609929209218894485648381)
                ·
                  refine ⟨228723453457085432118143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609929209218894485648381 228723453457085432118143)
                  ·
                    rfl

theorem cell20_501117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_501117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501117 prefixEnd_501117 := by exact prefixLift 501117
  have htrace : WordTrace (prefixWord ++ tailWord_501117) baseStart_501117 baseEnd_501117 := by
    simpa [prefixWord, tailWord_501117, baseEnd_501117] using wordTrace_append hprefix tailTrace_501117
  have hstable : (prefixWord ++ tailWord_501117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501117).length < 2 ^ (prefixWord ++ tailWord_501117).sum := by decide
  have hdescent : baseEnd_501117 < baseStart_501117 := by decide
  rcases family_descends (prefixWord ++ tailWord_501117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501148 : List Nat := [2, 2, 3, 4, 1, 2, 6]
def baseStart_501148 : Nat := 118140960795 + 501148 * 2 ^ 59
def prefixEnd_501148 : Nat := 4983230072969 + 3 ^ 40 * 501148 * 2
def baseEnd_501148 : Nat := 25415289189087455787187

theorem tailTrace_501148 : CollatzResearch.WordTrace tailWord_501148 prefixEnd_501148 25415289189087455787187 := by
  unfold tailWord_501148
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139184594216930054700049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12185579458955906739600065 9139184594216930054700049)
  ·
    refine ⟨6854388445662697541025037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9139184594216930054700049 6854388445662697541025037)
    ·
      refine ⟨2570395667123511577884389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6854388445662697541025037 2570395667123511577884389)
      ·
        refine ⟨481949187585658420853323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2570395667123511577884389 481949187585658420853323)
        ·
          refine ⟨722923781378487631279985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481949187585658420853323 722923781378487631279985)
          ·
            refine ⟨542192836033865723459989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722923781378487631279985 542192836033865723459989)
            ·
              refine ⟨25415289189087455787187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 542192836033865723459989 25415289189087455787187)
              ·
                rfl

theorem cell20_501148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 6].length) (baseStart_501148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501148 prefixEnd_501148 := by exact prefixLift 501148
  have htrace : WordTrace (prefixWord ++ tailWord_501148) baseStart_501148 baseEnd_501148 := by
    simpa [prefixWord, tailWord_501148, baseEnd_501148] using wordTrace_append hprefix tailTrace_501148
  have hstable : (prefixWord ++ tailWord_501148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501148).length < 2 ^ (prefixWord ++ tailWord_501148).sum := by decide
  have hdescent : baseEnd_501148 < baseStart_501148 := by decide
  rcases family_descends (prefixWord ++ tailWord_501148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501217 : List Nat := [1, 2, 3, 1, 2, 3, 4, 2, 2]
def baseStart_501217 : Nat := 118140960795 + 501217 * 2 ^ 59
def prefixEnd_501217 : Nat := 4983230072969 + 3 ^ 40 * 501217 * 2
def baseEnd_501217 : Nat := 228769096181929528784401

theorem tailTrace_501217 : CollatzResearch.WordTrace tailWord_501217 prefixEnd_501217 228769096181929528784401 := by
  unfold tailWord_501217
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280885825183884893661905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12187257216789256595774603 18280885825183884893661905)
  ·
    refine ⟨13710664368887913670246429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18280885825183884893661905 13710664368887913670246429)
    ·
      refine ⟨5141499138332967626342411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13710664368887913670246429 5141499138332967626342411)
      ·
        refine ⟨7712248707499451439513617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141499138332967626342411 7712248707499451439513617)
        ·
          refine ⟨5784186530624588579635213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7712248707499451439513617 5784186530624588579635213)
          ·
            refine ⟨2169069948984220717363205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5784186530624588579635213 2169069948984220717363205)
            ·
              refine ⟨406700615434541384505601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2169069948984220717363205 406700615434541384505601)
              ·
                refine ⟨305025461575906038379201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406700615434541384505601 305025461575906038379201)
                ·
                  refine ⟨228769096181929528784401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305025461575906038379201 228769096181929528784401)
                  ·
                    rfl

theorem cell20_501217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_501217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501217 prefixEnd_501217 := by exact prefixLift 501217
  have htrace : WordTrace (prefixWord ++ tailWord_501217) baseStart_501217 baseEnd_501217 := by
    simpa [prefixWord, tailWord_501217, baseEnd_501217] using wordTrace_append hprefix tailTrace_501217
  have hstable : (prefixWord ++ tailWord_501217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501217).length < 2 ^ (prefixWord ++ tailWord_501217).sum := by decide
  have hdescent : baseEnd_501217 < baseStart_501217 := by decide
  rcases family_descends (prefixWord ++ tailWord_501217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501238 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_501238 : Nat := 118140960795 + 501238 * 2 ^ 59
def prefixEnd_501238 : Nat := 4983230072969 + 3 ^ 40 * 501238 * 2
def baseEnd_501238 : Nat := 228778681154146789084315

theorem tailTrace_501238 : CollatzResearch.WordTrace tailWord_501238 prefixEnd_501238 228778681154146789084315 := by
  unfold tailWord_501238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142603234881737842511023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12187767838738536986784245 1142603234881737842511023)
  ·
    refine ⟨1713904852322606763766535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142603234881737842511023 1713904852322606763766535)
    ·
      refine ⟨2570857278483910145649803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713904852322606763766535 2570857278483910145649803)
      ·
        refine ⟨3856285917725865218474705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570857278483910145649803 3856285917725865218474705)
        ·
          refine ⟨2892214438294398913856029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3856285917725865218474705 2892214438294398913856029)
          ·
            refine ⟨1084580414360399592696011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2892214438294398913856029 1084580414360399592696011)
            ·
              refine ⟨1626870621540599389044017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084580414360399592696011 1626870621540599389044017)
              ·
                refine ⟨1220152966155449541783013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626870621540599389044017 1220152966155449541783013)
                ·
                  refine ⟨228778681154146789084315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1220152966155449541783013 228778681154146789084315)
                  ·
                    rfl

theorem cell20_501238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_501238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501238 prefixEnd_501238 := by exact prefixLift 501238
  have htrace : WordTrace (prefixWord ++ tailWord_501238) baseStart_501238 baseEnd_501238 := by
    simpa [prefixWord, tailWord_501238, baseEnd_501238] using wordTrace_append hprefix tailTrace_501238
  have hstable : (prefixWord ++ tailWord_501238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501238).length < 2 ^ (prefixWord ++ tailWord_501238).sum := by decide
  have hdescent : baseEnd_501238 < baseStart_501238 := by decide
  rcases family_descends (prefixWord ++ tailWord_501238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501245 : List Nat := [1, 4, 1, 1, 1, 5, 3, 4]
def baseStart_501245 : Nat := 118140960795 + 501245 * 2 ^ 59
def prefixEnd_501245 : Nat := 4983230072969 + 3 ^ 40 * 501245 * 2
def baseEnd_501245 : Nat := 76260625381628625283651

theorem tailTrace_501245 : CollatzResearch.WordTrace tailWord_501245 prefixEnd_501245 76260625381628625283651 := by
  unfold tailWord_501245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18281907069082445675681189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12187938046054963783787459 18281907069082445675681189)
  ·
    refine ⟨3427857575452958564190223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18281907069082445675681189 3427857575452958564190223)
    ·
      refine ⟨5141786363179437846285335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427857575452958564190223 5141786363179437846285335)
      ·
        refine ⟨7712679544769156769428003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141786363179437846285335 7712679544769156769428003)
        ·
          refine ⟨11569019317153735154142005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712679544769156769428003 11569019317153735154142005)
          ·
            refine ⟨1084595560983162670700813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11569019317153735154142005 1084595560983162670700813)
            ·
              refine ⟨406723335368686001512805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1084595560983162670700813 406723335368686001512805)
              ·
                refine ⟨76260625381628625283651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406723335368686001512805 76260625381628625283651)
                ·
                  rfl

theorem cell20_501245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_501245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501245 prefixEnd_501245 := by exact prefixLift 501245
  have htrace : WordTrace (prefixWord ++ tailWord_501245) baseStart_501245 baseEnd_501245 := by
    simpa [prefixWord, tailWord_501245, baseEnd_501245] using wordTrace_append hprefix tailTrace_501245
  have hstable : (prefixWord ++ tailWord_501245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501245).length < 2 ^ (prefixWord ++ tailWord_501245).sum := by decide
  have hdescent : baseEnd_501245 < baseStart_501245 := by decide
  rcases family_descends (prefixWord ++ tailWord_501245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501255 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 2]
def baseStart_501255 : Nat := 118140960795 + 501255 * 2 ^ 59
def prefixEnd_501255 : Nat := 4983230072969 + 3 ^ 40 * 501255 * 2
def baseEnd_501255 : Nat := 228786440417370285517579

theorem tailTrace_501255 : CollatzResearch.WordTrace tailWord_501255 prefixEnd_501255 228786440417370285517579 := by
  unfold tailWord_501255
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282271799046217383545219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12188181199364144922363479 18282271799046217383545219)
  ·
    refine ⟨27423407698569326075317829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18282271799046217383545219 27423407698569326075317829)
    ·
      refine ⟨5141888943481748639122093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27423407698569326075317829 5141888943481748639122093)
      ·
        refine ⟨1928208353805655739670785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5141888943481748639122093 1928208353805655739670785)
        ·
          refine ⟨1446156265354241804753089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928208353805655739670785 1446156265354241804753089)
          ·
            refine ⟨1084617199015681353564817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446156265354241804753089 1084617199015681353564817)
            ·
              refine ⟨813462899261761015173613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084617199015681353564817 813462899261761015173613)
              ·
                refine ⟨305048587223160380690105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813462899261761015173613 305048587223160380690105)
                ·
                  refine ⟨228786440417370285517579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305048587223160380690105 228786440417370285517579)
                  ·
                    rfl

theorem cell20_501255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 2].length) (baseStart_501255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501255 prefixEnd_501255 := by exact prefixLift 501255
  have htrace : WordTrace (prefixWord ++ tailWord_501255) baseStart_501255 baseEnd_501255 := by
    simpa [prefixWord, tailWord_501255, baseEnd_501255] using wordTrace_append hprefix tailTrace_501255
  have hstable : (prefixWord ++ tailWord_501255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501255).length < 2 ^ (prefixWord ++ tailWord_501255).sum := by decide
  have hdescent : baseEnd_501255 < baseStart_501255 := by decide
  rcases family_descends (prefixWord ++ tailWord_501255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501269 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 3]
def baseStart_501269 : Nat := 118140960795 + 501269 * 2 ^ 59
def prefixEnd_501269 : Nat := 4983230072969 + 3 ^ 40 * 501269 * 2
def baseEnd_501269 : Nat := 228792830398848459050855

theorem tailTrace_501269 : CollatzResearch.WordTrace tailWord_501269 prefixEnd_501269 228792830398848459050855 := by
  unfold tailWord_501269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282782420995497774554861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12188521613996998516369907 18282782420995497774554861)
  ·
    refine ⟨6856043407873311665458073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18282782420995497774554861 6856043407873311665458073)
    ·
      refine ⟨5142032555904983749093555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6856043407873311665458073 5142032555904983749093555)
      ·
        refine ⟨7713048833857475623640333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5142032555904983749093555 7713048833857475623640333)
        ·
          refine ⟨2892393312696553358865125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7713048833857475623640333 2892393312696553358865125)
          ·
            refine ⟨542323746130603754787211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2892393312696553358865125 542323746130603754787211)
            ·
              refine ⟨813485619195905632180817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542323746130603754787211 813485619195905632180817)
              ·
                refine ⟨610114214396929224135613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813485619195905632180817 610114214396929224135613)
                ·
                  refine ⟨228792830398848459050855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610114214396929224135613 228792830398848459050855)
                  ·
                    rfl

theorem cell20_501269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_501269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501269 prefixEnd_501269 := by exact prefixLift 501269
  have htrace : WordTrace (prefixWord ++ tailWord_501269) baseStart_501269 baseEnd_501269 := by
    simpa [prefixWord, tailWord_501269, baseEnd_501269] using wordTrace_append hprefix tailTrace_501269
  have hstable : (prefixWord ++ tailWord_501269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501269).length < 2 ^ (prefixWord ++ tailWord_501269).sum := by decide
  have hdescent : baseEnd_501269 < baseStart_501269 := by decide
  rcases family_descends (prefixWord ++ tailWord_501269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501276 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 2]
def baseStart_501276 : Nat := 118140960795 + 501276 * 2 ^ 59
def prefixEnd_501276 : Nat := 4983230072969 + 3 ^ 40 * 501276 * 2
def baseEnd_501276 : Nat := 228796025389587545817493

theorem tailTrace_501276 : CollatzResearch.WordTrace tailWord_501276 prefixEnd_501276 228796025389587545817493 := by
  unfold tailWord_501276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141518865985068985029841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12188691821313425313373121 9141518865985068985029841)
  ·
    refine ⟨6856139149488801738772381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9141518865985068985029841 6856139149488801738772381)
    ·
      refine ⟨2571052181058300652039643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6856139149488801738772381 2571052181058300652039643)
      ·
        refine ⟨3856578271587450978059465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571052181058300652039643 3856578271587450978059465)
        ·
          refine ⟨2892433703690588233544599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3856578271587450978059465 2892433703690588233544599)
          ·
            refine ⟨4338650555535882350316899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892433703690588233544599 4338650555535882350316899)
            ·
              refine ⟨6507975833303823525475349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338650555535882350316899 6507975833303823525475349)
              ·
                refine ⟨305061367186116727756657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6507975833303823525475349 305061367186116727756657)
                ·
                  refine ⟨228796025389587545817493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305061367186116727756657 228796025389587545817493)
                  ·
                    rfl

theorem cell20_501276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_501276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501276 prefixEnd_501276 := by exact prefixLift 501276
  have htrace : WordTrace (prefixWord ++ tailWord_501276) baseStart_501276 baseEnd_501276 := by
    simpa [prefixWord, tailWord_501276, baseEnd_501276] using wordTrace_append hprefix tailTrace_501276
  have hstable : (prefixWord ++ tailWord_501276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501276).length < 2 ^ (prefixWord ++ tailWord_501276).sum := by decide
  have hdescent : baseEnd_501276 < baseStart_501276 := by decide
  rcases family_descends (prefixWord ++ tailWord_501276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501304 : List Nat := [2, 1, 2, 1, 4, 3, 1, 6]
def baseStart_501304 : Nat := 118140960795 + 501304 * 2 ^ 59
def prefixEnd_501304 : Nat := 4983230072969 + 3 ^ 40 * 501304 * 2
def baseEnd_501304 : Nat := 76269601784181297628015

theorem tailTrace_501304 : CollatzResearch.WordTrace tailWord_501304 prefixEnd_501304 76269601784181297628015 := by
  unfold tailWord_501304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142029487934349376039483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12189372650579132501385977 9142029487934349376039483)
  ·
    refine ⟨13713044231901524064059225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9142029487934349376039483 13713044231901524064059225)
    ·
      refine ⟨10284783173926143048044419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13713044231901524064059225 10284783173926143048044419)
      ·
        refine ⟨15427174760889214572066629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10284783173926143048044419 15427174760889214572066629)
        ·
          refine ⟨2892595267666727732262493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15427174760889214572066629 2892595267666727732262493)
          ·
            refine ⟨1084723225375022899598435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2892595267666727732262493 1084723225375022899598435)
            ·
              refine ⟨1627084838062534349397653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084723225375022899598435 1627084838062534349397653)
              ·
                refine ⟨76269601784181297628015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1627084838062534349397653 76269601784181297628015)
                ·
                  rfl

theorem cell20_501304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_501304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501304 prefixEnd_501304 := by exact prefixLift 501304
  have htrace : WordTrace (prefixWord ++ tailWord_501304) baseStart_501304 baseEnd_501304 := by
    simpa [prefixWord, tailWord_501304, baseEnd_501304] using wordTrace_append hprefix tailTrace_501304
  have hstable : (prefixWord ++ tailWord_501304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501304).length < 2 ^ (prefixWord ++ tailWord_501304).sum := by decide
  have hdescent : baseEnd_501304 < baseStart_501304 := by decide
  rcases family_descends (prefixWord ++ tailWord_501304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501311 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_501311 : Nat := 118140960795 + 501311 * 2 ^ 59
def prefixEnd_501311 : Nat := 4983230072969 + 3 ^ 40 * 501311 * 2
def baseEnd_501311 : Nat := 228812000343282979650683

theorem tailTrace_501311 : CollatzResearch.WordTrace tailWord_501311 prefixEnd_501311 228812000343282979650683 := by
  unfold tailWord_501311
  simp only [CollatzResearch.WordTrace]
  refine ⟨18284314286843338947583787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12189542857895559298389191 18284314286843338947583787)
  ·
    refine ⟨27426471430265008421375681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18284314286843338947583787 27426471430265008421375681)
    ·
      refine ⟨20569853572698756316031761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27426471430265008421375681 20569853572698756316031761)
      ·
        refine ⟨15427390179524067237023821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20569853572698756316031761 15427390179524067237023821)
        ·
          refine ⟨5785271317321525213883933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15427390179524067237023821 5785271317321525213883933)
          ·
            refine ⟨2169476743995571955206475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5785271317321525213883933 2169476743995571955206475)
            ·
              refine ⟨3254215115993357932809713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169476743995571955206475 3254215115993357932809713)
              ·
                refine ⟨2440661336995018449607285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3254215115993357932809713 2440661336995018449607285)
                ·
                  refine ⟨228812000343282979650683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2440661336995018449607285 228812000343282979650683)
                  ·
                    rfl

theorem cell20_501311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_501311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501311 prefixEnd_501311 := by exact prefixLift 501311
  have htrace : WordTrace (prefixWord ++ tailWord_501311) baseStart_501311 baseEnd_501311 := by
    simpa [prefixWord, tailWord_501311, baseEnd_501311] using wordTrace_append hprefix tailTrace_501311
  have hstable : (prefixWord ++ tailWord_501311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501311).length < 2 ^ (prefixWord ++ tailWord_501311).sum := by decide
  have hdescent : baseEnd_501311 < baseStart_501311 := by decide
  rcases family_descends (prefixWord ++ tailWord_501311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501335 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_501335 : Nat := 118140960795 + 501335 * 2 ^ 59
def prefixEnd_501335 : Nat := 4983230072969 + 3 ^ 40 * 501335 * 2
def baseEnd_501335 : Nat := 228822954597245562850585

theorem tailTrace_501335 : CollatzResearch.WordTrace tailWord_501335 prefixEnd_501335 228822954597245562850585 := by
  unfold tailWord_501335
  simp only [CollatzResearch.WordTrace]
  refine ⟨18285189638756391046457459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12190126425837594030971639 18285189638756391046457459)
  ·
    refine ⟨27427784458134586569686189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18285189638756391046457459 27427784458134586569686189)
    ·
      refine ⟨10285419171800469963632321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27427784458134586569686189 10285419171800469963632321)
      ·
        refine ⟨7714064378850352472724241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10285419171800469963632321 7714064378850352472724241)
        ·
          refine ⟨5785548284137764354543181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7714064378850352472724241 5785548284137764354543181)
          ·
            refine ⟨2169580606551661632953693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5785548284137764354543181 2169580606551661632953693)
            ·
              refine ⟨813592727456873112357635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2169580606551661632953693 813592727456873112357635)
              ·
                refine ⟨1220389091185309668536453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813592727456873112357635 1220389091185309668536453)
                ·
                  refine ⟨228822954597245562850585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1220389091185309668536453 228822954597245562850585)
                  ·
                    rfl

theorem cell20_501335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_501335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501335 prefixEnd_501335 := by exact prefixLift 501335
  have htrace : WordTrace (prefixWord ++ tailWord_501335) baseStart_501335 baseEnd_501335 := by
    simpa [prefixWord, tailWord_501335, baseEnd_501335] using wordTrace_append hprefix tailTrace_501335
  have hstable : (prefixWord ++ tailWord_501335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501335).length < 2 ^ (prefixWord ++ tailWord_501335).sum := by decide
  have hdescent : baseEnd_501335 < baseStart_501335 := by decide
  rcases family_descends (prefixWord ++ tailWord_501335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501356 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_501356 : Nat := 118140960795 + 501356 * 2 ^ 59
def prefixEnd_501356 : Nat := 4983230072969 + 3 ^ 40 * 501356 * 2
def baseEnd_501356 : Nat := 228832539569462823150499

theorem tailTrace_501356 : CollatzResearch.WordTrace tailWord_501356 prefixEnd_501356 228832539569462823150499 := by
  unfold tailWord_501356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9142977785840155816485961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12190637047786874421981281 9142977785840155816485961)
  ·
    refine ⟨6857233339380116862364471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9142977785840155816485961 6857233339380116862364471)
    ·
      refine ⟨10285850009070175293546707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857233339380116862364471 10285850009070175293546707)
      ·
        refine ⟨15428775013605262940320061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10285850009070175293546707 15428775013605262940320061)
        ·
          refine ⟨5785790630101973602620023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15428775013605262940320061 5785790630101973602620023)
          ·
            refine ⟨8678685945152960403930035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5785790630101973602620023 8678685945152960403930035)
            ·
              refine ⟨13018028917729440605895053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8678685945152960403930035 13018028917729440605895053)
              ·
                refine ⟨4881760844148540227210645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13018028917729440605895053 4881760844148540227210645)
                ·
                  refine ⟨228832539569462823150499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4881760844148540227210645 228832539569462823150499)
                  ·
                    rfl

theorem cell20_501356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_501356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501356 prefixEnd_501356 := by exact prefixLift 501356
  have htrace : WordTrace (prefixWord ++ tailWord_501356) baseStart_501356 baseEnd_501356 := by
    simpa [prefixWord, tailWord_501356, baseEnd_501356] using wordTrace_append hprefix tailTrace_501356
  have hstable : (prefixWord ++ tailWord_501356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501356).length < 2 ^ (prefixWord ++ tailWord_501356).sum := by decide
  have hdescent : baseEnd_501356 < baseStart_501356 := by decide
  rcases family_descends (prefixWord ++ tailWord_501356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501380 : List Nat := [2, 3, 2, 1, 4, 8]
def baseStart_501380 : Nat := 118140960795 + 501380 * 2 ^ 59
def prefixEnd_501380 : Nat := 4983230072969 + 3 ^ 40 * 501380 * 2
def baseEnd_501380 : Nat := 8475684956423163198163

theorem tailTrace_501380 : CollatzResearch.WordTrace tailWord_501380 prefixEnd_501380 8475684956423163198163 := by
  unfold tailWord_501380
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143415461796681865922797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12191220615728909154563729 9143415461796681865922797)
  ·
    refine ⟨3428780798173755699721049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9143415461796681865922797 3428780798173755699721049)
    ·
      refine ⟨2571585598630316774790787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3428780798173755699721049 2571585598630316774790787)
      ·
        refine ⟨3857378397945475162186181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571585598630316774790787 3857378397945475162186181)
        ·
          refine ⟨723258449614776592909909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3857378397945475162186181 723258449614776592909909)
          ·
            refine ⟨8475684956423163198163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 723258449614776592909909 8475684956423163198163)
            ·
              rfl

theorem cell20_501380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 8].length) (baseStart_501380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501380 prefixEnd_501380 := by exact prefixLift 501380
  have htrace : WordTrace (prefixWord ++ tailWord_501380) baseStart_501380 baseEnd_501380 := by
    simpa [prefixWord, tailWord_501380, baseEnd_501380] using wordTrace_append hprefix tailTrace_501380
  have hstable : (prefixWord ++ tailWord_501380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501380).length < 2 ^ (prefixWord ++ tailWord_501380).sum := by decide
  have hdescent : baseEnd_501380 < baseStart_501380 := by decide
  rcases family_descends (prefixWord ++ tailWord_501380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501386 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_501386 : Nat := 118140960795 + 501386 * 2 ^ 59
def prefixEnd_501386 : Nat := 4983230072969 + 3 ^ 40 * 501386 * 2
def baseEnd_501386 : Nat := 228846232386916052150377

theorem tailTrace_501386 : CollatzResearch.WordTrace tailWord_501386 prefixEnd_501386 228846232386916052150377 := by
  unfold tailWord_501386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571762440392906689141003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12191366507714417837709341 4571762440392906689141003)
  ·
    refine ⟨6857643660589360033711505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4571762440392906689141003 6857643660589360033711505)
    ·
      refine ⟨5143232745442020025283629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6857643660589360033711505 5143232745442020025283629)
      ·
        refine ⟨1928712279540757509481361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5143232745442020025283629 1928712279540757509481361)
        ·
          refine ⟨1446534209655568132111021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928712279540757509481361 1446534209655568132111021)
          ·
            refine ⟨542450328620838049541633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1446534209655568132111021 542450328620838049541633)
            ·
              refine ⟨406837746465628537156225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542450328620838049541633 406837746465628537156225)
              ·
                refine ⟨305128309849221402867169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406837746465628537156225 305128309849221402867169)
                ·
                  refine ⟨228846232386916052150377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305128309849221402867169 228846232386916052150377)
                  ·
                    rfl

theorem cell20_501386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_501386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501386 prefixEnd_501386 := by exact prefixLift 501386
  have htrace : WordTrace (prefixWord ++ tailWord_501386) baseStart_501386 baseEnd_501386 := by
    simpa [prefixWord, tailWord_501386, baseEnd_501386] using wordTrace_append hprefix tailTrace_501386
  have hstable : (prefixWord ++ tailWord_501386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501386).length < 2 ^ (prefixWord ++ tailWord_501386).sum := by decide
  have hdescent : baseEnd_501386 < baseStart_501386 := by decide
  rcases family_descends (prefixWord ++ tailWord_501386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501401 : List Nat := [1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_501401 : Nat := 118140960795 + 501401 * 2 ^ 59
def prefixEnd_501401 : Nat := 4983230072969 + 3 ^ 40 * 501401 * 2
def baseEnd_501401 : Nat := 76284359598547555550105

theorem tailTrace_501401 : CollatzResearch.WordTrace tailWord_501401 prefixEnd_501401 76284359598547555550105 := by
  unfold tailWord_501401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18287596856517284318360057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12191731237678189545573371 18287596856517284318360057)
  ·
    refine ⟨13715697642387963238770043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18287596856517284318360057 13715697642387963238770043)
    ·
      refine ⟨20573546463581944858155065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13715697642387963238770043 20573546463581944858155065)
      ·
        refine ⟨15430159847686458643616299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20573546463581944858155065 15430159847686458643616299)
        ·
          refine ⟨23145239771529687965424449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15430159847686458643616299 23145239771529687965424449)
          ·
            refine ⟨17358929828647265974068337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23145239771529687965424449 17358929828647265974068337)
            ·
              refine ⟨13019197371485449480551253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17358929828647265974068337 13019197371485449480551253)
              ·
                refine ⟨76284359598547555550105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13019197371485449480551253 76284359598547555550105)
                ·
                  rfl

theorem cell20_501401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_501401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501401 prefixEnd_501401 := by exact prefixLift 501401
  have htrace : WordTrace (prefixWord ++ tailWord_501401) baseStart_501401 baseEnd_501401 := by
    simpa [prefixWord, tailWord_501401, baseEnd_501401] using wordTrace_append hprefix tailTrace_501401
  have hstable : (prefixWord ++ tailWord_501401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501401).length < 2 ^ (prefixWord ++ tailWord_501401).sum := by decide
  have hdescent : baseEnd_501401 < baseStart_501401 := by decide
  rcases family_descends (prefixWord ++ tailWord_501401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501439 : List Nat := [1, 1, 2, 2, 2, 3, 9]
def baseStart_501439 : Nat := 118140960795 + 501439 * 2 ^ 59
def prefixEnd_501439 : Nat := 4983230072969 + 3 ^ 40 * 501439 * 2
def baseEnd_501439 : Nat := 25430047003453713709277

theorem tailTrace_501439 : CollatzResearch.WordTrace tailWord_501439 prefixEnd_501439 25430047003453713709277 := by
  unfold tailWord_501439
  simp only [CollatzResearch.WordTrace]
  refine ⟨18288982830379616808243371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12192655220253077872162247 18288982830379616808243371)
  ·
    refine ⟨27433474245569425212365057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18288982830379616808243371 27433474245569425212365057)
    ·
      refine ⟨20575105684177068909273793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27433474245569425212365057 20575105684177068909273793)
      ·
        refine ⟨15431329263132801681955345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20575105684177068909273793 15431329263132801681955345)
        ·
          refine ⟨11573496947349601261466509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15431329263132801681955345 11573496947349601261466509)
          ·
            refine ⟨4340061355256100473049941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11573496947349601261466509 4340061355256100473049941)
            ·
              refine ⟨25430047003453713709277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4340061355256100473049941 25430047003453713709277)
              ·
                rfl

theorem cell20_501439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_501439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501439 prefixEnd_501439 := by exact prefixLift 501439
  have htrace : WordTrace (prefixWord ++ tailWord_501439) baseStart_501439 baseEnd_501439 := by
    simpa [prefixWord, tailWord_501439, baseEnd_501439] using wordTrace_append hprefix tailTrace_501439
  have hstable : (prefixWord ++ tailWord_501439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501439).length < 2 ^ (prefixWord ++ tailWord_501439).sum := by decide
  have hdescent : baseEnd_501439 < baseStart_501439 := by decide
  rcases family_descends (prefixWord ++ tailWord_501439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501469 : List Nat := [1, 4, 3, 3, 1, 2, 2, 4]
def baseStart_501469 : Nat := 118140960795 + 501469 * 2 ^ 59
def prefixEnd_501469 : Nat := 4983230072969 + 3 ^ 40 * 501469 * 2
def baseEnd_501469 : Nat := 76294705282845550794457

theorem tailTrace_501469 : CollatzResearch.WordTrace tailWord_501469 prefixEnd_501469 76294705282845550794457 := by
  unfold tailWord_501469
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290077020270931931835461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12193384680180621287890307 18290077020270931931835461)
  ·
    refine ⟨3429389441300799737219149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18290077020270931931835461 3429389441300799737219149)
    ·
      refine ⟨1286021040487799901457181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3429389441300799737219149 1286021040487799901457181)
      ·
        refine ⟨482257890182924963046443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1286021040487799901457181 482257890182924963046443)
        ·
          refine ⟨723386835274387444569665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482257890182924963046443 723386835274387444569665)
          ·
            refine ⟨542540126455790583427249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723386835274387444569665 542540126455790583427249)
            ·
              refine ⟨406905094841842937570437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542540126455790583427249 406905094841842937570437)
              ·
                refine ⟨76294705282845550794457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406905094841842937570437 76294705282845550794457)
                ·
                  rfl

theorem cell20_501469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_501469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501469 prefixEnd_501469 := by exact prefixLift 501469
  have htrace : WordTrace (prefixWord ++ tailWord_501469) baseStart_501469 baseEnd_501469 := by
    simpa [prefixWord, tailWord_501469, baseEnd_501469] using wordTrace_append hprefix tailTrace_501469
  have hstable : (prefixWord ++ tailWord_501469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501469).length < 2 ^ (prefixWord ++ tailWord_501469).sum := by decide
  have hdescent : baseEnd_501469 < baseStart_501469 := by decide
  rcases family_descends (prefixWord ++ tailWord_501469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501479 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 2]
def baseStart_501479 : Nat := 118140960795 + 501479 * 2 ^ 59
def prefixEnd_501479 : Nat := 4983230072969 + 3 ^ 40 * 501479 * 2
def baseEnd_501479 : Nat := 228888680121021062049997

theorem tailTrace_501479 : CollatzResearch.WordTrace tailWord_501479 prefixEnd_501479 228888680121021062049997 := by
  unfold tailWord_501479
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290441750234703639699491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12193627833489802426466327 18290441750234703639699491)
  ·
    refine ⟨27435662625352055459549237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18290441750234703639699491 27435662625352055459549237)
    ·
      refine ⟨2572093371126755199332741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27435662625352055459549237 2572093371126755199332741)
      ·
        refine ⟨482267507086266599874889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2572093371126755199332741 482267507086266599874889)
        ·
          refine ⟨361700630314699949906167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482267507086266599874889 361700630314699949906167)
          ·
            refine ⟨542550945472049924859251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361700630314699949906167 542550945472049924859251)
            ·
              refine ⟨813826418208074887288877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542550945472049924859251 813826418208074887288877)
              ·
                refine ⟨305184906828028082733329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813826418208074887288877 305184906828028082733329)
                ·
                  refine ⟨228888680121021062049997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305184906828028082733329 228888680121021062049997)
                  ·
                    rfl

theorem cell20_501479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 2].length) (baseStart_501479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501479 prefixEnd_501479 := by exact prefixLift 501479
  have htrace : WordTrace (prefixWord ++ tailWord_501479) baseStart_501479 baseEnd_501479 := by
    simpa [prefixWord, tailWord_501479, baseEnd_501479] using wordTrace_append hprefix tailTrace_501479
  have hstable : (prefixWord ++ tailWord_501479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501479).length < 2 ^ (prefixWord ++ tailWord_501479).sum := by decide
  have hdescent : baseEnd_501479 < baseStart_501479 := by decide
  rcases family_descends (prefixWord ++ tailWord_501479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501494 : List Nat := [5, 1, 1, 1, 1, 3, 8]
def baseStart_501494 : Nat := 118140960795 + 501494 * 2 ^ 59
def prefixEnd_501494 : Nat := 4983230072969 + 3 ^ 40 * 501494 * 2
def baseEnd_501494 : Nat := 25432836281083075172215

theorem tailTrace_501494 : CollatzResearch.WordTrace tailWord_501494 prefixEnd_501494 25432836281083075172215 := by
  unfold tailWord_501494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1143186802823772575093471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12193992563453574134330357 1143186802823772575093471)
  ·
    refine ⟨1714780204235658862640207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1143186802823772575093471 1714780204235658862640207)
    ·
      refine ⟨2572170306353488293960311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714780204235658862640207 2572170306353488293960311)
      ·
        refine ⟨3858255459530232440940467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572170306353488293960311 3858255459530232440940467)
        ·
          refine ⟨5787383189295348661410701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858255459530232440940467 5787383189295348661410701)
          ·
            refine ⟨2170268695985755748029013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5787383189295348661410701 2170268695985755748029013)
            ·
              refine ⟨25432836281083075172215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2170268695985755748029013 25432836281083075172215)
              ·
                rfl

theorem cell20_501494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_501494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501494 prefixEnd_501494 := by exact prefixLift 501494
  have htrace : WordTrace (prefixWord ++ tailWord_501494) baseStart_501494 baseEnd_501494 := by
    simpa [prefixWord, tailWord_501494, baseEnd_501494] using wordTrace_append hprefix tailTrace_501494
  have hstable : (prefixWord ++ tailWord_501494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501494).length < 2 ^ (prefixWord ++ tailWord_501494).sum := by decide
  have hdescent : baseEnd_501494 < baseStart_501494 := by decide
  rcases family_descends (prefixWord ++ tailWord_501494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501511 : List Nat := [1, 1, 4, 4, 2, 1, 2, 5]
def baseStart_501511 : Nat := 118140960795 + 501511 * 2 ^ 59
def prefixEnd_501511 : Nat := 4983230072969 + 3 ^ 40 * 501511 * 2
def baseEnd_501511 : Nat := 76301095264323724327733

theorem tailTrace_501511 : CollatzResearch.WordTrace tailWord_501511 prefixEnd_501511 76301095264323724327733 := by
  unfold tailWord_501511
  simp only [CollatzResearch.WordTrace]
  refine ⟨18291608886118773104864387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12194405924079182069909591 18291608886118773104864387)
  ·
    refine ⟨27437413329178159657296581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18291608886118773104864387 27437413329178159657296581)
    ·
      refine ⟨5144514999220904935743109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27437413329178159657296581 5144514999220904935743109)
      ·
        refine ⟨964596562353919675451833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5144514999220904935743109 964596562353919675451833)
        ·
          refine ⟨723447421765439756588875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964596562353919675451833 723447421765439756588875)
          ·
            refine ⟨1085171132648159634883313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723447421765439756588875 1085171132648159634883313)
            ·
              refine ⟨813878349486119726162485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085171132648159634883313 813878349486119726162485)
              ·
                refine ⟨76301095264323724327733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 813878349486119726162485 76301095264323724327733)
                ·
                  rfl

theorem cell20_501511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_501511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501511 prefixEnd_501511 := by exact prefixLift 501511
  have htrace : WordTrace (prefixWord ++ tailWord_501511) baseStart_501511 baseEnd_501511 := by
    simpa [prefixWord, tailWord_501511, baseEnd_501511] using wordTrace_append hprefix tailTrace_501511
  have hstable : (prefixWord ++ tailWord_501511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501511).length < 2 ^ (prefixWord ++ tailWord_501511).sum := by decide
  have hdescent : baseEnd_501511 < baseStart_501511 := by decide
  rcases family_descends (prefixWord ++ tailWord_501511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501515 : List Nat := [1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_501515 : Nat := 118140960795 + 501515 * 2 ^ 59
def prefixEnd_501515 : Nat := 4983230072969 + 3 ^ 40 * 501515 * 2
def baseEnd_501515 : Nat := 76301703833988312283283

theorem tailTrace_501515 : CollatzResearch.WordTrace tailWord_501515 prefixEnd_501515 76301703833988312283283 := by
  unfold tailWord_501515
  simp only [CollatzResearch.WordTrace]
  refine ⟨18291754778104281788009999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12194503185402854525339999 18291754778104281788009999)
  ·
    refine ⟨27437632167156422682014999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18291754778104281788009999 27437632167156422682014999)
    ·
      refine ⟨41156448250734634023022499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27437632167156422682014999 41156448250734634023022499)
      ·
        refine ⟨61734672376101951034533749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41156448250734634023022499 61734672376101951034533749)
        ·
          refine ⟨5787625535259557909487539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61734672376101951034533749 5787625535259557909487539)
          ·
            refine ⟨8681438302889336864231309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787625535259557909487539 8681438302889336864231309)
            ·
              refine ⟨3255539363583501324086741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8681438302889336864231309 3255539363583501324086741)
              ·
                refine ⟨76301703833988312283283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3255539363583501324086741 76301703833988312283283)
                ·
                  rfl

theorem cell20_501515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_501515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501515 prefixEnd_501515 := by exact prefixLift 501515
  have htrace : WordTrace (prefixWord ++ tailWord_501515) baseStart_501515 baseEnd_501515 := by
    simpa [prefixWord, tailWord_501515, baseEnd_501515] using wordTrace_append hprefix tailTrace_501515
  have hstable : (prefixWord ++ tailWord_501515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501515).length < 2 ^ (prefixWord ++ tailWord_501515).sum := by decide
  have hdescent : baseEnd_501515 < baseStart_501515 := by decide
  rcases family_descends (prefixWord ++ tailWord_501515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501553 : List Nat := [1, 2, 2, 3, 2, 10]
def baseStart_501553 : Nat := 118140960795 + 501553 * 2 ^ 59
def prefixEnd_501553 : Nat := 4983230072969 + 3 ^ 40 * 501553 * 2
def baseEnd_501553 : Nat := 8478609471755766429001

theorem tailTrace_501553 : CollatzResearch.WordTrace tailWord_501553 prefixEnd_501553 8478609471755766429001 := by
  unfold tailWord_501553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293140751966614277893313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12195427167977742851928875 18293140751966614277893313)
  ·
    refine ⟨13719855563974960708419985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18293140751966614277893313 13719855563974960708419985)
    ·
      refine ⟨10289891672981220531314989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13719855563974960708419985 10289891672981220531314989)
      ·
        refine ⟨3858709377367957699243121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10289891672981220531314989 3858709377367957699243121)
        ·
          refine ⟨2894032033025968274432341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3858709377367957699243121 2894032033025968274432341)
          ·
            refine ⟨8478609471755766429001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2894032033025968274432341 8478609471755766429001)
            ·
              rfl

theorem cell20_501553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 10].length) (baseStart_501553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501553 prefixEnd_501553 := by exact prefixLift 501553
  have htrace : WordTrace (prefixWord ++ tailWord_501553) baseStart_501553 baseEnd_501553 := by
    simpa [prefixWord, tailWord_501553, baseEnd_501553] using wordTrace_append hprefix tailTrace_501553
  have hstable : (prefixWord ++ tailWord_501553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501553).length < 2 ^ (prefixWord ++ tailWord_501553).sum := by decide
  have hdescent : baseEnd_501553 < baseStart_501553 := by decide
  rcases family_descends (prefixWord ++ tailWord_501553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501577 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_501577 : Nat := 118140960795 + 501577 * 2 ^ 59
def prefixEnd_501577 : Nat := 4983230072969 + 3 ^ 40 * 501577 * 2
def baseEnd_501577 : Nat := 228933409991368276782929

theorem tailTrace_501577 : CollatzResearch.WordTrace tailWord_501577 prefixEnd_501577 228933409991368276782929 := by
  unfold tailWord_501577
  simp only [CollatzResearch.WordTrace]
  refine ⟨18294016103879666376766985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12196010735919777584511323 18294016103879666376766985)
  ·
    refine ⟨13720512077909749782575239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18294016103879666376766985 13720512077909749782575239)
    ·
      refine ⟨20580768116864624673862859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13720512077909749782575239 20580768116864624673862859)
      ·
        refine ⟨30871152175296937010794289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20580768116864624673862859 30871152175296937010794289)
        ·
          refine ⟨23153364131472702758095717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30871152175296937010794289 23153364131472702758095717)
          ·
            refine ⟨4341255774651131767142947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23153364131472702758095717 4341255774651131767142947)
            ·
              refine ⟨6511883661976697650714421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341255774651131767142947 6511883661976697650714421)
              ·
                refine ⟨610489093310315404754477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6511883661976697650714421 610489093310315404754477)
                ·
                  refine ⟨228933409991368276782929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610489093310315404754477 228933409991368276782929)
                  ·
                    rfl

theorem cell20_501577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_501577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501577 prefixEnd_501577 := by exact prefixLift 501577
  have htrace : WordTrace (prefixWord ++ tailWord_501577) baseStart_501577 baseEnd_501577 := by
    simpa [prefixWord, tailWord_501577, baseEnd_501577] using wordTrace_append hprefix tailTrace_501577
  have hstable : (prefixWord ++ tailWord_501577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501577).length < 2 ^ (prefixWord ++ tailWord_501577).sum := by decide
  have hdescent : baseEnd_501577 < baseStart_501577 := by decide
  rcases family_descends (prefixWord ++ tailWord_501577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501629 : List Nat := [1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_501629 : Nat := 118140960795 + 501629 * 2 ^ 59
def prefixEnd_501629 : Nat := 4983230072969 + 3 ^ 40 * 501629 * 2
def baseEnd_501629 : Nat := 76319048069429069016461

theorem tailTrace_501629 : CollatzResearch.WordTrace tailWord_501629 prefixEnd_501629 76319048069429069016461 := by
  unfold tailWord_501629
  simp only [CollatzResearch.WordTrace]
  refine ⟨18295912699691279257659941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12197275133127519505106627 18295912699691279257659941)
  ·
    refine ⟨3430483631192114860811239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18295912699691279257659941 3430483631192114860811239)
    ·
      refine ⟨5145725446788172291216859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430483631192114860811239 5145725446788172291216859)
      ·
        refine ⟨7718588170182258436825289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145725446788172291216859 7718588170182258436825289)
        ·
          refine ⟨5788941127636693827618967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7718588170182258436825289 5788941127636693827618967)
          ·
            refine ⟨8683411691455040741428451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5788941127636693827618967 8683411691455040741428451)
            ·
              refine ⟨13025117537182561112142677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683411691455040741428451 13025117537182561112142677)
              ·
                refine ⟨76319048069429069016461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13025117537182561112142677 76319048069429069016461)
                ·
                  rfl

theorem cell20_501629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_501629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501629 prefixEnd_501629 := by exact prefixLift 501629
  have htrace : WordTrace (prefixWord ++ tailWord_501629) baseStart_501629 baseEnd_501629 := by
    simpa [prefixWord, tailWord_501629, baseEnd_501629] using wordTrace_append hprefix tailTrace_501629
  have hstable : (prefixWord ++ tailWord_501629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501629).length < 2 ^ (prefixWord ++ tailWord_501629).sum := by decide
  have hdescent : baseEnd_501629 < baseStart_501629 := by decide
  rcases family_descends (prefixWord ++ tailWord_501629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501632 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_501632 : Nat := 118140960795 + 501632 * 2 ^ 59
def prefixEnd_501632 : Nat := 4983230072969 + 3 ^ 40 * 501632 * 2
def baseEnd_501632 : Nat := 228958513490032529949371

theorem tailTrace_501632 : CollatzResearch.WordTrace tailWord_501632 prefixEnd_501632 228958513490032529949371 := by
  unfold tailWord_501632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148011059340205385009575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12197348079120273846679433 9148011059340205385009575)
  ·
    refine ⟨13722016589010308077514363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9148011059340205385009575 13722016589010308077514363)
    ·
      refine ⟨20583024883515462116271545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13722016589010308077514363 20583024883515462116271545)
      ·
        refine ⟨15437268662636596587203659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20583024883515462116271545 15437268662636596587203659)
        ·
          refine ⟨23155902993954894880805489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15437268662636596587203659 23155902993954894880805489)
          ·
            refine ⟨17366927245466171160604117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23155902993954894880805489 17366927245466171160604117)
            ·
              refine ⟨407037357315613386576659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17366927245466171160604117 407037357315613386576659)
              ·
                refine ⟨610556035973420079864989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407037357315613386576659 610556035973420079864989)
                ·
                  refine ⟨228958513490032529949371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610556035973420079864989 228958513490032529949371)
                  ·
                    rfl

theorem cell20_501632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_501632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501632 prefixEnd_501632 := by exact prefixLift 501632
  have htrace : WordTrace (prefixWord ++ tailWord_501632) baseStart_501632 baseEnd_501632 := by
    simpa [prefixWord, tailWord_501632, baseEnd_501632] using wordTrace_append hprefix tailTrace_501632
  have hstable : (prefixWord ++ tailWord_501632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501632).length < 2 ^ (prefixWord ++ tailWord_501632).sum := by decide
  have hdescent : baseEnd_501632 < baseStart_501632 := by decide
  rcases family_descends (prefixWord ++ tailWord_501632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501642 : List Nat := [3, 1, 2, 4, 2, 2, 2, 4]
def baseStart_501642 : Nat := 118140960795 + 501642 * 2 ^ 59
def prefixEnd_501642 : Nat := 4983230072969 + 3 ^ 40 * 501642 * 2
def baseEnd_501642 : Nat := 76321025920838979871999

theorem tailTrace_501642 : CollatzResearch.WordTrace tailWord_501642 prefixEnd_501642 76321025920838979871999 := by
  unfold tailWord_501642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574096712161045619470795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12197591232429454985255453 4574096712161045619470795)
  ·
    refine ⟨6861145068241568429206193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574096712161045619470795 6861145068241568429206193)
    ·
      refine ⟨5145858801181176321904645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6861145068241568429206193 5145858801181176321904645)
      ·
        refine ⟨964848525221470560357121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5145858801181176321904645 964848525221470560357121)
        ·
          refine ⟨723636393916102920267841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964848525221470560357121 723636393916102920267841)
          ·
            refine ⟨542727295437077190200881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723636393916102920267841 542727295437077190200881)
            ·
              refine ⟨407045471577807892650661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542727295437077190200881 407045471577807892650661)
              ·
                refine ⟨76321025920838979871999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407045471577807892650661 76321025920838979871999)
                ·
                  rfl

theorem cell20_501642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_501642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501642 prefixEnd_501642 := by exact prefixLift 501642
  have htrace : WordTrace (prefixWord ++ tailWord_501642) baseStart_501642 baseEnd_501642 := by
    simpa [prefixWord, tailWord_501642, baseEnd_501642] using wordTrace_append hprefix tailTrace_501642
  have hstable : (prefixWord ++ tailWord_501642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501642).length < 2 ^ (prefixWord ++ tailWord_501642).sum := by decide
  have hdescent : baseEnd_501642 < baseStart_501642 := by decide
  rcases family_descends (prefixWord ++ tailWord_501642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501663 : List Nat := [1, 1, 2, 5, 4, 1, 6]
def baseStart_501663 : Nat := 118140960795 + 501663 * 2 ^ 59
def prefixEnd_501663 : Nat := 4983230072969 + 3 ^ 40 * 501663 * 2
def baseEnd_501663 : Nat := 25441406970526022212879

theorem tailTrace_501663 : CollatzResearch.WordTrace tailWord_501663 prefixEnd_501663 25441406970526022212879 := by
  unfold tailWord_501663
  simp only [CollatzResearch.WordTrace]
  refine ⟨18297152781568103064397643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12198101854378735376265095 18297152781568103064397643)
  ·
    refine ⟨27445729172352154596596465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18297152781568103064397643 27445729172352154596596465)
    ·
      refine ⟨20584296879264115947447349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27445729172352154596596465 20584296879264115947447349)
      ·
        refine ⟨1929777832431010870073189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20584296879264115947447349 1929777832431010870073189)
        ·
          refine ⟨361833343580814538138723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1929777832431010870073189 361833343580814538138723)
          ·
            refine ⟨542750015371221807208085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361833343580814538138723 542750015371221807208085)
            ·
              refine ⟨25441406970526022212879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 542750015371221807208085 25441406970526022212879)
              ·
                rfl

theorem cell20_501663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 6].length) (baseStart_501663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501663 prefixEnd_501663 := by exact prefixLift 501663
  have htrace : WordTrace (prefixWord ++ tailWord_501663) baseStart_501663 baseEnd_501663 := by
    simpa [prefixWord, tailWord_501663, baseEnd_501663] using wordTrace_append hprefix tailTrace_501663
  have hstable : (prefixWord ++ tailWord_501663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501663).length < 2 ^ (prefixWord ++ tailWord_501663).sum := by decide
  have hdescent : baseEnd_501663 < baseStart_501663 := by decide
  rcases family_descends (prefixWord ++ tailWord_501663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501712 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_501712 : Nat := 118140960795 + 501712 * 2 ^ 59
def prefixEnd_501712 : Nat := 4983230072969 + 3 ^ 40 * 501712 * 2
def baseEnd_501712 : Nat := 228995027669907807282377

theorem tailTrace_501712 : CollatzResearch.WordTrace tailWord_501712 prefixEnd_501712 228995027669907807282377 := by
  unfold tailWord_501712
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149469979195292216465695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12199293305593722955287593 9149469979195292216465695)
  ·
    refine ⟨13724204968792938324698543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149469979195292216465695 13724204968792938324698543)
    ·
      refine ⟨20586307453189407487047815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13724204968792938324698543 20586307453189407487047815)
      ·
        refine ⟨30879461179784111230571723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20586307453189407487047815 30879461179784111230571723)
        ·
          refine ⟨46319191769676166845857585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30879461179784111230571723 46319191769676166845857585)
          ·
            refine ⟨34739393827257125134393189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46319191769676166845857585 34739393827257125134393189)
            ·
              refine ⟨6513636342610710962698723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34739393827257125134393189 6513636342610710962698723)
              ·
                refine ⟨9770454513916066444048085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6513636342610710962698723 9770454513916066444048085)
                ·
                  refine ⟨228995027669907807282377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9770454513916066444048085 228995027669907807282377)
                  ·
                    rfl

theorem cell20_501712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_501712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501712 prefixEnd_501712 := by exact prefixLift 501712
  have htrace : WordTrace (prefixWord ++ tailWord_501712) baseStart_501712 baseEnd_501712 := by
    simpa [prefixWord, tailWord_501712, baseEnd_501712] using wordTrace_append hprefix tailTrace_501712
  have hstable : (prefixWord ++ tailWord_501712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501712).length < 2 ^ (prefixWord ++ tailWord_501712).sum := by decide
  have hdescent : baseEnd_501712 < baseStart_501712 := by decide
  rcases family_descends (prefixWord ++ tailWord_501712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501722 : List Nat := [3, 1, 1, 2, 6, 7]
def baseStart_501722 : Nat := 118140960795 + 501722 * 2 ^ 59
def prefixEnd_501722 : Nat := 4983230072969 + 3 ^ 40 * 501722 * 2
def baseEnd_501722 : Nat := 8481466368236748775889

theorem tailTrace_501722 : CollatzResearch.WordTrace tailWord_501722 prefixEnd_501722 8481466368236748775889 := by
  unfold tailWord_501722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574826172088589035198855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12199536458902904093863613 4574826172088589035198855)
  ·
    refine ⟨6862239258132883552798283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574826172088589035198855 6862239258132883552798283)
    ·
      refine ⟨10293358887199325329197425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6862239258132883552798283 10293358887199325329197425)
      ·
        refine ⟨7720019165399493996898069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10293358887199325329197425 7720019165399493996898069)
        ·
          refine ⟨361875898378101281104597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7720019165399493996898069 361875898378101281104597)
          ·
            refine ⟨8481466368236748775889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 361875898378101281104597 8481466368236748775889)
            ·
              rfl

theorem cell20_501722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 7].length) (baseStart_501722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501722 prefixEnd_501722 := by exact prefixLift 501722
  have htrace : WordTrace (prefixWord ++ tailWord_501722) baseStart_501722 baseEnd_501722 := by
    simpa [prefixWord, tailWord_501722, baseEnd_501722] using wordTrace_append hprefix tailTrace_501722
  have hstable : (prefixWord ++ tailWord_501722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501722).length < 2 ^ (prefixWord ++ tailWord_501722).sum := by decide
  have hdescent : baseEnd_501722 < baseStart_501722 := by decide
  rcases family_descends (prefixWord ++ tailWord_501722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501724 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 2]
def baseStart_501724 : Nat := 118140960795 + 501724 * 2 ^ 59
def prefixEnd_501724 : Nat := 4983230072969 + 3 ^ 40 * 501724 * 2
def baseEnd_501724 : Nat := 229000504796889098882329

theorem tailTrace_501724 : CollatzResearch.WordTrace tailWord_501724 prefixEnd_501724 229000504796889098882329 := by
  unfold tailWord_501724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149688817173555241184113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12199585089564740321578817 9149688817173555241184113)
  ·
    refine ⟨6862266612880166430888085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9149688817173555241184113 6862266612880166430888085)
    ·
      refine ⟨321668747478757801447879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6862266612880166430888085 321668747478757801447879)
      ·
        refine ⟨482503121218136702171819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321668747478757801447879 482503121218136702171819)
        ·
          refine ⟨723754681827205053257729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482503121218136702171819 723754681827205053257729)
          ·
            refine ⟨542816011370403789943297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723754681827205053257729 542816011370403789943297)
            ·
              refine ⟨407112008527802842457473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542816011370403789943297 407112008527802842457473)
              ·
                refine ⟨305334006395852131843105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407112008527802842457473 305334006395852131843105)
                ·
                  refine ⟨229000504796889098882329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305334006395852131843105 229000504796889098882329)
                  ·
                    rfl

theorem cell20_501724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_501724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501724 prefixEnd_501724 := by exact prefixLift 501724
  have htrace : WordTrace (prefixWord ++ tailWord_501724) baseStart_501724 baseEnd_501724 := by
    simpa [prefixWord, tailWord_501724, baseEnd_501724] using wordTrace_append hprefix tailTrace_501724
  have hstable : (prefixWord ++ tailWord_501724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501724).length < 2 ^ (prefixWord ++ tailWord_501724).sum := by decide
  have hdescent : baseEnd_501724 < baseStart_501724 := by decide
  rcases family_descends (prefixWord ++ tailWord_501724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501725 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_501725 : Nat := 118140960795 + 501725 * 2 ^ 59
def prefixEnd_501725 : Nat := 4983230072969 + 3 ^ 40 * 501725 * 2
def baseEnd_501725 : Nat := 229000961224137539848991

theorem tailTrace_501725 : CollatzResearch.WordTrace tailWord_501725 prefixEnd_501725 229000961224137539848991 := by
  unfold tailWord_501725
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299414107343487653154629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12199609404895658435436419 18299414107343487653154629)
  ·
    refine ⟨3431140145126903934966493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18299414107343487653154629 3431140145126903934966493)
    ·
      refine ⟨1286677554422588975612435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3431140145126903934966493 1286677554422588975612435)
      ·
        refine ⟨1930016331633883463418653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286677554422588975612435 1930016331633883463418653)
        ·
          refine ⟨723756124362706298781995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1930016331633883463418653 723756124362706298781995)
          ·
            refine ⟨1085634186544059448172993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723756124362706298781995 1085634186544059448172993)
            ·
              refine ⟨814225639908044586129745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085634186544059448172993 814225639908044586129745)
              ·
                refine ⟨610669229931033439597309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814225639908044586129745 610669229931033439597309)
                ·
                  refine ⟨229000961224137539848991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610669229931033439597309 229000961224137539848991)
                  ·
                    rfl

theorem cell20_501725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_501725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501725 prefixEnd_501725 := by exact prefixLift 501725
  have htrace : WordTrace (prefixWord ++ tailWord_501725) baseStart_501725 baseEnd_501725 := by
    simpa [prefixWord, tailWord_501725, baseEnd_501725] using wordTrace_append hprefix tailTrace_501725
  have hstable : (prefixWord ++ tailWord_501725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501725).length < 2 ^ (prefixWord ++ tailWord_501725).sum := by decide
  have hdescent : baseEnd_501725 < baseStart_501725 := by decide
  rcases family_descends (prefixWord ++ tailWord_501725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501729 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_501729 : Nat := 118140960795 + 501729 * 2 ^ 59
def prefixEnd_501729 : Nat := 4983230072969 + 3 ^ 40 * 501729 * 2
def baseEnd_501729 : Nat := 229002786933131303715641

theorem tailTrace_501729 : CollatzResearch.WordTrace tailWord_501729 prefixEnd_501729 229002786933131303715641 := by
  unfold tailWord_501729
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299559999328996336300241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12199706666219330890866827 18299559999328996336300241)
  ·
    refine ⟨13724669999496747252225181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18299559999328996336300241 13724669999496747252225181)
    ·
      refine ⟨5146751249811280219584443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13724669999496747252225181 5146751249811280219584443)
      ·
        refine ⟨7720126874716920329376665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5146751249811280219584443 7720126874716920329376665)
        ·
          refine ⟨5790095156037690247032499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7720126874716920329376665 5790095156037690247032499)
          ·
            refine ⟨8685142734056535370548749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790095156037690247032499 8685142734056535370548749)
            ·
              refine ⟨3256928525271200763955781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8685142734056535370548749 3256928525271200763955781)
              ·
                refine ⟨610674098488350143241709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3256928525271200763955781 610674098488350143241709)
                ·
                  refine ⟨229002786933131303715641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610674098488350143241709 229002786933131303715641)
                  ·
                    rfl

theorem cell20_501729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_501729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501729 prefixEnd_501729 := by exact prefixLift 501729
  have htrace : WordTrace (prefixWord ++ tailWord_501729) baseStart_501729 baseEnd_501729 := by
    simpa [prefixWord, tailWord_501729, baseEnd_501729] using wordTrace_append hprefix tailTrace_501729
  have hstable : (prefixWord ++ tailWord_501729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501729).length < 2 ^ (prefixWord ++ tailWord_501729).sum := by decide
  have hdescent : baseEnd_501729 < baseStart_501729 := by decide
  rcases family_descends (prefixWord ++ tailWord_501729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501736 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_501736 : Nat := 118140960795 + 501736 * 2 ^ 59
def prefixEnd_501736 : Nat := 4983230072969 + 3 ^ 40 * 501736 * 2
def baseEnd_501736 : Nat := 229005981923870390482279

theorem tailTrace_501736 : CollatzResearch.WordTrace tailWord_501736 prefixEnd_501736 229005981923870390482279 := by
  unfold tailWord_501736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149907655151818265902531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12199876873535757687870041 9149907655151818265902531)
  ·
    refine ⟨13724861482727727398853797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149907655151818265902531 13724861482727727398853797)
    ·
      refine ⟨2573411528011448887285087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13724861482727727398853797 2573411528011448887285087)
      ·
        refine ⟨3860117292017173330927631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573411528011448887285087 3860117292017173330927631)
        ·
          refine ⟨5790175938025759996391447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860117292017173330927631 5790175938025759996391447)
          ·
            refine ⟨8685263907038639994587171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790175938025759996391447 8685263907038639994587171)
            ·
              refine ⟨13027895860557959991880757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685263907038639994587171 13027895860557959991880757)
              ·
                refine ⟨1221365236927308749238821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13027895860557959991880757 1221365236927308749238821)
                ·
                  refine ⟨229005981923870390482279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1221365236927308749238821 229005981923870390482279)
                  ·
                    rfl

theorem cell20_501736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_501736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501736 prefixEnd_501736 := by exact prefixLift 501736
  have htrace : WordTrace (prefixWord ++ tailWord_501736) baseStart_501736 baseEnd_501736 := by
    simpa [prefixWord, tailWord_501736, baseEnd_501736] using wordTrace_append hprefix tailTrace_501736
  have hstable : (prefixWord ++ tailWord_501736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501736).length < 2 ^ (prefixWord ++ tailWord_501736).sum := by decide
  have hdescent : baseEnd_501736 < baseStart_501736 := by decide
  rcases family_descends (prefixWord ++ tailWord_501736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501774 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_501774 : Nat := 118140960795 + 501774 * 2 ^ 59
def prefixEnd_501774 : Nat := 4983230072969 + 3 ^ 40 * 501774 * 2
def baseEnd_501774 : Nat := 229023326159311147215457

theorem tailTrace_501774 : CollatzResearch.WordTrace tailWord_501774 prefixEnd_501774 229023326159311147215457 := by
  unfold tailWord_501774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287650160520746127711047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12200800856110646014458917 2287650160520746127711047)
  ·
    refine ⟨3431475240781119191566571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287650160520746127711047 3431475240781119191566571)
    ·
      refine ⟨5147212861171678787349857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431475240781119191566571 5147212861171678787349857)
      ·
        refine ⟨3860409645878759090512393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5147212861171678787349857 3860409645878759090512393)
        ·
          refine ⟨2895307234409069317884295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3860409645878759090512393 2895307234409069317884295)
          ·
            refine ⟨4342960851613603976826443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2895307234409069317884295 4342960851613603976826443)
            ·
              refine ⟨6514441277420405965239665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4342960851613603976826443 6514441277420405965239665)
              ·
                refine ⟨4885830958065304473929749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6514441277420405965239665 4885830958065304473929749)
                ·
                  refine ⟨229023326159311147215457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4885830958065304473929749 229023326159311147215457)
                  ·
                    rfl

theorem cell20_501774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_501774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501774 prefixEnd_501774 := by exact prefixLift 501774
  have htrace : WordTrace (prefixWord ++ tailWord_501774) baseStart_501774 baseEnd_501774 := by
    simpa [prefixWord, tailWord_501774, baseEnd_501774] using wordTrace_append hprefix tailTrace_501774
  have hstable : (prefixWord ++ tailWord_501774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501774).length < 2 ^ (prefixWord ++ tailWord_501774).sum := by decide
  have hdescent : baseEnd_501774 < baseStart_501774 := by decide
  rcases family_descends (prefixWord ++ tailWord_501774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501791 : List Nat := [1, 1, 2, 4, 1, 2, 1, 6, 2]
def baseStart_501791 : Nat := 118140960795 + 501791 * 2 ^ 59
def prefixEnd_501791 : Nat := 4983230072969 + 3 ^ 40 * 501791 * 2
def baseEnd_501791 : Nat := 229031085422534643648721

theorem tailTrace_501791 : CollatzResearch.WordTrace tailWord_501791 prefixEnd_501791 229031085422534643648721 := by
  unfold tailWord_501791
  simp only [CollatzResearch.WordTrace]
  refine ⟨18301821325104380925057227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12201214216736253950038151 18301821325104380925057227)
  ·
    refine ⟨27452731987656571387585841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18301821325104380925057227 27452731987656571387585841)
    ·
      refine ⟨20589548990742428540689381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27452731987656571387585841 20589548990742428540689381)
      ·
        refine ⟨3860540435764205351379259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20589548990742428540689381 3860540435764205351379259)
        ·
          refine ⟨5790810653646308027068889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860540435764205351379259 5790810653646308027068889)
          ·
            refine ⟨4343107990234731020301667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5790810653646308027068889 4343107990234731020301667)
            ·
              refine ⟨6514661985352096530452501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343107990234731020301667 6514661985352096530452501)
              ·
                refine ⟨305374780563379524864961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6514661985352096530452501 305374780563379524864961)
                ·
                  refine ⟨229031085422534643648721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305374780563379524864961 229031085422534643648721)
                  ·
                    rfl

theorem cell20_501791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 2].length) (baseStart_501791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501791 prefixEnd_501791 := by exact prefixLift 501791
  have htrace : WordTrace (prefixWord ++ tailWord_501791) baseStart_501791 baseEnd_501791 := by
    simpa [prefixWord, tailWord_501791, baseEnd_501791] using wordTrace_append hprefix tailTrace_501791
  have hstable : (prefixWord ++ tailWord_501791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501791).length < 2 ^ (prefixWord ++ tailWord_501791).sum := by decide
  have hdescent : baseEnd_501791 < baseStart_501791 := by decide
  rcases family_descends (prefixWord ++ tailWord_501791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501825 : List Nat := [1, 2, 5, 1, 2, 3, 1, 3, 2]
def baseStart_501825 : Nat := 118140960795 + 501825 * 2 ^ 59
def prefixEnd_501825 : Nat := 4983230072969 + 3 ^ 40 * 501825 * 2
def baseEnd_501825 : Nat := 229046603948981636515249

theorem tailTrace_501825 : CollatzResearch.WordTrace tailWord_501825 prefixEnd_501825 229046603948981636515249 := by
  unfold tailWord_501825
  simp only [CollatzResearch.WordTrace]
  refine ⟨18303061406981204731794929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12202040937987469821196619 18303061406981204731794929)
  ·
    refine ⟨13727296055235903548846197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18303061406981204731794929 13727296055235903548846197)
    ·
      refine ⟨1286934005178365957704331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13727296055235903548846197 1286934005178365957704331)
      ·
        refine ⟨1930401007767548936556497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286934005178365957704331 1930401007767548936556497)
        ·
          refine ⟨1447800755825661702417373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930401007767548936556497 1447800755825661702417373)
          ·
            refine ⟨542925283434623138406515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1447800755825661702417373 542925283434623138406515)
            ·
              refine ⟨814387925151934707609773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542925283434623138406515 814387925151934707609773)
              ·
                refine ⟨305395471931975515353665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814387925151934707609773 305395471931975515353665)
                ·
                  refine ⟨229046603948981636515249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305395471931975515353665 229046603948981636515249)
                  ·
                    rfl

theorem cell20_501825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_501825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501825 prefixEnd_501825 := by exact prefixLift 501825
  have htrace : WordTrace (prefixWord ++ tailWord_501825) baseStart_501825 baseEnd_501825 := by
    simpa [prefixWord, tailWord_501825, baseEnd_501825] using wordTrace_append hprefix tailTrace_501825
  have hstable : (prefixWord ++ tailWord_501825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501825).length < 2 ^ (prefixWord ++ tailWord_501825).sum := by decide
  have hdescent : baseEnd_501825 < baseStart_501825 := by decide
  rcases family_descends (prefixWord ++ tailWord_501825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501853 : List Nat := [1, 4, 4, 1, 1, 2, 2, 5]
def baseStart_501853 : Nat := 118140960795 + 501853 * 2 ^ 59
def prefixEnd_501853 : Nat := 4983230072969 + 3 ^ 40 * 501853 * 2
def baseEnd_501853 : Nat := 76353127970645994527267

theorem tailTrace_501853 : CollatzResearch.WordTrace tailWord_501853 prefixEnd_501853 76353127970645994527267 := by
  unfold tailWord_501853
  simp only [CollatzResearch.WordTrace]
  refine ⟨18304082650879765513814213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12202721767253177009209475 18304082650879765513814213)
  ·
    refine ⟨3432015497039956033840165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18304082650879765513814213 3432015497039956033840165)
    ·
      refine ⟨643502905694991756345031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3432015497039956033840165 643502905694991756345031)
      ·
        refine ⟨965254358542487634517547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643502905694991756345031 965254358542487634517547)
        ·
          refine ⟨1447881537813731451776321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965254358542487634517547 1447881537813731451776321)
          ·
            refine ⟨1085911153360298588832241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1447881537813731451776321 1085911153360298588832241)
            ·
              refine ⟨814433365020223941624181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085911153360298588832241 814433365020223941624181)
              ·
                refine ⟨76353127970645994527267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814433365020223941624181 76353127970645994527267)
                ·
                  rfl

theorem cell20_501853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_501853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501853 prefixEnd_501853 := by exact prefixLift 501853
  have htrace : WordTrace (prefixWord ++ tailWord_501853) baseStart_501853 baseEnd_501853 := by
    simpa [prefixWord, tailWord_501853, baseEnd_501853] using wordTrace_append hprefix tailTrace_501853
  have hstable : (prefixWord ++ tailWord_501853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501853).length < 2 ^ (prefixWord ++ tailWord_501853).sum := by decide
  have hdescent : baseEnd_501853 < baseStart_501853 := by decide
  rcases family_descends (prefixWord ++ tailWord_501853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501860 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_501860 : Nat := 118140960795 + 501860 * 2 ^ 59
def prefixEnd_501860 : Nat := 4983230072969 + 3 ^ 40 * 501860 * 2
def baseEnd_501860 : Nat := 229062578902677070348439

theorem tailTrace_501860 : CollatzResearch.WordTrace tailWord_501860 prefixEnd_501860 229062578902677070348439 := by
  unfold tailWord_501860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152168980927202854659517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12202891974569603806212689 9152168980927202854659517)
  ·
    refine ⟨3432063367847701070497319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9152168980927202854659517 3432063367847701070497319)
    ·
      refine ⟨5148095051771551605745979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432063367847701070497319 5148095051771551605745979)
      ·
        refine ⟨7722142577657327408618969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148095051771551605745979 7722142577657327408618969)
        ·
          refine ⟨5791606933242995556464227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7722142577657327408618969 5791606933242995556464227)
          ·
            refine ⟨8687410399864493334696341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791606933242995556464227 8687410399864493334696341)
            ·
              refine ⟨407222362493648125063891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8687410399864493334696341 407222362493648125063891)
              ·
                refine ⟨610833543740472187595837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407222362493648125063891 610833543740472187595837)
                ·
                  refine ⟨229062578902677070348439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610833543740472187595837 229062578902677070348439)
                  ·
                    rfl

theorem cell20_501860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_501860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501860 prefixEnd_501860 := by exact prefixLift 501860
  have htrace : WordTrace (prefixWord ++ tailWord_501860) baseStart_501860 baseEnd_501860 := by
    simpa [prefixWord, tailWord_501860, baseEnd_501860] using wordTrace_append hprefix tailTrace_501860
  have hstable : (prefixWord ++ tailWord_501860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501860).length < 2 ^ (prefixWord ++ tailWord_501860).sum := by decide
  have hdescent : baseEnd_501860 < baseStart_501860 := by decide
  rcases family_descends (prefixWord ++ tailWord_501860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501898 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_501898 : Nat := 118140960795 + 501898 * 2 ^ 59
def prefixEnd_501898 : Nat := 4983230072969 + 3 ^ 40 * 501898 * 2
def baseEnd_501898 : Nat := 229079923138117827081617

theorem tailTrace_501898 : CollatzResearch.WordTrace tailWord_501898 prefixEnd_501898 229079923138117827081617 := by
  unfold tailWord_501898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576430983929184549800587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12203815957144492132801565 4576430983929184549800587)
  ·
    refine ⟨6864646475893776824700881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4576430983929184549800587 6864646475893776824700881)
    ·
      refine ⟨5148484856920332618525661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6864646475893776824700881 5148484856920332618525661)
      ·
        refine ⟨1930681821345124731947123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5148484856920332618525661 1930681821345124731947123)
        ·
          refine ⟨2896022732017687097920685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930681821345124731947123 2896022732017687097920685)
          ·
            refine ⟨1086008524506632661720257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2896022732017687097920685 1086008524506632661720257)
            ·
              refine ⟨814506393379974496290193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086008524506632661720257 814506393379974496290193)
              ·
                refine ⟨610879795034980872217645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814506393379974496290193 610879795034980872217645)
                ·
                  refine ⟨229079923138117827081617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610879795034980872217645 229079923138117827081617)
                  ·
                    rfl

theorem cell20_501898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_501898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501898 prefixEnd_501898 := by exact prefixLift 501898
  have htrace : WordTrace (prefixWord ++ tailWord_501898) baseStart_501898 baseEnd_501898 := by
    simpa [prefixWord, tailWord_501898, baseEnd_501898] using wordTrace_append hprefix tailTrace_501898
  have hstable : (prefixWord ++ tailWord_501898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501898).length < 2 ^ (prefixWord ++ tailWord_501898).sum := by decide
  have hdescent : baseEnd_501898 < baseStart_501898 := by decide
  rcases family_descends (prefixWord ++ tailWord_501898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501908 : List Nat := [2, 4, 2, 3, 1, 2, 1, 5]
def baseStart_501908 : Nat := 118140960795 + 501908 * 2 ^ 59
def prefixEnd_501908 : Nat := 4983230072969 + 3 ^ 40 * 501908 * 2
def baseEnd_501908 : Nat := 76361495803534078916081

theorem tailTrace_501908 : CollatzResearch.WordTrace tailWord_501908 prefixEnd_501908 76361495803534078916081 := by
  unfold tailWord_501908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153044332840254953533189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12204059110453673271377585 9153044332840254953533189)
  ·
    refine ⟨1716195812407547803787473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9153044332840254953533189 1716195812407547803787473)
    ·
      refine ⟨1287146859305660852840605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1716195812407547803787473 1287146859305660852840605)
      ·
        refine ⟨482680072239622819815227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1287146859305660852840605 482680072239622819815227)
        ·
          refine ⟨724020108359434229722841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482680072239622819815227 724020108359434229722841)
          ·
            refine ⟨543015081269575672292131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724020108359434229722841 543015081269575672292131)
            ·
              refine ⟨814522621904363508438197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543015081269575672292131 814522621904363508438197)
              ·
                refine ⟨76361495803534078916081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814522621904363508438197 76361495803534078916081)
                ·
                  rfl

theorem cell20_501908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_501908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501908 prefixEnd_501908 := by exact prefixLift 501908
  have htrace : WordTrace (prefixWord ++ tailWord_501908) baseStart_501908 baseEnd_501908 := by
    simpa [prefixWord, tailWord_501908, baseEnd_501908] using wordTrace_append hprefix tailTrace_501908
  have hstable : (prefixWord ++ tailWord_501908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501908).length < 2 ^ (prefixWord ++ tailWord_501908).sum := by decide
  have hdescent : baseEnd_501908 < baseStart_501908 := by decide
  rcases family_descends (prefixWord ++ tailWord_501908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501943 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 2]
def baseStart_501943 : Nat := 118140960795 + 501943 * 2 ^ 59
def prefixEnd_501943 : Nat := 4983230072969 + 3 ^ 40 * 501943 * 2
def baseEnd_501943 : Nat := 229100462364297670581433

theorem tailTrace_501943 : CollatzResearch.WordTrace tailWord_501943 prefixEnd_501943 229100462364297670581433 := by
  unfold tailWord_501943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18307365220553710884590483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12204910147035807256393655 18307365220553710884590483)
  ·
    refine ⟨27461047830830566326885725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18307365220553710884590483 27461047830830566326885725)
    ·
      refine ⟨10297892936561462372582147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27461047830830566326885725 10297892936561462372582147)
      ·
        refine ⟨15446839404842193558873221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10297892936561462372582147 15446839404842193558873221)
        ·
          refine ⟨2896282388407911292288729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15446839404842193558873221 2896282388407911292288729)
          ·
            refine ⟨2172211791305933469216547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2896282388407911292288729 2172211791305933469216547)
            ·
              refine ⟨3258317686958900203824821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172211791305933469216547 3258317686958900203824821)
              ·
                refine ⟨305467283152396894108577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3258317686958900203824821 305467283152396894108577)
                ·
                  refine ⟨229100462364297670581433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305467283152396894108577 229100462364297670581433)
                  ·
                    rfl

theorem cell20_501943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 2].length) (baseStart_501943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501943 prefixEnd_501943 := by exact prefixLift 501943
  have htrace : WordTrace (prefixWord ++ tailWord_501943) baseStart_501943 baseEnd_501943 := by
    simpa [prefixWord, tailWord_501943, baseEnd_501943] using wordTrace_append hprefix tailTrace_501943
  have hstable : (prefixWord ++ tailWord_501943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501943).length < 2 ^ (prefixWord ++ tailWord_501943).sum := by decide
  have hdescent : baseEnd_501943 < baseStart_501943 := by decide
  rcases family_descends (prefixWord ++ tailWord_501943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501947 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_501947 : Nat := 118140960795 + 501947 * 2 ^ 59
def prefixEnd_501947 : Nat := 4983230072969 + 3 ^ 40 * 501947 * 2
def baseEnd_501947 : Nat := 229102288073291434448083

theorem tailTrace_501947 : CollatzResearch.WordTrace tailWord_501947 prefixEnd_501947 229102288073291434448083 := by
  unfold tailWord_501947
  simp only [CollatzResearch.WordTrace]
  refine ⟨18307511112539219567736095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12205007408359479711824063 18307511112539219567736095)
  ·
    refine ⟨27461266668808829351604143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18307511112539219567736095 27461266668808829351604143)
    ·
      refine ⟨41191900003213244027406215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27461266668808829351604143 41191900003213244027406215)
      ·
        refine ⟨61787850004819866041109323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41191900003213244027406215 61787850004819866041109323)
        ·
          refine ⟨92681775007229799061663985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61787850004819866041109323 92681775007229799061663985)
          ·
            refine ⟨69511331255422349296247989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92681775007229799061663985 69511331255422349296247989)
            ·
              refine ⟨6516687305195845246523249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69511331255422349296247989 6516687305195845246523249)
              ·
                refine ⟨4887515478896883934892437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516687305195845246523249 4887515478896883934892437)
                ·
                  refine ⟨229102288073291434448083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4887515478896883934892437 229102288073291434448083)
                  ·
                    rfl

theorem cell20_501947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_501947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501947 prefixEnd_501947 := by exact prefixLift 501947
  have htrace : WordTrace (prefixWord ++ tailWord_501947) baseStart_501947 baseEnd_501947 := by
    simpa [prefixWord, tailWord_501947, baseEnd_501947] using wordTrace_append hprefix tailTrace_501947
  have hstable : (prefixWord ++ tailWord_501947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501947).length < 2 ^ (prefixWord ++ tailWord_501947).sum := by decide
  have hdescent : baseEnd_501947 < baseStart_501947 := by decide
  rcases family_descends (prefixWord ++ tailWord_501947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501950 : List Nat := [4, 2, 1, 1, 4, 1, 7]
def baseStart_501950 : Nat := 118140960795 + 501950 * 2 ^ 59
def prefixEnd_501950 : Nat := 4983230072969 + 3 ^ 40 * 501950 * 2
def baseEnd_501950 : Nat := 25455961928337417483119

theorem tailTrace_501950 : CollatzResearch.WordTrace tailWord_501950 prefixEnd_501950 25455961928337417483119 := by
  unfold tailWord_501950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288452566441043885011913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12205080354352234053396869 2288452566441043885011913)
  ·
    refine ⟨1716339424830782913758935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2288452566441043885011913 1716339424830782913758935)
    ·
      refine ⟨2574509137246174370638403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716339424830782913758935 2574509137246174370638403)
      ·
        refine ⟨3861763705869261555957605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574509137246174370638403 3861763705869261555957605)
        ·
          refine ⟨724080694850486541742051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3861763705869261555957605 724080694850486541742051)
          ·
            refine ⟨1086121042275729812613077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724080694850486541742051 1086121042275729812613077)
            ·
              refine ⟨25455961928337417483119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1086121042275729812613077 25455961928337417483119)
              ·
                rfl

theorem cell20_501950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 7].length) (baseStart_501950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501950 prefixEnd_501950 := by exact prefixLift 501950
  have htrace : WordTrace (prefixWord ++ tailWord_501950) baseStart_501950 baseEnd_501950 := by
    simpa [prefixWord, tailWord_501950, baseEnd_501950] using wordTrace_append hprefix tailTrace_501950
  have hstable : (prefixWord ++ tailWord_501950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501950).length < 2 ^ (prefixWord ++ tailWord_501950).sum := by decide
  have hdescent : baseEnd_501950 < baseStart_501950 := by decide
  rcases family_descends (prefixWord ++ tailWord_501950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501957 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_501957 : Nat := 118140960795 + 501957 * 2 ^ 59
def prefixEnd_501957 : Nat := 4983230072969 + 3 ^ 40 * 501957 * 2
def baseEnd_501957 : Nat := 229106852345775844114709

theorem tailTrace_501957 : CollatzResearch.WordTrace tailWord_501957 prefixEnd_501957 229106852345775844114709 := by
  unfold tailWord_501957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18307875842502991275600125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12205250561668660850400083 18307875842502991275600125)
  ·
    refine ⟨6865453440938621728350047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18307875842502991275600125 6865453440938621728350047)
    ·
      refine ⟨10298180161407932592525071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6865453440938621728350047 10298180161407932592525071)
      ·
        refine ⟨15447270242111898888787607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298180161407932592525071 15447270242111898888787607)
        ·
          refine ⟨23170905363167848333181411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15447270242111898888787607 23170905363167848333181411)
          ·
            refine ⟨34756358044751772499772117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23170905363167848333181411 34756358044751772499772117)
            ·
              refine ⟨814602141673869667963409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34756358044751772499772117 814602141673869667963409)
              ·
                refine ⟨610951606255402250972557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814602141673869667963409 610951606255402250972557)
                ·
                  refine ⟨229106852345775844114709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610951606255402250972557 229106852345775844114709)
                  ·
                    rfl

theorem cell20_501957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_501957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501957 prefixEnd_501957 := by exact prefixLift 501957
  have htrace : WordTrace (prefixWord ++ tailWord_501957) baseStart_501957 baseEnd_501957 := by
    simpa [prefixWord, tailWord_501957, baseEnd_501957] using wordTrace_append hprefix tailTrace_501957
  have hstable : (prefixWord ++ tailWord_501957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501957).length < 2 ^ (prefixWord ++ tailWord_501957).sum := by decide
  have hdescent : baseEnd_501957 < baseStart_501957 := by decide
  rcases family_descends (prefixWord ++ tailWord_501957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501981 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_501981 : Nat := 118140960795 + 501981 * 2 ^ 59
def prefixEnd_501981 : Nat := 4983230072969 + 3 ^ 40 * 501981 * 2
def baseEnd_501981 : Nat := 229117806599738427314611

theorem tailTrace_501981 : CollatzResearch.WordTrace tailWord_501981 prefixEnd_501981 229117806599738427314611 := by
  unfold tailWord_501981
  simp only [CollatzResearch.WordTrace]
  refine ⟨18308751194416043374473797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12205834129610695582982531 18308751194416043374473797)
  ·
    refine ⟨3432890848953008132713837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18308751194416043374473797 3432890848953008132713837)
    ·
      refine ⟨1287334068357378049767689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3432890848953008132713837 1287334068357378049767689)
      ·
        refine ⟨965500551268033537325767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1287334068357378049767689 965500551268033537325767)
        ·
          refine ⟨1448250826902050305988651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965500551268033537325767 1448250826902050305988651)
          ·
            refine ⟨2172376240353075458982977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448250826902050305988651 2172376240353075458982977)
            ·
              refine ⟨1629282180264806594237233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172376240353075458982977 1629282180264806594237233)
              ·
                refine ⟨1221961635198604945677925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629282180264806594237233 1221961635198604945677925)
                ·
                  refine ⟨229117806599738427314611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1221961635198604945677925 229117806599738427314611)
                  ·
                    rfl

theorem cell20_501981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_501981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_501981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_501981 prefixEnd_501981 := by exact prefixLift 501981
  have htrace : WordTrace (prefixWord ++ tailWord_501981) baseStart_501981 baseEnd_501981 := by
    simpa [prefixWord, tailWord_501981, baseEnd_501981] using wordTrace_append hprefix tailTrace_501981
  have hstable : (prefixWord ++ tailWord_501981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501981).length < 2 ^ (prefixWord ++ tailWord_501981).sum := by decide
  have hdescent : baseEnd_501981 < baseStart_501981 := by decide
  rcases family_descends (prefixWord ++ tailWord_501981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502016 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_502016 : Nat := 118140960795 + 502016 * 2 ^ 59
def prefixEnd_502016 : Nat := 4983230072969 + 3 ^ 40 * 502016 * 2
def baseEnd_502016 : Nat := 229133781553433861147801

theorem tailTrace_502016 : CollatzResearch.WordTrace tailWord_502016 prefixEnd_502016 229133781553433861147801 := by
  unfold tailWord_502016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155013874644622175998951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12206685166192829567998601 9155013874644622175998951)
  ·
    refine ⟨13732520811966933263998427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9155013874644622175998951 13732520811966933263998427)
    ·
      refine ⟨20598781217950399895997641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13732520811966933263998427 20598781217950399895997641)
      ·
        refine ⟨15449085913462799921998231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20598781217950399895997641 15449085913462799921998231)
        ·
          refine ⟨23173628870194199882997347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15449085913462799921998231 23173628870194199882997347)
          ·
            refine ⟨34760443305291299824496021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23173628870194199882997347 34760443305291299824496021)
            ·
              refine ⟨1629395779935529679273251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34760443305291299824496021 1629395779935529679273251)
              ·
                refine ⟨2444093669903294518909877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629395779935529679273251 2444093669903294518909877)
                ·
                  refine ⟨229133781553433861147801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2444093669903294518909877 229133781553433861147801)
                  ·
                    rfl

theorem cell20_502016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_502016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502016 prefixEnd_502016 := by exact prefixLift 502016
  have htrace : WordTrace (prefixWord ++ tailWord_502016) baseStart_502016 baseEnd_502016 := by
    simpa [prefixWord, tailWord_502016, baseEnd_502016] using wordTrace_append hprefix tailTrace_502016
  have hstable : (prefixWord ++ tailWord_502016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502016).length < 2 ^ (prefixWord ++ tailWord_502016).sum := by decide
  have hdescent : baseEnd_502016 < baseStart_502016 := by decide
  rcases family_descends (prefixWord ++ tailWord_502016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502033 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_502033 : Nat := 118140960795 + 502033 * 2 ^ 59
def prefixEnd_502033 : Nat := 4983230072969 + 3 ^ 40 * 502033 * 2
def baseEnd_502033 : Nat := 229141540816657357581065

theorem tailTrace_502033 : CollatzResearch.WordTrace tailWord_502033 prefixEnd_502033 229141540816657357581065 := by
  unfold tailWord_502033
  simp only [CollatzResearch.WordTrace]
  refine ⟨18310647790227656255366753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12207098526818437503577835 18310647790227656255366753)
  ·
    refine ⟨13732985842670742191525065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18310647790227656255366753 13732985842670742191525065)
    ·
      refine ⟨10299739382003056643643799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13732985842670742191525065 10299739382003056643643799)
      ·
        refine ⟨15449609073004584965465699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299739382003056643643799 15449609073004584965465699)
        ·
          refine ⟨23174413609506877448198549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15449609073004584965465699 23174413609506877448198549)
          ·
            refine ⟨1086300637945634880384307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23174413609506877448198549 1086300637945634880384307)
            ·
              refine ⟨1629450956918452320576461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086300637945634880384307 1629450956918452320576461)
              ·
                refine ⟨611044108844419620216173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629450956918452320576461 611044108844419620216173)
                ·
                  refine ⟨229141540816657357581065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611044108844419620216173 229141540816657357581065)
                  ·
                    rfl

theorem cell20_502033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_502033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502033 prefixEnd_502033 := by exact prefixLift 502033
  have htrace : WordTrace (prefixWord ++ tailWord_502033) baseStart_502033 baseEnd_502033 := by
    simpa [prefixWord, tailWord_502033, baseEnd_502033] using wordTrace_append hprefix tailTrace_502033
  have hstable : (prefixWord ++ tailWord_502033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502033).length < 2 ^ (prefixWord ++ tailWord_502033).sum := by decide
  have hdescent : baseEnd_502033 < baseStart_502033 := by decide
  rcases family_descends (prefixWord ++ tailWord_502033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502047 : List Nat := [1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_502047 : Nat := 118140960795 + 502047 * 2 ^ 59
def prefixEnd_502047 : Nat := 4983230072969 + 3 ^ 40 * 502047 * 2
def baseEnd_502047 : Nat := 76382643599378510371447

theorem tailTrace_502047 : CollatzResearch.WordTrace tailWord_502047 prefixEnd_502047 76382643599378510371447 := by
  unfold tailWord_502047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18311158412176936646376395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12207438941451291097584263 18311158412176936646376395)
  ·
    refine ⟨27466737618265404969564593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18311158412176936646376395 27466737618265404969564593)
    ·
      refine ⟨20600053213699053727173445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27466737618265404969564593 20600053213699053727173445)
      ·
        refine ⟨3862509977568572573845021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20600053213699053727173445 3862509977568572573845021)
        ·
          refine ⟨1448441241588214715191883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3862509977568572573845021 1448441241588214715191883)
          ·
            refine ⟨2172661862382322072787825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448441241588214715191883 2172661862382322072787825)
            ·
              refine ⟨1629496396786741554590869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172661862382322072787825 1629496396786741554590869)
              ·
                refine ⟨76382643599378510371447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1629496396786741554590869 76382643599378510371447)
                ·
                  rfl

theorem cell20_502047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_502047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502047 prefixEnd_502047 := by exact prefixLift 502047
  have htrace : WordTrace (prefixWord ++ tailWord_502047) baseStart_502047 baseEnd_502047 := by
    simpa [prefixWord, tailWord_502047, baseEnd_502047] using wordTrace_append hprefix tailTrace_502047
  have hstable : (prefixWord ++ tailWord_502047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502047).length < 2 ^ (prefixWord ++ tailWord_502047).sum := by decide
  have hdescent : baseEnd_502047 < baseStart_502047 := by decide
  rcases family_descends (prefixWord ++ tailWord_502047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502074 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_502074 : Nat := 118140960795 + 502074 * 2 ^ 59
def prefixEnd_502074 : Nat := 4983230072969 + 3 ^ 40 * 502074 * 2
def baseEnd_502074 : Nat := 229160254333843437214231

theorem tailTrace_502074 : CollatzResearch.WordTrace tailWord_502074 prefixEnd_502074 229160254333843437214231 := by
  unfold tailWord_502074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578035795769780064402319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12208095455386080171739517 4578035795769780064402319)
  ·
    refine ⟨6867053693654670096603479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4578035795769780064402319 6867053693654670096603479)
    ·
      refine ⟨10300580540482005144905219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867053693654670096603479 10300580540482005144905219)
      ·
        refine ⟨15450870810723007717357829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10300580540482005144905219 15450870810723007717357829)
        ·
          refine ⟨2897038277010563947004593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15450870810723007717357829 2897038277010563947004593)
          ·
            refine ⟨2172778707757922960253445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897038277010563947004593 2172778707757922960253445)
            ·
              refine ⟨407396007704610555047521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2172778707757922960253445 407396007704610555047521)
              ·
                refine ⟨305547005778457916285641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407396007704610555047521 305547005778457916285641)
                ·
                  refine ⟨229160254333843437214231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305547005778457916285641 229160254333843437214231)
                  ·
                    rfl

theorem cell20_502074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_502074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502074 prefixEnd_502074 := by exact prefixLift 502074
  have htrace : WordTrace (prefixWord ++ tailWord_502074) baseStart_502074 baseEnd_502074 := by
    simpa [prefixWord, tailWord_502074, baseEnd_502074] using wordTrace_append hprefix tailTrace_502074
  have hstable : (prefixWord ++ tailWord_502074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502074).length < 2 ^ (prefixWord ++ tailWord_502074).sum := by decide
  have hdescent : baseEnd_502074 < baseStart_502074 := by decide
  rcases family_descends (prefixWord ++ tailWord_502074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502081 : List Nat := [1, 2, 5, 2, 2, 2, 1, 5]
def baseStart_502081 : Nat := 118140960795 + 502081 * 2 ^ 59
def prefixEnd_502081 : Nat := 4983230072969 + 3 ^ 40 * 502081 * 2
def baseEnd_502081 : Nat := 76387816441527507993623

theorem tailTrace_502081 : CollatzResearch.WordTrace tailWord_502081 prefixEnd_502081 76387816441527507993623 := by
  unfold tailWord_502081
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312398494053760453114097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12208265662702506968742731 18312398494053760453114097)
  ·
    refine ⟨13734298870540320339835573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18312398494053760453114097 13734298870540320339835573)
    ·
      refine ⟨1287590519113155031859585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13734298870540320339835573 1287590519113155031859585)
      ·
        refine ⟨965692889334866273894689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1287590519113155031859585 965692889334866273894689)
        ·
          refine ⟨724269667001149705421017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965692889334866273894689 724269667001149705421017)
          ·
            refine ⟨543202250250862279065763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724269667001149705421017 543202250250862279065763)
            ·
              refine ⟨814803375376293418598645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543202250250862279065763 814803375376293418598645)
              ·
                refine ⟨76387816441527507993623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814803375376293418598645 76387816441527507993623)
                ·
                  rfl

theorem cell20_502081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_502081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502081 prefixEnd_502081 := by exact prefixLift 502081
  have htrace : WordTrace (prefixWord ++ tailWord_502081) baseStart_502081 baseEnd_502081 := by
    simpa [prefixWord, tailWord_502081, baseEnd_502081] using wordTrace_append hprefix tailTrace_502081
  have hstable : (prefixWord ++ tailWord_502081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502081).length < 2 ^ (prefixWord ++ tailWord_502081).sum := by decide
  have hdescent : baseEnd_502081 < baseStart_502081 := by decide
  rcases family_descends (prefixWord ++ tailWord_502081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502112 : List Nat := [2, 1, 1, 3, 5, 1, 2, 3, 2]
def baseStart_502112 : Nat := 118140960795 + 502112 * 2 ^ 59
def prefixEnd_502112 : Nat := 4983230072969 + 3 ^ 40 * 502112 * 2
def baseEnd_502112 : Nat := 229177598569284193947409

theorem tailTrace_502112 : CollatzResearch.WordTrace tailWord_502112 prefixEnd_502112 229177598569284193947409 := by
  unfold tailWord_502112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156764578470726373746295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12209019437960968498328393 9156764578470726373746295)
  ·
    refine ⟨13735146867706089560619443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156764578470726373746295 13735146867706089560619443)
    ·
      refine ⟨20602720301559134340929165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13735146867706089560619443 20602720301559134340929165)
      ·
        refine ⟨7726020113084675377848437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20602720301559134340929165 7726020113084675377848437)
        ·
          refine ⟨724314385601688316673291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7726020113084675377848437 724314385601688316673291)
          ·
            refine ⟨1086471578402532475009937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724314385601688316673291 1086471578402532475009937)
            ·
              refine ⟨814853683801899356257453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086471578402532475009937 814853683801899356257453)
              ·
                refine ⟨305570131425712258596545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814853683801899356257453 305570131425712258596545)
                ·
                  refine ⟨229177598569284193947409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305570131425712258596545 229177598569284193947409)
                  ·
                    rfl

theorem cell20_502112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_502112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502112 prefixEnd_502112 := by exact prefixLift 502112
  have htrace : WordTrace (prefixWord ++ tailWord_502112) baseStart_502112 baseEnd_502112 := by
    simpa [prefixWord, tailWord_502112, baseEnd_502112] using wordTrace_append hprefix tailTrace_502112
  have hstable : (prefixWord ++ tailWord_502112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502112).length < 2 ^ (prefixWord ++ tailWord_502112).sum := by decide
  have hdescent : baseEnd_502112 < baseStart_502112 := by decide
  rcases family_descends (prefixWord ++ tailWord_502112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502133 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_502133 : Nat := 118140960795 + 502133 * 2 ^ 59
def prefixEnd_502133 : Nat := 4983230072969 + 3 ^ 40 * 502133 * 2
def baseEnd_502133 : Nat := 229187183541501454247323

theorem tailTrace_502133 : CollatzResearch.WordTrace tailWord_502133 prefixEnd_502133 229187183541501454247323 := by
  unfold tailWord_502133
  simp only [CollatzResearch.WordTrace]
  refine ⟨18314295089865373334007053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12209530059910248889338035 18314295089865373334007053)
  ·
    refine ⟨6867860658699515000252645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18314295089865373334007053 6867860658699515000252645)
    ·
      refine ⟨1287723873506159062547371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6867860658699515000252645 1287723873506159062547371)
      ·
        refine ⟨1931585810259238593821057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287723873506159062547371 1931585810259238593821057)
        ·
          refine ⟨1448689357694428945365793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1931585810259238593821057 1448689357694428945365793)
          ·
            refine ⟨1086517018270821709024345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448689357694428945365793 1086517018270821709024345)
            ·
              refine ⟨814887763703116281768259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086517018270821709024345 814887763703116281768259)
              ·
                refine ⟨1222331645554674422652389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814887763703116281768259 1222331645554674422652389)
                ·
                  refine ⟨229187183541501454247323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222331645554674422652389 229187183541501454247323)
                  ·
                    rfl

theorem cell20_502133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_502133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502133 prefixEnd_502133 := by exact prefixLift 502133
  have htrace : WordTrace (prefixWord ++ tailWord_502133) baseStart_502133 baseEnd_502133 := by
    simpa [prefixWord, tailWord_502133, baseEnd_502133] using wordTrace_append hprefix tailTrace_502133
  have hstable : (prefixWord ++ tailWord_502133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502133).length < 2 ^ (prefixWord ++ tailWord_502133).sum := by decide
  have hdescent : baseEnd_502133 < baseStart_502133 := by decide
  rcases family_descends (prefixWord ++ tailWord_502133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502199 : List Nat := [1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_502199 : Nat := 118140960795 + 502199 * 2 ^ 59
def prefixEnd_502199 : Nat := 4983230072969 + 3 ^ 40 * 502199 * 2
def baseEnd_502199 : Nat := 76405769246632852682351

theorem tailTrace_502199 : CollatzResearch.WordTrace tailWord_502199 prefixEnd_502199 76405769246632852682351 := by
  unfold tailWord_502199
  simp only [CollatzResearch.WordTrace]
  refine ⟨18316702307626266605909651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12211134871750844403939767 18316702307626266605909651)
  ·
    refine ⟨27475053461439399908864477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18316702307626266605909651 27475053461439399908864477)
    ·
      refine ⟨10303145048039774965824179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27475053461439399908864477 10303145048039774965824179)
      ·
        refine ⟨15454717572059662448736269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303145048039774965824179 15454717572059662448736269)
        ·
          refine ⟨5795519089522373418276101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15454717572059662448736269 5795519089522373418276101)
          ·
            refine ⟨1086659829285445015926769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5795519089522373418276101 1086659829285445015926769)
            ·
              refine ⟨814994871964083761945077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086659829285445015926769 814994871964083761945077)
              ·
                refine ⟨76405769246632852682351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814994871964083761945077 76405769246632852682351)
                ·
                  rfl

theorem cell20_502199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_502199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502199 prefixEnd_502199 := by exact prefixLift 502199
  have htrace : WordTrace (prefixWord ++ tailWord_502199) baseStart_502199 baseEnd_502199 := by
    simpa [prefixWord, tailWord_502199, baseEnd_502199] using wordTrace_append hprefix tailTrace_502199
  have hstable : (prefixWord ++ tailWord_502199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502199).length < 2 ^ (prefixWord ++ tailWord_502199).sum := by decide
  have hdescent : baseEnd_502199 < baseStart_502199 := by decide
  rcases family_descends (prefixWord ++ tailWord_502199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502243 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 2]
def baseStart_502243 : Nat := 118140960795 + 502243 * 2 ^ 59
def prefixEnd_502243 : Nat := 4983230072969 + 3 ^ 40 * 502243 * 2
def baseEnd_502243 : Nat := 229237390538829960580207

theorem tailTrace_502243 : CollatzResearch.WordTrace tailWord_502243 prefixEnd_502243 229237390538829960580207 := by
  unfold tailWord_502243
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318307119466862120511383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212204746311241413674255 18318307119466862120511383)
  ·
    refine ⟨27477460679200293180767075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18318307119466862120511383 27477460679200293180767075)
    ·
      refine ⟨41216191018800439771150613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27477460679200293180767075 41216191018800439771150613)
      ·
        refine ⟨1932008954006270614272685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41216191018800439771150613 1932008954006270614272685)
        ·
          refine ⟨724503357752351480352257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1932008954006270614272685 724503357752351480352257)
          ·
            refine ⟨543377518314263610264193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724503357752351480352257 543377518314263610264193)
            ·
              refine ⟨407533138735697707698145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543377518314263610264193 407533138735697707698145)
              ·
                refine ⟨305649854051773280773609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407533138735697707698145 305649854051773280773609)
                ·
                  refine ⟨229237390538829960580207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305649854051773280773609 229237390538829960580207)
                  ·
                    rfl

theorem cell20_502243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 2].length) (baseStart_502243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502243 prefixEnd_502243 := by exact prefixLift 502243
  have htrace : WordTrace (prefixWord ++ tailWord_502243) baseStart_502243 baseEnd_502243 := by
    simpa [prefixWord, tailWord_502243, baseEnd_502243] using wordTrace_append hprefix tailTrace_502243
  have hstable : (prefixWord ++ tailWord_502243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502243).length < 2 ^ (prefixWord ++ tailWord_502243).sum := by decide
  have hdescent : baseEnd_502243 < baseStart_502243 := by decide
  rcases family_descends (prefixWord ++ tailWord_502243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502247 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 2]
def baseStart_502247 : Nat := 118140960795 + 502247 * 2 ^ 59
def prefixEnd_502247 : Nat := 4983230072969 + 3 ^ 40 * 502247 * 2
def baseEnd_502247 : Nat := 229239216247823724446857

theorem tailTrace_502247 : CollatzResearch.WordTrace tailWord_502247 prefixEnd_502247 229239216247823724446857 := by
  unfold tailWord_502247
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318453011452370803656995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212302007634913869104663 18318453011452370803656995)
  ·
    refine ⟨27477679517178556205485493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18318453011452370803656995 27477679517178556205485493)
    ·
      refine ⟨2576032454735489644264265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27477679517178556205485493 2576032454735489644264265)
      ·
        refine ⟨1932024341051617233198199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2576032454735489644264265 1932024341051617233198199)
        ·
          refine ⟨2898036511577425849797299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932024341051617233198199 2898036511577425849797299)
          ·
            refine ⟨4347054767366138774695949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898036511577425849797299 4347054767366138774695949)
            ·
              refine ⟨1630145537762302040510981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4347054767366138774695949 1630145537762302040510981)
              ·
                refine ⟨305652288330431632595809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1630145537762302040510981 305652288330431632595809)
                ·
                  refine ⟨229239216247823724446857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305652288330431632595809 229239216247823724446857)
                  ·
                    rfl

theorem cell20_502247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 2].length) (baseStart_502247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502247 prefixEnd_502247 := by exact prefixLift 502247
  have htrace : WordTrace (prefixWord ++ tailWord_502247) baseStart_502247 baseEnd_502247 := by
    simpa [prefixWord, tailWord_502247, baseEnd_502247] using wordTrace_append hprefix tailTrace_502247
  have hstable : (prefixWord ++ tailWord_502247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502247).length < 2 ^ (prefixWord ++ tailWord_502247).sum := by decide
  have hdescent : baseEnd_502247 < baseStart_502247 := by decide
  rcases family_descends (prefixWord ++ tailWord_502247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502251 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_502251 : Nat := 118140960795 + 502251 * 2 ^ 59
def prefixEnd_502251 : Nat := 4983230072969 + 3 ^ 40 * 502251 * 2
def baseEnd_502251 : Nat := 229241041956817488313507

theorem tailTrace_502251 : CollatzResearch.WordTrace tailWord_502251 prefixEnd_502251 229241041956817488313507 := by
  unfold tailWord_502251
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318598903437879486802607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212399268958586324535071 18318598903437879486802607)
  ·
    refine ⟨27477898355156819230203911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18318598903437879486802607 27477898355156819230203911)
    ·
      refine ⟨41216847532735228845305867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27477898355156819230203911 41216847532735228845305867)
      ·
        refine ⟨61825271299102843267958801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41216847532735228845305867 61825271299102843267958801)
        ·
          refine ⟨46368953474327132450969101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61825271299102843267958801 46368953474327132450969101)
          ·
            refine ⟨17388357552872674669113413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46368953474327132450969101 17388357552872674669113413)
            ·
              refine ⟨3260317041163626500458765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17388357552872674669113413 3260317041163626500458765)
              ·
                refine ⟨1222618890436359937672037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3260317041163626500458765 1222618890436359937672037)
                ·
                  refine ⟨229241041956817488313507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222618890436359937672037 229241041956817488313507)
                  ·
                    rfl

theorem cell20_502251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_502251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502251 prefixEnd_502251 := by exact prefixLift 502251
  have htrace : WordTrace (prefixWord ++ tailWord_502251) baseStart_502251 baseEnd_502251 := by
    simpa [prefixWord, tailWord_502251, baseEnd_502251] using wordTrace_append hprefix tailTrace_502251
  have hstable : (prefixWord ++ tailWord_502251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502251).length < 2 ^ (prefixWord ++ tailWord_502251).sum := by decide
  have hdescent : baseEnd_502251 < baseStart_502251 := by decide
  rcases family_descends (prefixWord ++ tailWord_502251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502254 : List Nat := [4, 1, 2, 1, 2, 4, 1, 5]
def baseStart_502254 : Nat := 118140960795 + 502254 * 2 ^ 59
def prefixEnd_502254 : Nat := 4983230072969 + 3 ^ 40 * 502254 * 2
def baseEnd_502254 : Nat := 76414137079520937071165

theorem tailTrace_502254 : CollatzResearch.WordTrace tailWord_502254 prefixEnd_502254 76414137079520937071165 := by
  unfold tailWord_502254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289838540303376374895227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12212472214951340666107877 2289838540303376374895227)
  ·
    refine ⟨3434757810455064562342841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289838540303376374895227 3434757810455064562342841)
    ·
      refine ⟨2576068357841298421757131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3434757810455064562342841 2576068357841298421757131)
      ·
        refine ⟨3864102536761947632635697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576068357841298421757131 3864102536761947632635697)
        ·
          refine ⟨2898076902571460724476773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864102536761947632635697 2898076902571460724476773)
          ·
            refine ⟨543389419232148885839395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2898076902571460724476773 543389419232148885839395)
            ·
              refine ⟨815084128848223328759093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543389419232148885839395 815084128848223328759093)
              ·
                refine ⟨76414137079520937071165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 815084128848223328759093 76414137079520937071165)
                ·
                  rfl

theorem cell20_502254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_502254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502254 prefixEnd_502254 := by exact prefixLift 502254
  have htrace : WordTrace (prefixWord ++ tailWord_502254) baseStart_502254 baseEnd_502254 := by
    simpa [prefixWord, tailWord_502254, baseEnd_502254] using wordTrace_append hprefix tailTrace_502254
  have hstable : (prefixWord ++ tailWord_502254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502254).length < 2 ^ (prefixWord ++ tailWord_502254).sum := by decide
  have hdescent : baseEnd_502254 < baseStart_502254 := by decide
  rcases family_descends (prefixWord ++ tailWord_502254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502275 : List Nat := [1, 1, 1, 3, 2, 1, 7, 4]
def baseStart_502275 : Nat := 118140960795 + 502275 * 2 ^ 59
def prefixEnd_502275 : Nat := 4983230072969 + 3 ^ 40 * 502275 * 2
def baseEnd_502275 : Nat := 76417332070260023837803

theorem tailTrace_502275 : CollatzResearch.WordTrace tailWord_502275 prefixEnd_502275 76417332070260023837803 := by
  unfold tailWord_502275
  simp only [CollatzResearch.WordTrace]
  refine ⟨18319474255350931585676279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212982836900621057117519 18319474255350931585676279)
  ·
    refine ⟨27479211383026397378514419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18319474255350931585676279 27479211383026397378514419)
    ·
      refine ⟨41218817074539596067771629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27479211383026397378514419 41218817074539596067771629)
      ·
        refine ⟨15457056402952348525414361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41218817074539596067771629 15457056402952348525414361)
        ·
          refine ⟨11592792302214261394060771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15457056402952348525414361 11592792302214261394060771)
          ·
            refine ⟨17389188453321392091091157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11592792302214261394060771 17389188453321392091091157)
            ·
              refine ⟨407559104374720127134949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17389188453321392091091157 407559104374720127134949)
              ·
                refine ⟨76417332070260023837803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407559104374720127134949 76417332070260023837803)
                ·
                  rfl

theorem cell20_502275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_502275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502275 prefixEnd_502275 := by exact prefixLift 502275
  have htrace : WordTrace (prefixWord ++ tailWord_502275) baseStart_502275 baseEnd_502275 := by
    simpa [prefixWord, tailWord_502275, baseEnd_502275] using wordTrace_append hprefix tailTrace_502275
  have hstable : (prefixWord ++ tailWord_502275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502275).length < 2 ^ (prefixWord ++ tailWord_502275).sum := by decide
  have hdescent : baseEnd_502275 < baseStart_502275 := by decide
  rcases family_descends (prefixWord ++ tailWord_502275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502282 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_502282 : Nat := 118140960795 + 502282 * 2 ^ 59
def prefixEnd_502282 : Nat := 4983230072969 + 3 ^ 40 * 502282 * 2
def baseEnd_502282 : Nat := 229255191201519158280047

theorem tailTrace_502282 : CollatzResearch.WordTrace tailWord_502282 prefixEnd_502282 229255191201519158280047 := by
  unfold tailWord_502282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579932391581392945295275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12213153044217047854120733 4579932391581392945295275)
  ·
    refine ⟨6869898587372089417942913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4579932391581392945295275 6869898587372089417942913)
    ·
      refine ⟨5152423940529067063457185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6869898587372089417942913 5152423940529067063457185)
      ·
        refine ⟨3864317955396800297592889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5152423940529067063457185 3864317955396800297592889)
        ·
          refine ⟨2898238466547600223194667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864317955396800297592889 2898238466547600223194667)
          ·
            refine ⟨4347357699821400334792001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898238466547600223194667 4347357699821400334792001)
            ·
              refine ⟨3260518274866050251094001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4347357699821400334792001 3260518274866050251094001)
              ·
                refine ⟨2445388706149537688320501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260518274866050251094001 2445388706149537688320501)
                ·
                  refine ⟨229255191201519158280047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2445388706149537688320501 229255191201519158280047)
                  ·
                    rfl

theorem cell20_502282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_502282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502282 prefixEnd_502282 := by exact prefixLift 502282
  have htrace : WordTrace (prefixWord ++ tailWord_502282) baseStart_502282 baseEnd_502282 := by
    simpa [prefixWord, tailWord_502282, baseEnd_502282] using wordTrace_append hprefix tailTrace_502282
  have hstable : (prefixWord ++ tailWord_502282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502282).length < 2 ^ (prefixWord ++ tailWord_502282).sum := by decide
  have hdescent : baseEnd_502282 < baseStart_502282 := by decide
  rcases family_descends (prefixWord ++ tailWord_502282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502292 : List Nat := [2, 4, 3, 1, 1, 2, 7]
def baseStart_502292 : Nat := 118140960795 + 502292 * 2 ^ 59
def prefixEnd_502292 : Nat := 4983230072969 + 3 ^ 40 * 502292 * 2
def baseEnd_502292 : Nat := 25473306163778174216297

theorem tailTrace_502292 : CollatzResearch.WordTrace tailWord_502292 prefixEnd_502292 25473306163778174216297 := by
  unfold tailWord_502292
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160047148144671744522565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12213396197526228992696753 9160047148144671744522565)
  ·
    refine ⟨1717508840277125952097981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9160047148144671744522565 1717508840277125952097981)
    ·
      refine ⟨644065815103922232036743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1717508840277125952097981 644065815103922232036743)
      ·
        refine ⟨966098722655883348055115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644065815103922232036743 966098722655883348055115)
        ·
          refine ⟨1449148083983825022082673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966098722655883348055115 1449148083983825022082673)
          ·
            refine ⟨1086861062987868766562005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449148083983825022082673 1086861062987868766562005)
            ·
              refine ⟨25473306163778174216297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1086861062987868766562005 25473306163778174216297)
              ·
                rfl

theorem cell20_502292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 7].length) (baseStart_502292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502292 prefixEnd_502292 := by exact prefixLift 502292
  have htrace : WordTrace (prefixWord ++ tailWord_502292) baseStart_502292 baseEnd_502292 := by
    simpa [prefixWord, tailWord_502292, baseEnd_502292] using wordTrace_append hprefix tailTrace_502292
  have hstable : (prefixWord ++ tailWord_502292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502292).length < 2 ^ (prefixWord ++ tailWord_502292).sum := by decide
  have hdescent : baseEnd_502292 < baseStart_502292 := by decide
  rcases family_descends (prefixWord ++ tailWord_502292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502295 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 3]
def baseStart_502295 : Nat := 118140960795 + 502295 * 2 ^ 59
def prefixEnd_502295 : Nat := 4983230072969 + 3 ^ 40 * 502295 * 2
def baseEnd_502295 : Nat := 229261124755748890846661

theorem tailTrace_502295 : CollatzResearch.WordTrace tailWord_502295 prefixEnd_502295 229261124755748890846661 := by
  unfold tailWord_502295
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320203715278475001404339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12213469143518983334269559 18320203715278475001404339)
  ·
    refine ⟨27480305572917712502106509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18320203715278475001404339 27480305572917712502106509)
    ·
      refine ⟨10305114589844142188289941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27480305572917712502106509 10305114589844142188289941)
      ·
        refine ⟨483052246398944165076091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10305114589844142188289941 483052246398944165076091)
        ·
          refine ⟨724578369598416247614137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483052246398944165076091 724578369598416247614137)
          ·
            refine ⟨543433777198812185710603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724578369598416247614137 543433777198812185710603)
            ·
              refine ⟨815150665798218278565905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543433777198812185710603 815150665798218278565905)
              ·
                refine ⟨611362999348663708924429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815150665798218278565905 611362999348663708924429)
                ·
                  refine ⟨229261124755748890846661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611362999348663708924429 229261124755748890846661)
                  ·
                    rfl

theorem cell20_502295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_502295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502295 prefixEnd_502295 := by exact prefixLift 502295
  have htrace : WordTrace (prefixWord ++ tailWord_502295) baseStart_502295 baseEnd_502295 := by
    simpa [prefixWord, tailWord_502295, baseEnd_502295] using wordTrace_append hprefix tailTrace_502295
  have hstable : (prefixWord ++ tailWord_502295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502295).length < 2 ^ (prefixWord ++ tailWord_502295).sum := by decide
  have hdescent : baseEnd_502295 < baseStart_502295 := by decide
  rcases family_descends (prefixWord ++ tailWord_502295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502320 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_502320 : Nat := 118140960795 + 502320 * 2 ^ 59
def prefixEnd_502320 : Nat := 4983230072969 + 3 ^ 40 * 502320 * 2
def baseEnd_502320 : Nat := 229272535436959915013225

theorem tailTrace_502320 : CollatzResearch.WordTrace tailWord_502320 prefixEnd_502320 229272535436959915013225 := by
  unfold tailWord_502320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160557770093952135532207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12214077026791936180709609 9160557770093952135532207)
  ·
    refine ⟨13740836655140928203298311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9160557770093952135532207 13740836655140928203298311)
    ·
      refine ⟨20611254982711392304947467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13740836655140928203298311 20611254982711392304947467)
      ·
        refine ⟨30916882474067088457421201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20611254982711392304947467 30916882474067088457421201)
        ·
          refine ⟨23187661855550316343065901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30916882474067088457421201 23187661855550316343065901)
          ·
            refine ⟨8695373195831368628649713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23187661855550316343065901 8695373195831368628649713)
            ·
              refine ⟨6521529896873526471487285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8695373195831368628649713 6521529896873526471487285)
              ·
                refine ⟨611393427831893106701933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6521529896873526471487285 611393427831893106701933)
                ·
                  refine ⟨229272535436959915013225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611393427831893106701933 229272535436959915013225)
                  ·
                    rfl

theorem cell20_502320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_502320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502320 prefixEnd_502320 := by exact prefixLift 502320
  have htrace : WordTrace (prefixWord ++ tailWord_502320) baseStart_502320 baseEnd_502320 := by
    simpa [prefixWord, tailWord_502320, baseEnd_502320] using wordTrace_append hprefix tailTrace_502320
  have hstable : (prefixWord ++ tailWord_502320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502320).length < 2 ^ (prefixWord ++ tailWord_502320).sum := by decide
  have hdescent : baseEnd_502320 < baseStart_502320 := by decide
  rcases family_descends (prefixWord ++ tailWord_502320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502327 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_502327 : Nat := 118140960795 + 502327 * 2 ^ 59
def prefixEnd_502327 : Nat := 4983230072969 + 3 ^ 40 * 502327 * 2
def baseEnd_502327 : Nat := 229275730427699001779863

theorem tailTrace_502327 : CollatzResearch.WordTrace tailWord_502327 prefixEnd_502327 229275730427699001779863 := by
  unfold tailWord_502327
  simp only [CollatzResearch.WordTrace]
  refine ⟨18321370851162544466569235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12214247234108362977712823 18321370851162544466569235)
  ·
    refine ⟨27482056276743816699853853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18321370851162544466569235 27482056276743816699853853)
    ·
      refine ⟨10305771103778931262445195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27482056276743816699853853 10305771103778931262445195)
      ·
        refine ⟨15458656655668396893667793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305771103778931262445195 15458656655668396893667793)
        ·
          refine ⟨11593992491751297670250845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15458656655668396893667793 11593992491751297670250845)
          ·
            refine ⟨4347747184406736626344067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11593992491751297670250845 4347747184406736626344067)
            ·
              refine ⟨6521620776610104939516101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347747184406736626344067 6521620776610104939516101)
              ·
                refine ⟨1222803895614394676159269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6521620776610104939516101 1222803895614394676159269)
                ·
                  refine ⟨229275730427699001779863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222803895614394676159269 229275730427699001779863)
                  ·
                    rfl

theorem cell20_502327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_502327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502327 prefixEnd_502327 := by exact prefixLift 502327
  have htrace : WordTrace (prefixWord ++ tailWord_502327) baseStart_502327 baseEnd_502327 := by
    simpa [prefixWord, tailWord_502327, baseEnd_502327] using wordTrace_append hprefix tailTrace_502327
  have hstable : (prefixWord ++ tailWord_502327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502327).length < 2 ^ (prefixWord ++ tailWord_502327).sum := by decide
  have hdescent : baseEnd_502327 < baseStart_502327 := by decide
  rcases family_descends (prefixWord ++ tailWord_502327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502330 : List Nat := [3, 1, 1, 1, 3, 5, 2, 4]
def baseStart_502330 : Nat := 118140960795 + 502330 * 2 ^ 59
def prefixEnd_502330 : Nat := 4983230072969 + 3 ^ 40 * 502330 * 2
def baseEnd_502330 : Nat := 76425699903148108226617

theorem tailTrace_502330 : CollatzResearch.WordTrace tailWord_502330 prefixEnd_502330 76425699903148108226617 := by
  unfold tailWord_502330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580370067537918994732111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12214320180101117319285629 4580370067537918994732111)
  ·
    refine ⟨6870555101306878492098167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580370067537918994732111 6870555101306878492098167)
    ·
      refine ⟨10305832651960317738147251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870555101306878492098167 10305832651960317738147251)
      ·
        refine ⟨15458748977940476607220877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305832651960317738147251 15458748977940476607220877)
        ·
          refine ⟨5797030866727678727707829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15458748977940476607220877 5797030866727678727707829)
          ·
            refine ⟨543471643755719880722609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5797030866727678727707829 543471643755719880722609)
            ·
              refine ⟨407603732816789910541957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543471643755719880722609 407603732816789910541957)
              ·
                refine ⟨76425699903148108226617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407603732816789910541957 76425699903148108226617)
                ·
                  rfl

theorem cell20_502330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_502330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502330 prefixEnd_502330 := by exact prefixLift 502330
  have htrace : WordTrace (prefixWord ++ tailWord_502330) baseStart_502330 baseEnd_502330 := by
    simpa [prefixWord, tailWord_502330, baseEnd_502330] using wordTrace_append hprefix tailTrace_502330
  have hstable : (prefixWord ++ tailWord_502330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502330).length < 2 ^ (prefixWord ++ tailWord_502330).sum := by decide
  have hdescent : baseEnd_502330 < baseStart_502330 := by decide
  rcases family_descends (prefixWord ++ tailWord_502330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502379 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_502379 : Nat := 118140960795 + 502379 * 2 ^ 59
def prefixEnd_502379 : Nat := 4983230072969 + 3 ^ 40 * 502379 * 2
def baseEnd_502379 : Nat := 229299464644617932046317

theorem tailTrace_502379 : CollatzResearch.WordTrace tailWord_502379 prefixEnd_502379 229299464644617932046317 := by
  unfold tailWord_502379
  simp only [CollatzResearch.WordTrace]
  refine ⟨18323267446974157347462191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12215511631316104898308127 18323267446974157347462191)
  ·
    refine ⟨27484901170461236021193287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18323267446974157347462191 27484901170461236021193287)
    ·
      refine ⟨41227351755691854031789931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27484901170461236021193287 41227351755691854031789931)
      ·
        refine ⟨61841027633537781047684897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41227351755691854031789931 61841027633537781047684897)
        ·
          refine ⟨46380770725153335785763673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61841027633537781047684897 46380770725153335785763673)
          ·
            refine ⟨34785578043865001839322755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46380770725153335785763673 34785578043865001839322755)
            ·
              refine ⟨52178367065797502758984133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34785578043865001839322755 52178367065797502758984133)
              ·
                refine ⟨9783443824837031767309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52178367065797502758984133 9783443824837031767309525)
                ·
                  refine ⟨229299464644617932046317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9783443824837031767309525 229299464644617932046317)
                  ·
                    rfl

theorem cell20_502379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_502379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502379 prefixEnd_502379 := by exact prefixLift 502379
  have htrace : WordTrace (prefixWord ++ tailWord_502379) baseStart_502379 baseEnd_502379 := by
    simpa [prefixWord, tailWord_502379, baseEnd_502379] using wordTrace_append hprefix tailTrace_502379
  have hstable : (prefixWord ++ tailWord_502379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502379).length < 2 ^ (prefixWord ++ tailWord_502379).sum := by decide
  have hdescent : baseEnd_502379 < baseStart_502379 := by decide
  rcases family_descends (prefixWord ++ tailWord_502379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502402 : List Nat := [3, 4, 3, 1, 2, 7]
def baseStart_502402 : Nat := 118140960795 + 502402 * 2 ^ 59
def prefixEnd_502402 : Nat := 4983230072969 + 3 ^ 40 * 502402 * 2
def baseEnd_502402 : Nat := 8492961573012299047391

theorem tailTrace_502402 : CollatzResearch.WordTrace tailWord_502402 prefixEnd_502402 8492961573012299047391 := by
  unfold tailWord_502402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581026581472708068887365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12216070883927221517032973 4581026581472708068887365)
  ·
    refine ⟨858942484026132762916381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4581026581472708068887365 858942484026132762916381)
    ·
      refine ⟨322103431509799786093643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 858942484026132762916381 322103431509799786093643)
      ·
        refine ⟨483155147264699679140465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322103431509799786093643 483155147264699679140465)
        ·
          refine ⟨362366360448524759355349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483155147264699679140465 362366360448524759355349)
          ·
            refine ⟨8492961573012299047391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 362366360448524759355349 8492961573012299047391)
            ·
              rfl

theorem cell20_502402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 7].length) (baseStart_502402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502402 prefixEnd_502402 := by exact prefixLift 502402
  have htrace : WordTrace (prefixWord ++ tailWord_502402) baseStart_502402 baseEnd_502402 := by
    simpa [prefixWord, tailWord_502402, baseEnd_502402] using wordTrace_append hprefix tailTrace_502402
  have hstable : (prefixWord ++ tailWord_502402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502402).length < 2 ^ (prefixWord ++ tailWord_502402).sum := by decide
  have hdescent : baseEnd_502402 < baseStart_502402 := by decide
  rcases family_descends (prefixWord ++ tailWord_502402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502410 : List Nat := [3, 1, 2, 3, 11]
def baseStart_502410 : Nat := 118140960795 + 502410 * 2 ^ 59
def prefixEnd_502410 : Nat := 4983230072969 + 3 ^ 40 * 502410 * 2
def baseEnd_502410 : Nat := 2831032270238513605097

theorem tailTrace_502410 : CollatzResearch.WordTrace tailWord_502410 prefixEnd_502410 2831032270238513605097 := by
  unfold tailWord_502410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581099527465462410460171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12216265406574566427893789 4581099527465462410460171)
  ·
    refine ⟨6871649291198193615690257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581099527465462410460171 6871649291198193615690257)
    ·
      refine ⟨5153736968398645211767693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6871649291198193615690257 5153736968398645211767693)
      ·
        refine ⟨1932651363149491954412885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5153736968398645211767693 1932651363149491954412885)
        ·
          refine ⟨2831032270238513605097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1932651363149491954412885 2831032270238513605097)
          ·
            rfl

theorem cell20_502410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 11].length) (baseStart_502410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502410 prefixEnd_502410 := by exact prefixLift 502410
  have htrace : WordTrace (prefixWord ++ tailWord_502410) baseStart_502410 baseEnd_502410 := by
    simpa [prefixWord, tailWord_502410, baseEnd_502410] using wordTrace_append hprefix tailTrace_502410
  have hstable : (prefixWord ++ tailWord_502410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502410).length < 2 ^ (prefixWord ++ tailWord_502410).sum := by decide
  have hdescent : baseEnd_502410 < baseStart_502410 := by decide
  rcases family_descends (prefixWord ++ tailWord_502410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502417 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_502417 : Nat := 118140960795 + 502417 * 2 ^ 59
def prefixEnd_502417 : Nat := 4983230072969 + 3 ^ 40 * 502417 * 2
def baseEnd_502417 : Nat := 229316808880058688779495

theorem tailTrace_502417 : CollatzResearch.WordTrace tailWord_502417 prefixEnd_502417 229316808880058688779495 := by
  unfold tailWord_502417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18324653420836489837345505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12216435613890993224897003 18324653420836489837345505)
  ·
    refine ⟨13743490065627367378009129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18324653420836489837345505 13743490065627367378009129)
    ·
      refine ⟨10307617549220525533506847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13743490065627367378009129 10307617549220525533506847)
      ·
        refine ⟨15461426323830788300260271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10307617549220525533506847 15461426323830788300260271)
        ·
          refine ⟨23192139485746182450390407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15461426323830788300260271 23192139485746182450390407)
          ·
            refine ⟨34788209228619273675585611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23192139485746182450390407 34788209228619273675585611)
            ·
              refine ⟨52182313842928910513378417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34788209228619273675585611 52182313842928910513378417)
              ·
                refine ⟨39136735382196682885033813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52182313842928910513378417 39136735382196682885033813)
                ·
                  refine ⟨229316808880058688779495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39136735382196682885033813 229316808880058688779495)
                  ·
                    rfl

theorem cell20_502417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_502417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502417 prefixEnd_502417 := by exact prefixLift 502417
  have htrace : WordTrace (prefixWord ++ tailWord_502417) baseStart_502417 baseEnd_502417 := by
    simpa [prefixWord, tailWord_502417, baseEnd_502417] using wordTrace_append hprefix tailTrace_502417
  have hstable : (prefixWord ++ tailWord_502417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502417).length < 2 ^ (prefixWord ++ tailWord_502417).sum := by decide
  have hdescent : baseEnd_502417 < baseStart_502417 := by decide
  rcases family_descends (prefixWord ++ tailWord_502417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502468 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_502468 : Nat := 118140960795 + 502468 * 2 ^ 59
def prefixEnd_502468 : Nat := 4983230072969 + 3 ^ 40 * 502468 * 2
def baseEnd_502468 : Nat := 229340086669729178079287

theorem tailTrace_502468 : CollatzResearch.WordTrace tailWord_502468 prefixEnd_502468 229340086669729178079287 := by
  unfold tailWord_502468
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163256771825862773726029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12217675695767817031634705 9163256771825862773726029)
  ·
    refine ⟨3436221289434698540147261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9163256771825862773726029 3436221289434698540147261)
    ·
      refine ⟨1288582983538011952555223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3436221289434698540147261 1288582983538011952555223)
      ·
        refine ⟨1932874475307017928832835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288582983538011952555223 1932874475307017928832835)
        ·
          refine ⟨2899311712960526893249253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932874475307017928832835 2899311712960526893249253)
          ·
            refine ⟨543620946180098792484235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2899311712960526893249253 543620946180098792484235)
            ·
              refine ⟨815431419270148188726353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543620946180098792484235 815431419270148188726353)
              ·
                refine ⟨611573564452611141544765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815431419270148188726353 611573564452611141544765)
                ·
                  refine ⟨229340086669729178079287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611573564452611141544765 229340086669729178079287)
                  ·
                    rfl

theorem cell20_502468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_502468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502468 prefixEnd_502468 := by exact prefixLift 502468
  have htrace : WordTrace (prefixWord ++ tailWord_502468) baseStart_502468 baseEnd_502468 := by
    simpa [prefixWord, tailWord_502468, baseEnd_502468] using wordTrace_append hprefix tailTrace_502468
  have hstable : (prefixWord ++ tailWord_502468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502468).length < 2 ^ (prefixWord ++ tailWord_502468).sum := by decide
  have hdescent : baseEnd_502468 < baseStart_502468 := by decide
  rcases family_descends (prefixWord ++ tailWord_502468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502472 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_502472 : Nat := 118140960795 + 502472 * 2 ^ 59
def prefixEnd_502472 : Nat := 4983230072969 + 3 ^ 40 * 502472 * 2
def baseEnd_502472 : Nat := 229341912378722941945937

theorem tailTrace_502472 : CollatzResearch.WordTrace tailWord_502472 prefixEnd_502472 229341912378722941945937 := by
  unfold tailWord_502472
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163329717818617115298835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12217772957091489487065113 9163329717818617115298835)
  ·
    refine ⟨13744994576727925672948253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9163329717818617115298835 13744994576727925672948253)
    ·
      refine ⟨5154372966272972127355595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13744994576727925672948253 5154372966272972127355595)
      ·
        refine ⟨7731559449409458191033393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154372966272972127355595 7731559449409458191033393)
        ·
          refine ⟨5798669587057093643275045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7731559449409458191033393 5798669587057093643275045)
          ·
            refine ⟨1087250547573205058114071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5798669587057093643275045 1087250547573205058114071)
            ·
              refine ⟨1630875821359807587171107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087250547573205058114071 1630875821359807587171107)
              ·
                refine ⟨2446313732039711380756661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630875821359807587171107 2446313732039711380756661)
                ·
                  refine ⟨229341912378722941945937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446313732039711380756661 229341912378722941945937)
                  ·
                    rfl

theorem cell20_502472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_502472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502472 prefixEnd_502472 := by exact prefixLift 502472
  have htrace : WordTrace (prefixWord ++ tailWord_502472) baseStart_502472 baseEnd_502472 := by
    simpa [prefixWord, tailWord_502472, baseEnd_502472] using wordTrace_append hprefix tailTrace_502472
  have hstable : (prefixWord ++ tailWord_502472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502472).length < 2 ^ (prefixWord ++ tailWord_502472).sum := by decide
  have hdescent : baseEnd_502472 < baseStart_502472 := by decide
  rcases family_descends (prefixWord ++ tailWord_502472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502485 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 3]
def baseStart_502485 : Nat := 118140960795 + 502485 * 2 ^ 59
def prefixEnd_502485 : Nat := 4983230072969 + 3 ^ 40 * 502485 * 2
def baseEnd_502485 : Nat := 229347845932952674512551

theorem tailTrace_502485 : CollatzResearch.WordTrace tailWord_502485 prefixEnd_502485 229347845932952674512551 := by
  unfold tailWord_502485
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327133584590137450820909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12218089056393424967213939 18327133584590137450820909)
  ·
    refine ⟨6872675094221301544057841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18327133584590137450820909 6872675094221301544057841)
    ·
      refine ⟨5154506320665976158043381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6872675094221301544057841 5154506320665976158043381)
      ·
        refine ⟨483234967562435264816567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5154506320665976158043381 483234967562435264816567)
        ·
          refine ⟨724852451343652897224851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483234967562435264816567 724852451343652897224851)
          ·
            refine ⟨1087278677015479345837277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724852451343652897224851 1087278677015479345837277)
            ·
              refine ⟨407729503880804754688979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1087278677015479345837277 407729503880804754688979)
              ·
                refine ⟨611594255821207132033469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407729503880804754688979 611594255821207132033469)
                ·
                  refine ⟨229347845932952674512551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611594255821207132033469 229347845932952674512551)
                  ·
                    rfl

theorem cell20_502485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_502485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502485 prefixEnd_502485 := by exact prefixLift 502485
  have htrace : WordTrace (prefixWord ++ tailWord_502485) baseStart_502485 baseEnd_502485 := by
    simpa [prefixWord, tailWord_502485, baseEnd_502485] using wordTrace_append hprefix tailTrace_502485
  have hstable : (prefixWord ++ tailWord_502485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502485).length < 2 ^ (prefixWord ++ tailWord_502485).sum := by decide
  have hdescent : baseEnd_502485 < baseStart_502485 := by decide
  rcases family_descends (prefixWord ++ tailWord_502485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502489 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 3]
def baseStart_502489 : Nat := 118140960795 + 502489 * 2 ^ 59
def prefixEnd_502489 : Nat := 4983230072969 + 3 ^ 40 * 502489 * 2
def baseEnd_502489 : Nat := 229349671641946438379201

theorem tailTrace_502489 : CollatzResearch.WordTrace tailWord_502489 prefixEnd_502489 229349671641946438379201 := by
  unfold tailWord_502489
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327279476575646133966521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12218186317717097422644347 18327279476575646133966521)
  ·
    refine ⟨13745459607431734600474891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18327279476575646133966521 13745459607431734600474891)
    ·
      refine ⟨20618189411147601900712337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13745459607431734600474891 20618189411147601900712337)
      ·
        refine ⟨15463642058360701425534253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20618189411147601900712337 15463642058360701425534253)
        ·
          refine ⟨5798865771885263034575345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15463642058360701425534253 5798865771885263034575345)
          ·
            refine ⟨4349149328913947275931509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5798865771885263034575345 4349149328913947275931509)
            ·
              refine ⟨407732749585682557118579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4349149328913947275931509 407732749585682557118579)
              ·
                refine ⟨611599124378523835677869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407732749585682557118579 611599124378523835677869)
                ·
                  refine ⟨229349671641946438379201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611599124378523835677869 229349671641946438379201)
                  ·
                    rfl

theorem cell20_502489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_502489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502489 prefixEnd_502489 := by exact prefixLift 502489
  have htrace : WordTrace (prefixWord ++ tailWord_502489) baseStart_502489 baseEnd_502489 := by
    simpa [prefixWord, tailWord_502489, baseEnd_502489] using wordTrace_append hprefix tailTrace_502489
  have hstable : (prefixWord ++ tailWord_502489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502489).length < 2 ^ (prefixWord ++ tailWord_502489).sum := by decide
  have hdescent : baseEnd_502489 < baseStart_502489 := by decide
  rcases family_descends (prefixWord ++ tailWord_502489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502510 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_502510 : Nat := 118140960795 + 502510 * 2 ^ 59
def prefixEnd_502510 : Nat := 4983230072969 + 3 ^ 40 * 502510 * 2
def baseEnd_502510 : Nat := 229359256614163698679115

theorem tailTrace_502510 : CollatzResearch.WordTrace tailWord_502510 prefixEnd_502510 229359256614163698679115 := by
  unfold tailWord_502510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2291005676187445840060123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12218696939666377813653989 2291005676187445840060123)
  ·
    refine ⟨3436508514281168760090185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2291005676187445840060123 3436508514281168760090185)
    ·
      refine ⟨2577381385710876570067639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3436508514281168760090185 2577381385710876570067639)
      ·
        refine ⟨3866072078566314855101459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577381385710876570067639 3866072078566314855101459)
        ·
          refine ⟨5799108117849472282652189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866072078566314855101459 5799108117849472282652189)
          ·
            refine ⟨2174665544193552105994571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5799108117849472282652189 2174665544193552105994571)
            ·
              refine ⟨3261998316290328158991857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174665544193552105994571 3261998316290328158991857)
              ·
                refine ⟨2446498737217746119243893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261998316290328158991857 2446498737217746119243893)
                ·
                  refine ⟨229359256614163698679115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2446498737217746119243893 229359256614163698679115)
                  ·
                    rfl

theorem cell20_502510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_502510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502510 prefixEnd_502510 := by exact prefixLift 502510
  have htrace : WordTrace (prefixWord ++ tailWord_502510) baseStart_502510 baseEnd_502510 := by
    simpa [prefixWord, tailWord_502510, baseEnd_502510] using wordTrace_append hprefix tailTrace_502510
  have hstable : (prefixWord ++ tailWord_502510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502510).length < 2 ^ (prefixWord ++ tailWord_502510).sum := by decide
  have hdescent : baseEnd_502510 < baseStart_502510 := by decide
  rcases family_descends (prefixWord ++ tailWord_502510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502516 : List Nat := [2, 6, 1, 1, 3, 1, 6]
def baseStart_502516 : Nat := 118140960795 + 502516 * 2 ^ 59
def prefixEnd_502516 : Nat := 4983230072969 + 3 ^ 40 * 502516 * 2
def baseEnd_502516 : Nat := 25484666130850482719899

theorem tailTrace_502516 : CollatzResearch.WordTrace tailWord_502516 prefixEnd_502516 25484666130850482719899 := by
  unfold tailWord_502516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164132123738914872599701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12218842831651886496799601 9164132123738914872599701)
  ·
    refine ⟨429568693300261634653111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9164132123738914872599701 429568693300261634653111)
    ·
      refine ⟨644353039950392451979667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429568693300261634653111 644353039950392451979667)
      ·
        refine ⟨966529559925588677969501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644353039950392451979667 966529559925588677969501)
        ·
          refine ⟨362448584972095754238563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966529559925588677969501 362448584972095754238563)
          ·
            refine ⟨543672877458143631357845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362448584972095754238563 543672877458143631357845)
            ·
              refine ⟨25484666130850482719899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 543672877458143631357845 25484666130850482719899)
              ·
                rfl

theorem cell20_502516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 6].length) (baseStart_502516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502516 prefixEnd_502516 := by exact prefixLift 502516
  have htrace : WordTrace (prefixWord ++ tailWord_502516) baseStart_502516 baseEnd_502516 := by
    simpa [prefixWord, tailWord_502516, baseEnd_502516] using wordTrace_append hprefix tailTrace_502516
  have hstable : (prefixWord ++ tailWord_502516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502516).length < 2 ^ (prefixWord ++ tailWord_502516).sum := by decide
  have hdescent : baseEnd_502516 < baseStart_502516 := by decide
  rcases family_descends (prefixWord ++ tailWord_502516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502524 : List Nat := [2, 2, 2, 1, 3, 2, 8]
def baseStart_502524 : Nat := 118140960795 + 502524 * 2 ^ 59
def prefixEnd_502524 : Nat := 4983230072969 + 3 ^ 40 * 502524 * 2
def baseEnd_502524 : Nat := 25485071843960208023599

theorem tailTrace_502524 : CollatzResearch.WordTrace tailWord_502524 prefixEnd_502524 25485071843960208023599 := by
  unfold tailWord_502524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164278015724423555745313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12219037354299231407660417 9164278015724423555745313)
  ·
    refine ⟨6873208511793317666808985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9164278015724423555745313 6873208511793317666808985)
    ·
      refine ⟨5154906383844988250106739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6873208511793317666808985 5154906383844988250106739)
      ·
        refine ⟨7732359575767482375160109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154906383844988250106739 7732359575767482375160109)
        ·
          refine ⟨2899634840912805890685041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7732359575767482375160109 2899634840912805890685041)
          ·
            refine ⟨2174726130684604418013781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899634840912805890685041 2174726130684604418013781)
            ·
              refine ⟨25485071843960208023599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2174726130684604418013781 25485071843960208023599)
              ·
                rfl

theorem cell20_502524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_502524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502524 prefixEnd_502524 := by exact prefixLift 502524
  have htrace : WordTrace (prefixWord ++ tailWord_502524) baseStart_502524 baseEnd_502524 := by
    simpa [prefixWord, tailWord_502524, baseEnd_502524] using wordTrace_append hprefix tailTrace_502524
  have hstable : (prefixWord ++ tailWord_502524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502524).length < 2 ^ (prefixWord ++ tailWord_502524).sum := by decide
  have hdescent : baseEnd_502524 < baseStart_502524 := by decide
  rcases family_descends (prefixWord ++ tailWord_502524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502572 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 2]
def baseStart_502572 : Nat := 118140960795 + 502572 * 2 ^ 59
def prefixEnd_502572 : Nat := 4983230072969 + 3 ^ 40 * 502572 * 2
def baseEnd_502572 : Nat := 229387555103567038612195

theorem tailTrace_502572 : CollatzResearch.WordTrace tailWord_502572 prefixEnd_502572 229387555103567038612195 := by
  unfold tailWord_502572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165153367637475654618985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12220204490183300872825313 9165153367637475654618985)
  ·
    refine ⟨6873865025728106740964239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9165153367637475654618985 6873865025728106740964239)
    ·
      refine ⟨10310797538592160111446359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873865025728106740964239 10310797538592160111446359)
      ·
        refine ⟨15466196307888240167169539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310797538592160111446359 15466196307888240167169539)
        ·
          refine ⟨23199294461832360250754309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15466196307888240167169539 23199294461832360250754309)
          ·
            refine ⟨4349867711593567547016433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23199294461832360250754309 4349867711593567547016433)
            ·
              refine ⟨3262400783695175660262325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349867711593567547016433 3262400783695175660262325)
              ·
                refine ⟨305850073471422718149593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3262400783695175660262325 305850073471422718149593)
                ·
                  refine ⟨229387555103567038612195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305850073471422718149593 229387555103567038612195)
                  ·
                    rfl

theorem cell20_502572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_502572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502572 prefixEnd_502572 := by exact prefixLift 502572
  have htrace : WordTrace (prefixWord ++ tailWord_502572) baseStart_502572 baseEnd_502572 := by
    simpa [prefixWord, tailWord_502572, baseEnd_502572] using wordTrace_append hprefix tailTrace_502572
  have hstable : (prefixWord ++ tailWord_502572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502572).length < 2 ^ (prefixWord ++ tailWord_502572).sum := by decide
  have hdescent : baseEnd_502572 < baseStart_502572 := by decide
  rcases family_descends (prefixWord ++ tailWord_502572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502617 : List Nat := [1, 2, 1, 2, 2, 5, 3, 4]
def baseStart_502617 : Nat := 118140960795 + 502617 * 2 ^ 59
def prefixEnd_502617 : Nat := 4983230072969 + 3 ^ 40 * 502617 * 2
def baseEnd_502617 : Nat := 76469364776582294037337

theorem tailTrace_502617 : CollatzResearch.WordTrace tailWord_502617 prefixEnd_502617 76469364776582294037337 := by
  unfold tailWord_502617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331948020111923994626105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12221298680074615996417403 18331948020111923994626105)
  ·
    refine ⟨13748961015083942995969579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18331948020111923994626105 13748961015083942995969579)
    ·
      refine ⟨20623441522625914493954369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13748961015083942995969579 20623441522625914493954369)
      ·
        refine ⟨15467581141969435870465777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20623441522625914493954369 15467581141969435870465777)
        ·
          refine ⟨11600685856477076902849333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15467581141969435870465777 11600685856477076902849333)
          ·
            refine ⟨1087564299044725959642125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11600685856477076902849333 1087564299044725959642125)
            ·
              refine ⟨407836612141772234865797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1087564299044725959642125 407836612141772234865797)
              ·
                refine ⟨76469364776582294037337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407836612141772234865797 76469364776582294037337)
                ·
                  rfl

theorem cell20_502617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_502617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502617 prefixEnd_502617 := by exact prefixLift 502617
  have htrace : WordTrace (prefixWord ++ tailWord_502617) baseStart_502617 baseEnd_502617 := by
    simpa [prefixWord, tailWord_502617, baseEnd_502617] using wordTrace_append hprefix tailTrace_502617
  have hstable : (prefixWord ++ tailWord_502617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502617).length < 2 ^ (prefixWord ++ tailWord_502617).sum := by decide
  have hdescent : baseEnd_502617 < baseStart_502617 := by decide
  rcases family_descends (prefixWord ++ tailWord_502617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502627 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 2]
def baseStart_502627 : Nat := 118140960795 + 502627 * 2 ^ 59
def prefixEnd_502627 : Nat := 4983230072969 + 3 ^ 40 * 502627 * 2
def baseEnd_502627 : Nat := 229412658602231291778637

theorem tailTrace_502627 : CollatzResearch.WordTrace tailWord_502627 prefixEnd_502627 229412658602231291778637 := by
  unfold tailWord_502627
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332312750075695702490135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12221541833383797134993423 18332312750075695702490135)
  ·
    refine ⟨27498469125113543553735203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18332312750075695702490135 27498469125113543553735203)
    ·
      refine ⟨41247703687670315330602805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27498469125113543553735203 41247703687670315330602805)
      ·
        refine ⟨3866972220719092062244013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41247703687670315330602805 3866972220719092062244013)
        ·
          refine ⟨1450114582769659523341505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3866972220719092062244013 1450114582769659523341505)
          ·
            refine ⟨1087585937077244642506129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450114582769659523341505 1087585937077244642506129)
            ·
              refine ⟨815689452807933481879597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087585937077244642506129 815689452807933481879597)
              ·
                refine ⟨305883544802975055704849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815689452807933481879597 305883544802975055704849)
                ·
                  refine ⟨229412658602231291778637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305883544802975055704849 229412658602231291778637)
                  ·
                    rfl

theorem cell20_502627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 2].length) (baseStart_502627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502627 prefixEnd_502627 := by exact prefixLift 502627
  have htrace : WordTrace (prefixWord ++ tailWord_502627) baseStart_502627 baseEnd_502627 := by
    simpa [prefixWord, tailWord_502627, baseEnd_502627] using wordTrace_append hprefix tailTrace_502627
  have hstable : (prefixWord ++ tailWord_502627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502627).length < 2 ^ (prefixWord ++ tailWord_502627).sum := by decide
  have hdescent : baseEnd_502627 < baseStart_502627 := by decide
  rcases family_descends (prefixWord ++ tailWord_502627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502641 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 3]
def baseStart_502641 : Nat := 118140960795 + 502641 * 2 ^ 59
def prefixEnd_502641 : Nat := 4983230072969 + 3 ^ 40 * 502641 * 2
def baseEnd_502641 : Nat := 229419048583709465311913

theorem tailTrace_502641 : CollatzResearch.WordTrace tailWord_502641 prefixEnd_502641 229419048583709465311913 := by
  unfold tailWord_502641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332823372024976093499777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12221882248016650728999851 18332823372024976093499777)
  ·
    refine ⟨13749617529018732070124833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18332823372024976093499777 13749617529018732070124833)
    ·
      refine ⟨10312213146764049052593625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13749617529018732070124833 10312213146764049052593625)
      ·
        refine ⟨7734159860073036789445219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10312213146764049052593625 7734159860073036789445219)
        ·
          refine ⟨11601239790109555184167829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734159860073036789445219 11601239790109555184167829)
          ·
            refine ⟨543808115161385399257867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11601239790109555184167829 543808115161385399257867)
            ·
              refine ⟨815712172742078098886801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543808115161385399257867 815712172742078098886801)
              ·
                refine ⟨611784129556558574165101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815712172742078098886801 611784129556558574165101)
                ·
                  refine ⟨229419048583709465311913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611784129556558574165101 229419048583709465311913)
                  ·
                    rfl

theorem cell20_502641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_502641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502641 prefixEnd_502641 := by exact prefixLift 502641
  have htrace : WordTrace (prefixWord ++ tailWord_502641) baseStart_502641 baseEnd_502641 := by
    simpa [prefixWord, tailWord_502641, baseEnd_502641] using wordTrace_append hprefix tailTrace_502641
  have hstable : (prefixWord ++ tailWord_502641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502641).length < 2 ^ (prefixWord ++ tailWord_502641).sum := by decide
  have hdescent : baseEnd_502641 < baseStart_502641 := by decide
  rcases family_descends (prefixWord ++ tailWord_502641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502678 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_502678 : Nat := 118140960795 + 502678 * 2 ^ 59
def prefixEnd_502678 : Nat := 4983230072969 + 3 ^ 40 * 502678 * 2
def baseEnd_502678 : Nat := 229435936391901781078429

theorem tailTrace_502678 : CollatzResearch.WordTrace tailWord_502678 prefixEnd_502678 229435936391901781078429 := by
  unfold tailWord_502678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145885804555683213287293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12222781915260620941731125 1145885804555683213287293)
  ·
    refine ⟨429707176708381204982735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1145885804555683213287293 429707176708381204982735)
    ·
      refine ⟨644560765062571807474103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429707176708381204982735 644560765062571807474103)
      ·
        refine ⟨966841147593857711211155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644560765062571807474103 966841147593857711211155)
        ·
          refine ⟨1450261721390786566816733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966841147593857711211155 1450261721390786566816733)
          ·
            refine ⟨543848145521544962556275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1450261721390786566816733 543848145521544962556275)
            ·
              refine ⟨815772218282317443834413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543848145521544962556275 815772218282317443834413)
              ·
                refine ⟨305914581855869041437905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815772218282317443834413 305914581855869041437905)
                ·
                  refine ⟨229435936391901781078429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305914581855869041437905 229435936391901781078429)
                  ·
                    rfl

theorem cell20_502678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_502678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502678 prefixEnd_502678 := by exact prefixLift 502678
  have htrace : WordTrace (prefixWord ++ tailWord_502678) baseStart_502678 baseEnd_502678 := by
    simpa [prefixWord, tailWord_502678, baseEnd_502678] using wordTrace_append hprefix tailTrace_502678
  have hstable : (prefixWord ++ tailWord_502678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502678).length < 2 ^ (prefixWord ++ tailWord_502678).sum := by decide
  have hdescent : baseEnd_502678 < baseStart_502678 := by decide
  rcases family_descends (prefixWord ++ tailWord_502678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502682 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_502682 : Nat := 118140960795 + 502682 * 2 ^ 59
def prefixEnd_502682 : Nat := 4983230072969 + 3 ^ 40 * 502682 * 2
def baseEnd_502682 : Nat := 229437762100895544945079

theorem tailTrace_502682 : CollatzResearch.WordTrace tailWord_502682 prefixEnd_502682 229437762100895544945079 := by
  unfold tailWord_502682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583579691219110023935575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12222879176584293397161533 4583579691219110023935575)
  ·
    refine ⟨6875369536828665035903363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4583579691219110023935575 6875369536828665035903363)
    ·
      refine ⟨10313054305242997553855045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6875369536828665035903363 10313054305242997553855045)
      ·
        refine ⟨1933697682233062041347821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10313054305242997553855045 1933697682233062041347821)
        ·
          refine ⟨725136630837398265505433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1933697682233062041347821 725136630837398265505433)
          ·
            refine ⟨543852473128048699129075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725136630837398265505433 543852473128048699129075)
            ·
              refine ⟨815778709692073048693613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543852473128048699129075 815778709692073048693613)
              ·
                refine ⟨305917016134527393260105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815778709692073048693613 305917016134527393260105)
                ·
                  refine ⟨229437762100895544945079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305917016134527393260105 229437762100895544945079)
                  ·
                    rfl

theorem cell20_502682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_502682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502682 prefixEnd_502682 := by exact prefixLift 502682
  have htrace : WordTrace (prefixWord ++ tailWord_502682) baseStart_502682 baseEnd_502682 := by
    simpa [prefixWord, tailWord_502682, baseEnd_502682] using wordTrace_append hprefix tailTrace_502682
  have hstable : (prefixWord ++ tailWord_502682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502682).length < 2 ^ (prefixWord ++ tailWord_502682).sum := by decide
  have hdescent : baseEnd_502682 < baseStart_502682 := by decide
  rcases family_descends (prefixWord ++ tailWord_502682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502714 : List Nat := [3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_502714 : Nat := 118140960795 + 502714 * 2 ^ 59
def prefixEnd_502714 : Nat := 4983230072969 + 3 ^ 40 * 502714 * 2
def baseEnd_502714 : Nat := 76484122590948551959427

theorem tailTrace_502714 : CollatzResearch.WordTrace tailWord_502714 prefixEnd_502714 76484122590948551959427 := by
  unfold tailWord_502714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583871475190127390226799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12223657267173673040604797 4583871475190127390226799)
  ·
    refine ⟨6875807212785191085340199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4583871475190127390226799 6875807212785191085340199)
    ·
      refine ⟨10313710819177786628010299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6875807212785191085340199 10313710819177786628010299)
      ·
        refine ⟨15470566228766679942015449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10313710819177786628010299 15470566228766679942015449)
        ·
          refine ⟨11602924671575009956511587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15470566228766679942015449 11602924671575009956511587)
          ·
            refine ⟨17404387007362514934767381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602924671575009956511587 17404387007362514934767381)
            ·
              refine ⟨815830640970117887567221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17404387007362514934767381 815830640970117887567221)
              ·
                refine ⟨76484122590948551959427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 815830640970117887567221 76484122590948551959427)
                ·
                  rfl

theorem cell20_502714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_502714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502714 prefixEnd_502714 := by exact prefixLift 502714
  have htrace : WordTrace (prefixWord ++ tailWord_502714) baseStart_502714 baseEnd_502714 := by
    simpa [prefixWord, tailWord_502714, baseEnd_502714] using wordTrace_append hprefix tailTrace_502714
  have hstable : (prefixWord ++ tailWord_502714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502714).length < 2 ^ (prefixWord ++ tailWord_502714).sum := by decide
  have hdescent : baseEnd_502714 < baseStart_502714 := by decide
  rcases family_descends (prefixWord ++ tailWord_502714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502717 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_502717 : Nat := 118140960795 + 502717 * 2 ^ 59
def prefixEnd_502717 : Nat := 4983230072969 + 3 ^ 40 * 502717 * 2
def baseEnd_502717 : Nat := 229453737054590978778269

theorem tailTrace_502717 : CollatzResearch.WordTrace tailWord_502717 prefixEnd_502717 229453737054590978778269 := by
  unfold tailWord_502717
  simp only [CollatzResearch.WordTrace]
  refine ⟨18335595319749641073266405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12223730213166427382177603 18335595319749641073266405)
  ·
    refine ⟨3437924122453057701237451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18335595319749641073266405 3437924122453057701237451)
    ·
      refine ⟨5156886183679586551856177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437924122453057701237451 5156886183679586551856177)
      ·
        refine ⟨3867664637759689913892133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5156886183679586551856177 3867664637759689913892133)
        ·
          refine ⟨725187119579941858854775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3867664637759689913892133 725187119579941858854775)
          ·
            refine ⟨1087780679369912788282163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725187119579941858854775 1087780679369912788282163)
            ·
              refine ⟨1631671019054869182423245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087780679369912788282163 1631671019054869182423245)
              ·
                refine ⟨611876632145575943408717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631671019054869182423245 611876632145575943408717)
                ·
                  refine ⟨229453737054590978778269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611876632145575943408717 229453737054590978778269)
                  ·
                    rfl

theorem cell20_502717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_502717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502717 prefixEnd_502717 := by exact prefixLift 502717
  have htrace : WordTrace (prefixWord ++ tailWord_502717) baseStart_502717 baseEnd_502717 := by
    simpa [prefixWord, tailWord_502717, baseEnd_502717] using wordTrace_append hprefix tailTrace_502717
  have hstable : (prefixWord ++ tailWord_502717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502717).length < 2 ^ (prefixWord ++ tailWord_502717).sum := by decide
  have hdescent : baseEnd_502717 < baseStart_502717 := by decide
  rcases family_descends (prefixWord ++ tailWord_502717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502769 : List Nat := [1, 2, 2, 2, 4, 3, 1, 5]
def baseStart_502769 : Nat := 118140960795 + 502769 * 2 ^ 59
def prefixEnd_502769 : Nat := 4983230072969 + 3 ^ 40 * 502769 * 2
def baseEnd_502769 : Nat := 76492490423836636348241

theorem tailTrace_502769 : CollatzResearch.WordTrace tailWord_502769 prefixEnd_502769 76492490423836636348241 := by
  unfold tailWord_502769
  simp only [CollatzResearch.WordTrace]
  refine ⟨18337491915561253954159361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12224994610374169302772907 18337491915561253954159361)
  ·
    refine ⟨13753118936670940465619521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18337491915561253954159361 13753118936670940465619521)
    ·
      refine ⟨10314839202503205349214641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13753118936670940465619521 10314839202503205349214641)
      ·
        refine ⟨7736129401877404011910981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10314839202503205349214641 7736129401877404011910981)
        ·
          refine ⟨1450524262852013252233309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7736129401877404011910981 1450524262852013252233309)
          ·
            refine ⟨543946598569504969587491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1450524262852013252233309 543946598569504969587491)
            ·
              refine ⟨815919897854257454381237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543946598569504969587491 815919897854257454381237)
              ·
                refine ⟨76492490423836636348241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 815919897854257454381237 76492490423836636348241)
                ·
                  rfl

theorem cell20_502769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_502769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502769 prefixEnd_502769 := by exact prefixLift 502769
  have htrace : WordTrace (prefixWord ++ tailWord_502769) baseStart_502769 baseEnd_502769 := by
    simpa [prefixWord, tailWord_502769, baseEnd_502769] using wordTrace_append hprefix tailTrace_502769
  have hstable : (prefixWord ++ tailWord_502769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502769).length < 2 ^ (prefixWord ++ tailWord_502769).sum := by decide
  have hdescent : baseEnd_502769 < baseStart_502769 := by decide
  rcases family_descends (prefixWord ++ tailWord_502769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502821 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_502821 : Nat := 118140960795 + 502821 * 2 ^ 59
def prefixEnd_502821 : Nat := 4983230072969 + 3 ^ 40 * 502821 * 2
def baseEnd_502821 : Nat := 229501205488428839311177

theorem tailTrace_502821 : CollatzResearch.WordTrace tailWord_502821 prefixEnd_502821 229501205488428839311177 := by
  unfold tailWord_502821
  simp only [CollatzResearch.WordTrace]
  refine ⟨18339388511372866835052317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12226259007581911223368211 18339388511372866835052317)
  ·
    refine ⟨6877270691764825063144619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18339388511372866835052317 6877270691764825063144619)
    ·
      refine ⟨10315906037647237594716929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877270691764825063144619 10315906037647237594716929)
      ·
        refine ⟨7736929528235428196037697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10315906037647237594716929 7736929528235428196037697)
        ·
          refine ⟨5802697146176571147028273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7736929528235428196037697 5802697146176571147028273)
          ·
            refine ⟨4352022859632428360271205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5802697146176571147028273 4352022859632428360271205)
            ·
              refine ⟨816004286181080317550851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4352022859632428360271205 816004286181080317550851)
              ·
                refine ⟨1224006429271620476326277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816004286181080317550851 1224006429271620476326277)
                ·
                  refine ⟨229501205488428839311177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224006429271620476326277 229501205488428839311177)
                  ·
                    rfl

theorem cell20_502821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_502821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502821 prefixEnd_502821 := by exact prefixLift 502821
  have htrace : WordTrace (prefixWord ++ tailWord_502821) baseStart_502821 baseEnd_502821 := by
    simpa [prefixWord, tailWord_502821, baseEnd_502821] using wordTrace_append hprefix tailTrace_502821
  have hstable : (prefixWord ++ tailWord_502821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502821).length < 2 ^ (prefixWord ++ tailWord_502821).sum := by decide
  have hdescent : baseEnd_502821 < baseStart_502821 := by decide
  rcases family_descends (prefixWord ++ tailWord_502821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502838 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_502838 : Nat := 118140960795 + 502838 * 2 ^ 59
def prefixEnd_502838 : Nat := 4983230072969 + 3 ^ 40 * 502838 * 2
def baseEnd_502838 : Nat := 229508964751652335744441

theorem tailTrace_502838 : CollatzResearch.WordTrace tailWord_502838 prefixEnd_502838 229508964751652335744441 := by
  unfold tailWord_502838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146250534519454921151323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12226672368207519158947445 1146250534519454921151323)
  ·
    refine ⟨1719375801779182381726985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146250534519454921151323 1719375801779182381726985)
    ·
      refine ⟨1289531851334386786295239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719375801779182381726985 1289531851334386786295239)
      ·
        refine ⟨1934297777001580179442859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289531851334386786295239 1934297777001580179442859)
        ·
          refine ⟨2901446665502370269164289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934297777001580179442859 2901446665502370269164289)
          ·
            refine ⟨2176084999126777701873217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901446665502370269164289 2176084999126777701873217)
            ·
              refine ⟨1632063749345083276404913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176084999126777701873217 1632063749345083276404913)
              ·
                refine ⟨1224047812008812457303685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632063749345083276404913 1224047812008812457303685)
                ·
                  refine ⟨229508964751652335744441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224047812008812457303685 229508964751652335744441)
                  ·
                    rfl

theorem cell20_502838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_502838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502838 prefixEnd_502838 := by exact prefixLift 502838
  have htrace : WordTrace (prefixWord ++ tailWord_502838) baseStart_502838 baseEnd_502838 := by
    simpa [prefixWord, tailWord_502838, baseEnd_502838] using wordTrace_append hprefix tailTrace_502838
  have hstable : (prefixWord ++ tailWord_502838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502838).length < 2 ^ (prefixWord ++ tailWord_502838).sum := by decide
  have hdescent : baseEnd_502838 < baseStart_502838 := by decide
  rcases family_descends (prefixWord ++ tailWord_502838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502845 : List Nat := [1, 4, 1, 3, 1, 2, 4, 4]
def baseStart_502845 : Nat := 118140960795 + 502845 * 2 ^ 59
def prefixEnd_502845 : Nat := 4983230072969 + 3 ^ 40 * 502845 * 2
def baseEnd_502845 : Nat := 76504053247463807503693

theorem tailTrace_502845 : CollatzResearch.WordTrace tailWord_502845 prefixEnd_502845 76504053247463807503693 := by
  unfold tailWord_502845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18340263863285918933925989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12226842575523945955950659 18340263863285918933925989)
  ·
    refine ⟨3438799474366109800111123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18340263863285918933925989 3438799474366109800111123)
    ·
      refine ⟨5158199211549164700166685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438799474366109800111123 5158199211549164700166685)
      ·
        refine ⟨1934324704330936762562507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5158199211549164700166685 1934324704330936762562507)
        ·
          refine ⟨2901487056496405143843761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934324704330936762562507 2901487056496405143843761)
          ·
            refine ⟨2176115292372303857882821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901487056496405143843761 2176115292372303857882821)
            ·
              refine ⟨408021617319806973353029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2176115292372303857882821 408021617319806973353029)
              ·
                refine ⟨76504053247463807503693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408021617319806973353029 76504053247463807503693)
                ·
                  rfl

theorem cell20_502845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_502845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502845 prefixEnd_502845 := by exact prefixLift 502845
  have htrace : WordTrace (prefixWord ++ tailWord_502845) baseStart_502845 baseEnd_502845 := by
    simpa [prefixWord, tailWord_502845, baseEnd_502845] using wordTrace_append hprefix tailTrace_502845
  have hstable : (prefixWord ++ tailWord_502845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502845).length < 2 ^ (prefixWord ++ tailWord_502845).sum := by decide
  have hdescent : baseEnd_502845 < baseStart_502845 := by decide
  rcases family_descends (prefixWord ++ tailWord_502845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502855 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 2]
def baseStart_502855 : Nat := 118140960795 + 502855 * 2 ^ 59
def prefixEnd_502855 : Nat := 4983230072969 + 3 ^ 40 * 502855 * 2
def baseEnd_502855 : Nat := 229516724014875832177705

theorem tailTrace_502855 : CollatzResearch.WordTrace tailWord_502855 prefixEnd_502855 229516724014875832177705 := by
  unfold tailWord_502855
  simp only [CollatzResearch.WordTrace]
  refine ⟨18340628593249690641790019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12227085728833127094526679 18340628593249690641790019)
  ·
    refine ⟨27510942889874535962685029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18340628593249690641790019 27510942889874535962685029)
    ·
      refine ⟨5158301791851475493003443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27510942889874535962685029 5158301791851475493003443)
      ·
        refine ⟨7737452687777213239505165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158301791851475493003443 7737452687777213239505165)
        ·
          refine ⟨2901544757916454964814437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7737452687777213239505165 2901544757916454964814437)
          ·
            refine ⟨544039642109335305902707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2901544757916454964814437 544039642109335305902707)
            ·
              refine ⟨816059463164002958854061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544039642109335305902707 816059463164002958854061)
              ·
                refine ⟨306022298686501109570273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 816059463164002958854061 306022298686501109570273)
                ·
                  refine ⟨229516724014875832177705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306022298686501109570273 229516724014875832177705)
                  ·
                    rfl

theorem cell20_502855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 2].length) (baseStart_502855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502855 prefixEnd_502855 := by exact prefixLift 502855
  have htrace : WordTrace (prefixWord ++ tailWord_502855) baseStart_502855 baseEnd_502855 := by
    simpa [prefixWord, tailWord_502855, baseEnd_502855] using wordTrace_append hprefix tailTrace_502855
  have hstable : (prefixWord ++ tailWord_502855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502855).length < 2 ^ (prefixWord ++ tailWord_502855).sum := by decide
  have hdescent : baseEnd_502855 < baseStart_502855 := by decide
  rcases family_descends (prefixWord ++ tailWord_502855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502866 : List Nat := [3, 2, 2, 1, 3, 1, 8]
def baseStart_502866 : Nat := 118140960795 + 502866 * 2 ^ 59
def prefixEnd_502866 : Nat := 4983230072969 + 3 ^ 40 * 502866 * 2
def baseEnd_502866 : Nat := 25502416079400964756777

theorem tailTrace_502866 : CollatzResearch.WordTrace tailWord_502866 prefixEnd_502866 25502416079400964756777 := by
  unfold tailWord_502866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585257449052459880110113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12227353197473226346960301 4585257449052459880110113)
  ·
    refine ⟨3438943086789344910082585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4585257449052459880110113 3438943086789344910082585)
    ·
      refine ⟨2579207315092008682561939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3438943086789344910082585 2579207315092008682561939)
      ·
        refine ⟨3868810972638013023842909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579207315092008682561939 3868810972638013023842909)
        ·
          refine ⟨1450804114739254883941091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3868810972638013023842909 1450804114739254883941091)
          ·
            refine ⟨2176206172108882325911637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450804114739254883941091 2176206172108882325911637)
            ·
              refine ⟨25502416079400964756777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2176206172108882325911637 25502416079400964756777)
              ·
                rfl

theorem cell20_502866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_502866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502866 prefixEnd_502866 := by exact prefixLift 502866
  have htrace : WordTrace (prefixWord ++ tailWord_502866) baseStart_502866 baseEnd_502866 := by
    simpa [prefixWord, tailWord_502866, baseEnd_502866] using wordTrace_append hprefix tailTrace_502866
  have hstable : (prefixWord ++ tailWord_502866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502866).length < 2 ^ (prefixWord ++ tailWord_502866).sum := by decide
  have hdescent : baseEnd_502866 < baseStart_502866 := by decide
  rcases family_descends (prefixWord ++ tailWord_502866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502963 : List Nat := [1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_502963 : Nat := 118140960795 + 502963 * 2 ^ 59
def prefixEnd_502963 : Nat := 4983230072969 + 3 ^ 40 * 502963 * 2
def baseEnd_502963 : Nat := 76522006052569152192421

theorem tailTrace_502963 : CollatzResearch.WordTrace tailWord_502963 prefixEnd_502963 76522006052569152192421 := by
  unfold tailWord_502963
  simp only [CollatzResearch.WordTrace]
  refine ⟨18344567676858425086721543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12229711784572283391147695 18344567676858425086721543)
  ·
    refine ⟨27516851515287637630082315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18344567676858425086721543 27516851515287637630082315)
    ·
      refine ⟨41275277272931456445123473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27516851515287637630082315 41275277272931456445123473)
      ·
        refine ⟨30956457954698592333842605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41275277272931456445123473 30956457954698592333842605)
        ·
          refine ⟨11608671733011972125190977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30956457954698592333842605 11608671733011972125190977)
          ·
            refine ⟨8706503799758979093893233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608671733011972125190977 8706503799758979093893233)
            ·
              refine ⟨6529877849819234320419925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706503799758979093893233 6529877849819234320419925)
              ·
                refine ⟨76522006052569152192421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6529877849819234320419925 76522006052569152192421)
                ·
                  rfl

theorem cell20_502963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_502963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502963 prefixEnd_502963 := by exact prefixLift 502963
  have htrace : WordTrace (prefixWord ++ tailWord_502963) baseStart_502963 baseEnd_502963 := by
    simpa [prefixWord, tailWord_502963, baseEnd_502963] using wordTrace_append hprefix tailTrace_502963
  have hstable : (prefixWord ++ tailWord_502963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502963).length < 2 ^ (prefixWord ++ tailWord_502963).sum := by decide
  have hdescent : baseEnd_502963 < baseStart_502963 := by decide
  rcases family_descends (prefixWord ++ tailWord_502963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502987 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_502987 : Nat := 118140960795 + 502987 * 2 ^ 59
def prefixEnd_502987 : Nat := 4983230072969 + 3 ^ 40 * 502987 * 2
def baseEnd_502987 : Nat := 229576972411670039777165

theorem tailTrace_502987 : CollatzResearch.WordTrace tailWord_502987 prefixEnd_502987 229576972411670039777165 := by
  unfold tailWord_502987
  simp only [CollatzResearch.WordTrace]
  refine ⟨18345443028771477185595215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12230295352514318123730143 18345443028771477185595215)
  ·
    refine ⟨27518164543157215778392823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18345443028771477185595215 27518164543157215778392823)
    ·
      refine ⟨41277246814735823667589235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27518164543157215778392823 41277246814735823667589235)
      ·
        refine ⟨61915870222103735501383853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41277246814735823667589235 61915870222103735501383853)
        ·
          refine ⟨23218451333288900813018945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61915870222103735501383853 23218451333288900813018945)
          ·
            refine ⟨17413838499966675609764209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23218451333288900813018945 17413838499966675609764209)
            ·
              refine ⟨13060378874975006707323157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17413838499966675609764209 13060378874975006707323157)
              ·
                refine ⟨612205259764453439405773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13060378874975006707323157 612205259764453439405773)
                ·
                  refine ⟨229576972411670039777165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612205259764453439405773 229576972411670039777165)
                  ·
                    rfl

theorem cell20_502987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_502987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502987 prefixEnd_502987 := by exact prefixLift 502987
  have htrace : WordTrace (prefixWord ++ tailWord_502987) baseStart_502987 baseEnd_502987 := by
    simpa [prefixWord, tailWord_502987, baseEnd_502987] using wordTrace_append hprefix tailTrace_502987
  have hstable : (prefixWord ++ tailWord_502987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502987).length < 2 ^ (prefixWord ++ tailWord_502987).sum := by decide
  have hdescent : baseEnd_502987 < baseStart_502987 := by decide
  rcases family_descends (prefixWord ++ tailWord_502987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502990 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_502990 : Nat := 118140960795 + 502990 * 2 ^ 59
def prefixEnd_502990 : Nat := 4983230072969 + 3 ^ 40 * 502990 * 2
def baseEnd_502990 : Nat := 229578341693415362677153

theorem tailTrace_502990 : CollatzResearch.WordTrace tailWord_502990 prefixEnd_502990 229578341693415362677153 := by
  unfold tailWord_502990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293194055970076087244303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12230368298507072465302949 2293194055970076087244303)
  ·
    refine ⟨3439791083955114130866455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2293194055970076087244303 3439791083955114130866455)
    ·
      refine ⟨5159686625932671196299683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3439791083955114130866455 5159686625932671196299683)
      ·
        refine ⟨7739529938899006794449525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159686625932671196299683 7739529938899006794449525)
        ·
          refine ⟨725580931771781886979643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7739529938899006794449525 725580931771781886979643)
          ·
            refine ⟨1088371397657672830469465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725580931771781886979643 1088371397657672830469465)
            ·
              refine ⟨816278548243254622852099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088371397657672830469465 816278548243254622852099)
              ·
                refine ⟨1224417822364881934278149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816278548243254622852099 1224417822364881934278149)
                ·
                  refine ⟨229578341693415362677153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224417822364881934278149 229578341693415362677153)
                  ·
                    rfl

theorem cell20_502990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_502990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_502990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_502990 prefixEnd_502990 := by exact prefixLift 502990
  have htrace : WordTrace (prefixWord ++ tailWord_502990) baseStart_502990 baseEnd_502990 := by
    simpa [prefixWord, tailWord_502990, baseEnd_502990] using wordTrace_append hprefix tailTrace_502990
  have hstable : (prefixWord ++ tailWord_502990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502990).length < 2 ^ (prefixWord ++ tailWord_502990).sum := by decide
  have hdescent : baseEnd_502990 < baseStart_502990 := by decide
  rcases family_descends (prefixWord ++ tailWord_502990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503001 : List Nat := [1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_503001 : Nat := 118140960795 + 503001 * 2 ^ 59
def prefixEnd_503001 : Nat := 4983230072969 + 3 ^ 40 * 503001 * 2
def baseEnd_503001 : Nat := 76527787464382737770147

theorem tailTrace_503001 : CollatzResearch.WordTrace tailWord_503001 prefixEnd_503001 76527787464382737770147 := by
  unfold tailWord_503001
  simp only [CollatzResearch.WordTrace]
  refine ⟨18345953650720757576604857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12230635767147171717736571 18345953650720757576604857)
  ·
    refine ⟨13759465238040568182453643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18345953650720757576604857 13759465238040568182453643)
    ·
      refine ⟨20639197857060852273680465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13759465238040568182453643 20639197857060852273680465)
      ·
        refine ⟨15479398392795639205260349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20639197857060852273680465 15479398392795639205260349)
        ·
          refine ⟨5804774397298364701972631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15479398392795639205260349 5804774397298364701972631)
          ·
            refine ⟨8707161595947547052958947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804774397298364701972631 8707161595947547052958947)
            ·
              refine ⟨13060742393921320579438421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707161595947547052958947 13060742393921320579438421)
              ·
                refine ⟨76527787464382737770147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13060742393921320579438421 76527787464382737770147)
                ·
                  rfl

theorem cell20_503001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_503001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503001 prefixEnd_503001 := by exact prefixLift 503001
  have htrace : WordTrace (prefixWord ++ tailWord_503001) baseStart_503001 baseEnd_503001 := by
    simpa [prefixWord, tailWord_503001, baseEnd_503001] using wordTrace_append hprefix tailTrace_503001
  have hstable : (prefixWord ++ tailWord_503001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503001).length < 2 ^ (prefixWord ++ tailWord_503001).sum := by decide
  have hdescent : baseEnd_503001 < baseStart_503001 := by decide
  rcases family_descends (prefixWord ++ tailWord_503001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503018 : List Nat := [3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_503018 : Nat := 118140960795 + 503018 * 2 ^ 59
def prefixEnd_503018 : Nat := 4983230072969 + 3 ^ 40 * 503018 * 2
def baseEnd_503018 : Nat := 76530373885457236581235

theorem tailTrace_503018 : CollatzResearch.WordTrace tailWord_503018 prefixEnd_503018 76530373885457236581235 := by
  unfold tailWord_503018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586643422914792369993427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12231049127772779653315805 4586643422914792369993427)
  ·
    refine ⟨6879965134372188554990141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586643422914792369993427 6879965134372188554990141)
    ·
      refine ⟨2579986925389570708121303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6879965134372188554990141 2579986925389570708121303)
      ·
        refine ⟨3869980388084356062181955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579986925389570708121303 3869980388084356062181955)
        ·
          refine ⟨5804970582126534093272933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869980388084356062181955 5804970582126534093272933)
          ·
            refine ⟨1088431984148725142488675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5804970582126534093272933 1088431984148725142488675)
            ·
              refine ⟨1632647976223087713733013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088431984148725142488675 1632647976223087713733013)
              ·
                refine ⟨76530373885457236581235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1632647976223087713733013 76530373885457236581235)
                ·
                  rfl

theorem cell20_503018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_503018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503018 prefixEnd_503018 := by exact prefixLift 503018
  have htrace : WordTrace (prefixWord ++ tailWord_503018) baseStart_503018 baseEnd_503018 := by
    simpa [prefixWord, tailWord_503018, baseEnd_503018] using wordTrace_append hprefix tailTrace_503018
  have hstable : (prefixWord ++ tailWord_503018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503018).length < 2 ^ (prefixWord ++ tailWord_503018).sum := by decide
  have hdescent : baseEnd_503018 < baseStart_503018 := by decide
  rcases family_descends (prefixWord ++ tailWord_503018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503039 : List Nat := [1, 1, 2, 2, 1, 5, 8]
def baseStart_503039 : Nat := 118140960795 + 503039 * 2 ^ 59
def prefixEnd_503039 : Nat := 4983230072969 + 3 ^ 40 * 503039 * 2
def baseEnd_503039 : Nat := 25511189625398774449291

theorem tailTrace_503039 : CollatzResearch.WordTrace tailWord_503039 prefixEnd_503039 25511189625398774449291 := by
  unfold tailWord_503039
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347339624583090066488171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12231559749722060044325447 18347339624583090066488171)
  ·
    refine ⟨27521009436874635099732257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18347339624583090066488171 27521009436874635099732257)
    ·
      refine ⟨20640757077655976324799193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27521009436874635099732257 20640757077655976324799193)
      ·
        refine ⟨15480567808241982243599395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20640757077655976324799193 15480567808241982243599395)
        ·
          refine ⟨23220851712362973365399093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15480567808241982243599395 23220851712362973365399093)
          ·
            refine ⟨2176954848034028753006165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23220851712362973365399093 2176954848034028753006165)
            ·
              refine ⟨25511189625398774449291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2176954848034028753006165 25511189625398774449291)
              ·
                rfl

theorem cell20_503039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_503039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503039 prefixEnd_503039 := by exact prefixLift 503039
  have htrace : WordTrace (prefixWord ++ tailWord_503039) baseStart_503039 baseEnd_503039 := by
    simpa [prefixWord, tailWord_503039, baseEnd_503039] using wordTrace_append hprefix tailTrace_503039
  have hstable : (prefixWord ++ tailWord_503039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503039).length < 2 ^ (prefixWord ++ tailWord_503039).sum := by decide
  have hdescent : baseEnd_503039 < baseStart_503039 := by decide
  rcases family_descends (prefixWord ++ tailWord_503039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503087 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 2]
def baseStart_503087 : Nat := 118140960795 + 503087 * 2 ^ 59
def prefixEnd_503087 : Nat := 4983230072969 + 3 ^ 40 * 503087 * 2
def baseEnd_503087 : Nat := 229622615136514136443423

theorem tailTrace_503087 : CollatzResearch.WordTrace tailWord_503087 prefixEnd_503087 229622615136514136443423 := by
  unfold tailWord_503087
  simp only [CollatzResearch.WordTrace]
  refine ⟨18349090328409194264235515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12232726885606129509490343 18349090328409194264235515)
  ·
    refine ⟨27523635492613791396353273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18349090328409194264235515 27523635492613791396353273)
    ·
      refine ⟨20642726619460343547264955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27523635492613791396353273 20642726619460343547264955)
      ·
        refine ⟨30964089929190515320897433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20642726619460343547264955 30964089929190515320897433)
        ·
          refine ⟨23223067446892886490673075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30964089929190515320897433 23223067446892886490673075)
          ·
            refine ⟨34834601170339329736009613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23223067446892886490673075 34834601170339329736009613)
            ·
              refine ⟨13062975438877248651003605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34834601170339329736009613 13062975438877248651003605)
              ·
                refine ⟨306163486848685515257897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13062975438877248651003605 306163486848685515257897)
                ·
                  refine ⟨229622615136514136443423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306163486848685515257897 229622615136514136443423)
                  ·
                    rfl

theorem cell20_503087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 2].length) (baseStart_503087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503087 prefixEnd_503087 := by exact prefixLift 503087
  have htrace : WordTrace (prefixWord ++ tailWord_503087) baseStart_503087 baseEnd_503087 := by
    simpa [prefixWord, tailWord_503087, baseEnd_503087] using wordTrace_append hprefix tailTrace_503087
  have hstable : (prefixWord ++ tailWord_503087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503087).length < 2 ^ (prefixWord ++ tailWord_503087).sum := by decide
  have hdescent : baseEnd_503087 < baseStart_503087 := by decide
  rcases family_descends (prefixWord ++ tailWord_503087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503097 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_503097 : Nat := 118140960795 + 503097 * 2 ^ 59
def prefixEnd_503097 : Nat := 4983230072969 + 3 ^ 40 * 503097 * 2
def baseEnd_503097 : Nat := 229627179408998546110049

theorem tailTrace_503097 : CollatzResearch.WordTrace tailWord_503097 prefixEnd_503097 229627179408998546110049 := by
  unfold tailWord_503097
  simp only [CollatzResearch.WordTrace]
  refine ⟨18349455058372965972099545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12232970038915310648066363 18349455058372965972099545)
  ·
    refine ⟨13762091293779724479074659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18349455058372965972099545 13762091293779724479074659)
    ·
      refine ⟨20643136940669586718611989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13762091293779724479074659 20643136940669586718611989)
      ·
        refine ⟨967647044093886877434937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20643136940669586718611989 967647044093886877434937)
        ·
          refine ⟨725735283070415158076203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967647044093886877434937 725735283070415158076203)
          ·
            refine ⟨1088602924605622737114305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725735283070415158076203 1088602924605622737114305)
            ·
              refine ⟨816452193454217052835729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088602924605622737114305 816452193454217052835729)
              ·
                refine ⟨612339145090662789626797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816452193454217052835729 612339145090662789626797)
                ·
                  refine ⟨229627179408998546110049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612339145090662789626797 229627179408998546110049)
                  ·
                    rfl

theorem cell20_503097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_503097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503097 prefixEnd_503097 := by exact prefixLift 503097
  have htrace : WordTrace (prefixWord ++ tailWord_503097) baseStart_503097 baseEnd_503097 := by
    simpa [prefixWord, tailWord_503097, baseEnd_503097] using wordTrace_append hprefix tailTrace_503097
  have hstable : (prefixWord ++ tailWord_503097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503097).length < 2 ^ (prefixWord ++ tailWord_503097).sum := by decide
  have hdescent : baseEnd_503097 < baseStart_503097 := by decide
  rcases family_descends (prefixWord ++ tailWord_503097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503125 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_503125 : Nat := 118140960795 + 503125 * 2 ^ 59
def prefixEnd_503125 : Nat := 4983230072969 + 3 ^ 40 * 503125 * 2
def baseEnd_503125 : Nat := 229639959371954893176601

theorem tailTrace_503125 : CollatzResearch.WordTrace tailWord_503125 prefixEnd_503125 229639959371954893176601 := by
  unfold tailWord_503125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350476302271526754118829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12233650868181017836079219 18350476302271526754118829)
  ·
    refine ⟨6881428613351822532794561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18350476302271526754118829 6881428613351822532794561)
    ·
      refine ⟨5161071460013866899595921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6881428613351822532794561 5161071460013866899595921)
      ·
        refine ⟨3870803595010400174696941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5161071460013866899595921 3870803595010400174696941)
        ·
          refine ⟨1451551348128900065511353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3870803595010400174696941 1451551348128900065511353)
          ·
            refine ⟨1088663511096675049133515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451551348128900065511353 1088663511096675049133515)
            ·
              refine ⟨1632995266645012573700273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088663511096675049133515 1632995266645012573700273)
              ·
                refine ⟨1224746449983759430275205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632995266645012573700273 1224746449983759430275205)
                ·
                  refine ⟨229639959371954893176601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1224746449983759430275205 229639959371954893176601)
                  ·
                    rfl

theorem cell20_503125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_503125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503125 prefixEnd_503125 := by exact prefixLift 503125
  have htrace : WordTrace (prefixWord ++ tailWord_503125) baseStart_503125 baseEnd_503125 := by
    simpa [prefixWord, tailWord_503125, baseEnd_503125] using wordTrace_append hprefix tailTrace_503125
  have hstable : (prefixWord ++ tailWord_503125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503125).length < 2 ^ (prefixWord ++ tailWord_503125).sum := by decide
  have hdescent : baseEnd_503125 < baseStart_503125 := by decide
  rcases family_descends (prefixWord ++ tailWord_503125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503163 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 2]
def baseStart_503163 : Nat := 118140960795 + 503163 * 2 ^ 59
def prefixEnd_503163 : Nat := 4983230072969 + 3 ^ 40 * 503163 * 2
def baseEnd_503163 : Nat := 229657303607395649909779

theorem tailTrace_503163 : CollatzResearch.WordTrace tailWord_503163 prefixEnd_503163 229657303607395649909779 := by
  unfold tailWord_503163
  simp only [CollatzResearch.WordTrace]
  refine ⟨18351862276133859244002143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12234574850755906162668095 18351862276133859244002143)
  ·
    refine ⟨27527793414200788866003215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18351862276133859244002143 27527793414200788866003215)
    ·
      refine ⟨41291690121301183299004823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27527793414200788866003215 41291690121301183299004823)
      ·
        refine ⟨61937535181951774948507235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41291690121301183299004823 61937535181951774948507235)
        ·
          refine ⟨92906302772927662422760853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61937535181951774948507235 92906302772927662422760853)
          ·
            refine ⟨4354982942480984176066915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92906302772927662422760853 4354982942480984176066915)
            ·
              refine ⟨6532474413721476264100373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354982942480984176066915 6532474413721476264100373)
              ·
                refine ⟨306209738143194199879705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6532474413721476264100373 306209738143194199879705)
                ·
                  refine ⟨229657303607395649909779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306209738143194199879705 229657303607395649909779)
                  ·
                    rfl

theorem cell20_503163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 2].length) (baseStart_503163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503163 prefixEnd_503163 := by exact prefixLift 503163
  have htrace : WordTrace (prefixWord ++ tailWord_503163) baseStart_503163 baseEnd_503163 := by
    simpa [prefixWord, tailWord_503163, baseEnd_503163] using wordTrace_append hprefix tailTrace_503163
  have hstable : (prefixWord ++ tailWord_503163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503163).length < 2 ^ (prefixWord ++ tailWord_503163).sum := by decide
  have hdescent : baseEnd_503163 < baseStart_503163 := by decide
  rcases family_descends (prefixWord ++ tailWord_503163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503197 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 2]
def baseStart_503197 : Nat := 118140960795 + 503197 * 2 ^ 59
def prefixEnd_503197 : Nat := 4983230072969 + 3 ^ 40 * 503197 * 2
def baseEnd_503197 : Nat := 229672822133842642776307

theorem tailTrace_503197 : CollatzResearch.WordTrace tailWord_503197 prefixEnd_503197 229672822133842642776307 := by
  unfold tailWord_503197
  simp only [CollatzResearch.WordTrace]
  refine ⟨18353102358010683050739845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12235401572007122033826563 18353102358010683050739845)
  ·
    refine ⟨3441206692127003072013721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18353102358010683050739845 3441206692127003072013721)
    ·
      refine ⟨2580905019095252304010291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3441206692127003072013721 2580905019095252304010291)
      ·
        refine ⟨3871357528642878456015437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580905019095252304010291 3871357528642878456015437)
        ·
          refine ⟨1451759073241079421005789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3871357528642878456015437 1451759073241079421005789)
          ·
            refine ⟨544409652465404782877171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1451759073241079421005789 544409652465404782877171)
            ·
              refine ⟨816614478698107174315757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544409652465404782877171 816614478698107174315757)
              ·
                refine ⟨306230429511790190368409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 816614478698107174315757 306230429511790190368409)
                ·
                  refine ⟨229672822133842642776307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306230429511790190368409 229672822133842642776307)
                  ·
                    rfl

theorem cell20_503197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_503197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503197 prefixEnd_503197 := by exact prefixLift 503197
  have htrace : WordTrace (prefixWord ++ tailWord_503197) baseStart_503197 baseEnd_503197 := by
    simpa [prefixWord, tailWord_503197, baseEnd_503197] using wordTrace_append hprefix tailTrace_503197
  have hstable : (prefixWord ++ tailWord_503197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503197).length < 2 ^ (prefixWord ++ tailWord_503197).sum := by decide
  have hdescent : baseEnd_503197 < baseStart_503197 := by decide
  rcases family_descends (prefixWord ++ tailWord_503197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503228 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_503228 : Nat := 118140960795 + 503228 * 2 ^ 59
def prefixEnd_503228 : Nat := 4983230072969 + 3 ^ 40 * 503228 * 2
def baseEnd_503228 : Nat := 229686971378544312742847

theorem tailTrace_503228 : CollatzResearch.WordTrace tailWord_503228 prefixEnd_503228 229686971378544312742847 := by
  unfold tailWord_503228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177116510449187672559169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12236155347265583563412225 9177116510449187672559169)
  ·
    refine ⟨6882837382836890754419377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9177116510449187672559169 6882837382836890754419377)
    ·
      refine ⟨5162128037127668065814533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6882837382836890754419377 5162128037127668065814533)
      ·
        refine ⟨967899006961437762340225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5162128037127668065814533 967899006961437762340225)
        ·
          refine ⟨725924255221078321755169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967899006961437762340225 725924255221078321755169)
          ·
            refine ⟨544443191415808741316377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725924255221078321755169 544443191415808741316377)
            ·
              refine ⟨408332393561856555987283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544443191415808741316377 408332393561856555987283)
              ·
                refine ⟨612498590342784833980925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408332393561856555987283 612498590342784833980925)
                ·
                  refine ⟨229686971378544312742847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612498590342784833980925 229686971378544312742847)
                  ·
                    rfl

theorem cell20_503228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_503228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503228 prefixEnd_503228 := by exact prefixLift 503228
  have htrace : WordTrace (prefixWord ++ tailWord_503228) baseStart_503228 baseEnd_503228 := by
    simpa [prefixWord, tailWord_503228, baseEnd_503228] using wordTrace_append hprefix tailTrace_503228
  have hstable : (prefixWord ++ tailWord_503228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503228).length < 2 ^ (prefixWord ++ tailWord_503228).sum := by decide
  have hdescent : baseEnd_503228 < baseStart_503228 := by decide
  rcases family_descends (prefixWord ++ tailWord_503228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503232 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_503232 : Nat := 118140960795 + 503232 * 2 ^ 59
def prefixEnd_503232 : Nat := 4983230072969 + 3 ^ 40 * 503232 * 2
def baseEnd_503232 : Nat := 229688797087538076609497

theorem tailTrace_503232 : CollatzResearch.WordTrace tailWord_503232 prefixEnd_503232 229688797087538076609497 := by
  unfold tailWord_503232
  simp only [CollatzResearch.WordTrace]
  refine ⟨9177189456441942014131975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12236252608589256018842633 9177189456441942014131975)
  ·
    refine ⟨13765784184662913021197963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9177189456441942014131975 13765784184662913021197963)
    ·
      refine ⟨20648676276994369531796945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13765784184662913021197963 20648676276994369531796945)
      ·
        refine ⟨15486507207745777148847709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20648676276994369531796945 15486507207745777148847709)
        ·
          refine ⟨5807440202904666430817891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15486507207745777148847709 5807440202904666430817891)
          ·
            refine ⟨8711160304356999646226837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5807440202904666430817891 8711160304356999646226837)
            ·
              refine ⟨408335639266734358416883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8711160304356999646226837 408335639266734358416883)
              ·
                refine ⟨612503458900101537625325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408335639266734358416883 612503458900101537625325)
                ·
                  refine ⟨229688797087538076609497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612503458900101537625325 229688797087538076609497)
                  ·
                    rfl

theorem cell20_503232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_503232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503232 prefixEnd_503232 := by exact prefixLift 503232
  have htrace : WordTrace (prefixWord ++ tailWord_503232) baseStart_503232 baseEnd_503232 := by
    simpa [prefixWord, tailWord_503232, baseEnd_503232] using wordTrace_append hprefix tailTrace_503232
  have hstable : (prefixWord ++ tailWord_503232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503232).length < 2 ^ (prefixWord ++ tailWord_503232).sum := by decide
  have hdescent : baseEnd_503232 < baseStart_503232 := by decide
  rcases family_descends (prefixWord ++ tailWord_503232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503267 : List Nat := [1, 1, 1, 6, 2, 9]
def baseStart_503267 : Nat := 118140960795 + 503267 * 2 ^ 59
def prefixEnd_503267 : Nat := 4983230072969 + 3 ^ 40 * 503267 * 2
def baseEnd_503267 : Nat := 8507584149675315201581

theorem tailTrace_503267 : CollatzResearch.WordTrace tailWord_503267 prefixEnd_503267 8507584149675315201581 := by
  unfold tailWord_503267
  simp only [CollatzResearch.WordTrace]
  refine ⟨18355655467757085005788055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12237103645171390003858703 18355655467757085005788055)
  ·
    refine ⟨27533483201635627508682083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18355655467757085005788055 27533483201635627508682083)
    ·
      refine ⟨41300224802453441263023125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27533483201635627508682083 41300224802453441263023125)
      ·
        refine ⟨1935948037615005059204209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41300224802453441263023125 1935948037615005059204209)
        ·
          refine ⟨1451961028211253794403157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1935948037615005059204209 1451961028211253794403157)
          ·
            refine ⟨8507584149675315201581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1451961028211253794403157 8507584149675315201581)
            ·
              rfl

theorem cell20_503267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 9].length) (baseStart_503267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503267 prefixEnd_503267 := by exact prefixLift 503267
  have htrace : WordTrace (prefixWord ++ tailWord_503267) baseStart_503267 baseEnd_503267 := by
    simpa [prefixWord, tailWord_503267, baseEnd_503267] using wordTrace_append hprefix tailTrace_503267
  have hstable : (prefixWord ++ tailWord_503267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503267).length < 2 ^ (prefixWord ++ tailWord_503267).sum := by decide
  have hdescent : baseEnd_503267 < baseStart_503267 := by decide
  rcases family_descends (prefixWord ++ tailWord_503267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503315 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 2]
def baseStart_503315 : Nat := 118140960795 + 503315 * 2 ^ 59
def prefixEnd_503315 : Nat := 4983230072969 + 3 ^ 40 * 503315 * 2
def baseEnd_503315 : Nat := 229726680549158676842491

theorem tailTrace_503315 : CollatzResearch.WordTrace tailWord_503315 prefixEnd_503315 229726680549158676842491 := by
  unfold tailWord_503315
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357406171583189203535399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12238270781055459469023599 18357406171583189203535399)
  ·
    refine ⟨27536109257374783805303099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18357406171583189203535399 27536109257374783805303099)
    ·
      refine ⟨41304163886062175707954649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27536109257374783805303099 41304163886062175707954649)
      ·
        refine ⟨30978122914546631780965987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41304163886062175707954649 30978122914546631780965987)
        ·
          refine ⟨46467184371819947671448981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30978122914546631780965987 46467184371819947671448981)
          ·
            refine ⟨2178149267429060047099171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46467184371819947671448981 2178149267429060047099171)
            ·
              refine ⟨3267223901143590070648757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178149267429060047099171 3267223901143590070648757)
              ·
                refine ⟨306302240732211569123321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3267223901143590070648757 306302240732211569123321)
                ·
                  refine ⟨229726680549158676842491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306302240732211569123321 229726680549158676842491)
                  ·
                    rfl

theorem cell20_503315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 2].length) (baseStart_503315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503315 prefixEnd_503315 := by exact prefixLift 503315
  have htrace : WordTrace (prefixWord ++ tailWord_503315) baseStart_503315 baseEnd_503315 := by
    simpa [prefixWord, tailWord_503315, baseEnd_503315] using wordTrace_append hprefix tailTrace_503315
  have hstable : (prefixWord ++ tailWord_503315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503315).length < 2 ^ (prefixWord ++ tailWord_503315).sum := by decide
  have hdescent : baseEnd_503315 < baseStart_503315 := by decide
  rcases family_descends (prefixWord ++ tailWord_503315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503329 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_503329 : Nat := 118140960795 + 503329 * 2 ^ 59
def prefixEnd_503329 : Nat := 4983230072969 + 3 ^ 40 * 503329 * 2
def baseEnd_503329 : Nat := 229733070530636850375767

theorem tailTrace_503329 : CollatzResearch.WordTrace tailWord_503329 prefixEnd_503329 229733070530636850375767 := by
  unfold tailWord_503329
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357916793532469594545041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12238611195688313063030027 18357916793532469594545041)
  ·
    refine ⟨13768437595149352195908781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18357916793532469594545041 13768437595149352195908781)
    ·
      refine ⟨5163164098181007073465793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13768437595149352195908781 5163164098181007073465793)
      ·
        refine ⟨3872373073635755305099345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5163164098181007073465793 3872373073635755305099345)
        ·
          refine ⟨2904279805226816478824509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3872373073635755305099345 2904279805226816478824509)
          ·
            refine ⟨1089104926960056179559191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2904279805226816478824509 1089104926960056179559191)
            ·
              refine ⟨1633657390440084269338787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089104926960056179559191 1633657390440084269338787)
              ·
                refine ⟨2450486085660126404008181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633657390440084269338787 2450486085660126404008181)
                ·
                  refine ⟨229733070530636850375767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2450486085660126404008181 229733070530636850375767)
                  ·
                    rfl

theorem cell20_503329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_503329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503329 prefixEnd_503329 := by exact prefixLift 503329
  have htrace : WordTrace (prefixWord ++ tailWord_503329) baseStart_503329 baseEnd_503329 := by
    simpa [prefixWord, tailWord_503329, baseEnd_503329] using wordTrace_append hprefix tailTrace_503329
  have hstable : (prefixWord ++ tailWord_503329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503329).length < 2 ^ (prefixWord ++ tailWord_503329).sum := by decide
  have hdescent : baseEnd_503329 < baseStart_503329 := by decide
  rcases family_descends (prefixWord ++ tailWord_503329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503356 : List Nat := [2, 2, 2, 2, 5, 1, 2, 4]
def baseStart_503356 : Nat := 118140960795 + 503356 * 2 ^ 59
def prefixEnd_503356 : Nat := 4983230072969 + 3 ^ 40 * 503356 * 2
def baseEnd_503356 : Nat := 76581798022114918825219

theorem tailTrace_503356 : CollatzResearch.WordTrace tailWord_503356 prefixEnd_503356 76581798022114918825219 := by
  unfold tailWord_503356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179450782217326602888961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12239267709623102137185281 9179450782217326602888961)
  ·
    refine ⟨6884588086662994952166721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9179450782217326602888961 6884588086662994952166721)
    ·
      refine ⟨5163441064997246214125041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6884588086662994952166721 5163441064997246214125041)
      ·
        refine ⟨3872580798747934660593781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5163441064997246214125041 3872580798747934660593781)
        ·
          refine ⟨363054449882618874430667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3872580798747934660593781 363054449882618874430667)
          ·
            refine ⟨544581674823928311646001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363054449882618874430667 544581674823928311646001)
            ·
              refine ⟨408436256117946233734501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544581674823928311646001 408436256117946233734501)
              ·
                refine ⟨76581798022114918825219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408436256117946233734501 76581798022114918825219)
                ·
                  rfl

theorem cell20_503356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_503356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503356 prefixEnd_503356 := by exact prefixLift 503356
  have htrace : WordTrace (prefixWord ++ tailWord_503356) baseStart_503356 baseEnd_503356 := by
    simpa [prefixWord, tailWord_503356, baseEnd_503356] using wordTrace_append hprefix tailTrace_503356
  have hstable : (prefixWord ++ tailWord_503356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503356).length < 2 ^ (prefixWord ++ tailWord_503356).sum := by decide
  have hdescent : baseEnd_503356 < baseStart_503356 := by decide
  rcases family_descends (prefixWord ++ tailWord_503356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503429 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 2]
def baseStart_503429 : Nat := 118140960795 + 503429 * 2 ^ 59
def prefixEnd_503429 : Nat := 4983230072969 + 3 ^ 40 * 503429 * 2
def baseEnd_503429 : Nat := 229778713255480947042025

theorem tailTrace_503429 : CollatzResearch.WordTrace tailWord_503429 prefixEnd_503429 229778713255480947042025 := by
  unfold tailWord_503429
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361564093170186673185341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12241042728780124448790227 18361564093170186673185341)
  ·
    refine ⟨6885586534938820002444503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18361564093170186673185341 6885586534938820002444503)
    ·
      refine ⟨10328379802408230003666755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885586534938820002444503 10328379802408230003666755)
      ·
        refine ⟨15492569703612345005500133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10328379802408230003666755 15492569703612345005500133)
        ·
          refine ⟨2904856819427314688531275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15492569703612345005500133 2904856819427314688531275)
          ·
            refine ⟨4357285229140972032796913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904856819427314688531275 4357285229140972032796913)
            ·
              refine ⟨3267963921855729024597685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4357285229140972032796913 3267963921855729024597685)
              ·
                refine ⟨306371617673974596056033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3267963921855729024597685 306371617673974596056033)
                ·
                  refine ⟨229778713255480947042025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306371617673974596056033 229778713255480947042025)
                  ·
                    rfl

theorem cell20_503429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_503429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503429 prefixEnd_503429 := by exact prefixLift 503429
  have htrace : WordTrace (prefixWord ++ tailWord_503429) baseStart_503429 baseEnd_503429 := by
    simpa [prefixWord, tailWord_503429, baseEnd_503429] using wordTrace_append hprefix tailTrace_503429
  have hstable : (prefixWord ++ tailWord_503429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503429).length < 2 ^ (prefixWord ++ tailWord_503429).sum := by decide
  have hdescent : baseEnd_503429 < baseStart_503429 := by decide
  rcases family_descends (prefixWord ++ tailWord_503429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503442 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_503442 : Nat := 118140960795 + 503442 * 2 ^ 59
def prefixEnd_503442 : Nat := 4983230072969 + 3 ^ 40 * 503442 * 2
def baseEnd_503442 : Nat := 229784646809710679608639

theorem tailTrace_503442 : CollatzResearch.WordTrace tailWord_503442 prefixEnd_503442 229784646809710679608639 := by
  unfold tailWord_503442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590509560530772473352145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12241358828082059928939053 4590509560530772473352145)
  ·
    refine ⟨3442882170398079355014109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4590509560530772473352145 3442882170398079355014109)
    ·
      refine ⟨1291080813899279758130291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3442882170398079355014109 1291080813899279758130291)
      ·
        refine ⟨1936621220848919637195437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291080813899279758130291 1936621220848919637195437)
        ·
          refine ⟨726232957818344863948289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1936621220848919637195437 726232957818344863948289)
          ·
            refine ⟨544674718363758647961217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726232957818344863948289 544674718363758647961217)
            ·
              refine ⟨408506038772818985970913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544674718363758647961217 408506038772818985970913)
              ·
                refine ⟨306379529079614239478185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408506038772818985970913 306379529079614239478185)
                ·
                  refine ⟨229784646809710679608639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306379529079614239478185 229784646809710679608639)
                  ·
                    rfl

theorem cell20_503442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_503442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503442 prefixEnd_503442 := by exact prefixLift 503442
  have htrace : WordTrace (prefixWord ++ tailWord_503442) baseStart_503442 baseEnd_503442 := by
    simpa [prefixWord, tailWord_503442, baseEnd_503442] using wordTrace_append hprefix tailTrace_503442
  have hstable : (prefixWord ++ tailWord_503442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503442).length < 2 ^ (prefixWord ++ tailWord_503442).sum := by decide
  have hdescent : baseEnd_503442 < baseStart_503442 := by decide
  rcases family_descends (prefixWord ++ tailWord_503442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503470 : List Nat := [4, 1, 4, 1, 2, 1, 3, 4]
def baseStart_503470 : Nat := 118140960795 + 503470 * 2 ^ 59
def prefixEnd_503470 : Nat := 4983230072969 + 3 ^ 40 * 503470 * 2
def baseEnd_503470 : Nat := 76599142257555675558397

theorem tailTrace_503470 : CollatzResearch.WordTrace tailWord_503470 prefixEnd_503470 76599142257555675558397 := by
  unfold tailWord_503470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295382435752706334428483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12242039657347767116951909 2295382435752706334428483)
  ·
    refine ⟨3443073653629059501642725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2295382435752706334428483 3443073653629059501642725)
    ·
      refine ⟨645576310055448656558011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3443073653629059501642725 645576310055448656558011)
      ·
        refine ⟨968364465083172984837017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645576310055448656558011 968364465083172984837017)
        ·
          refine ⟨726273348812379738627763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968364465083172984837017 726273348812379738627763)
          ·
            refine ⟨1089410023218569607941645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726273348812379738627763 1089410023218569607941645)
            ·
              refine ⟨408528758706963602978117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1089410023218569607941645 408528758706963602978117)
              ·
                refine ⟨76599142257555675558397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408528758706963602978117 76599142257555675558397)
                ·
                  rfl

theorem cell20_503470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_503470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503470 prefixEnd_503470 := by exact prefixLift 503470
  have htrace : WordTrace (prefixWord ++ tailWord_503470) baseStart_503470 baseEnd_503470 := by
    simpa [prefixWord, tailWord_503470, baseEnd_503470] using wordTrace_append hprefix tailTrace_503470
  have hstable : (prefixWord ++ tailWord_503470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503470).length < 2 ^ (prefixWord ++ tailWord_503470).sum := by decide
  have hdescent : baseEnd_503470 < baseStart_503470 := by decide
  rcases family_descends (prefixWord ++ tailWord_503470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503484 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 2]
def baseStart_503484 : Nat := 118140960795 + 503484 * 2 ^ 59
def prefixEnd_503484 : Nat := 4983230072969 + 3 ^ 40 * 503484 * 2
def baseEnd_503484 : Nat := 229803816754145200208467

theorem tailTrace_503484 : CollatzResearch.WordTrace tailWord_503484 prefixEnd_503484 229803816754145200208467 := by
  unfold tailWord_503484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181785053985465533218753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12242380071980620710958337 9181785053985465533218753)
  ·
    refine ⟨6886338790489099149914065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9181785053985465533218753 6886338790489099149914065)
    ·
      refine ⟨5164754092866824362435549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6886338790489099149914065 5164754092866824362435549)
      ·
        refine ⟨1936782784825059135913331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5164754092866824362435549 1936782784825059135913331)
        ·
          refine ⟨2905174177237588703869997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936782784825059135913331 2905174177237588703869997)
          ·
            refine ⟨1089440316464095763951249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2905174177237588703869997 1089440316464095763951249)
            ·
              refine ⟨817080237348071822963437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089440316464095763951249 817080237348071822963437)
              ·
                refine ⟨306405089005526933611289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 817080237348071822963437 306405089005526933611289)
                ·
                  refine ⟨229803816754145200208467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306405089005526933611289 229803816754145200208467)
                  ·
                    rfl

theorem cell20_503484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_503484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503484 prefixEnd_503484 := by exact prefixLift 503484
  have htrace : WordTrace (prefixWord ++ tailWord_503484) baseStart_503484 baseEnd_503484 := by
    simpa [prefixWord, tailWord_503484, baseEnd_503484] using wordTrace_append hprefix tailTrace_503484
  have hstable : (prefixWord ++ tailWord_503484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503484).length < 2 ^ (prefixWord ++ tailWord_503484).sum := by decide
  have hdescent : baseEnd_503484 < baseStart_503484 := by decide
  rcases family_descends (prefixWord ++ tailWord_503484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503490 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_503490 : Nat := 118140960795 + 503490 * 2 ^ 59
def prefixEnd_503490 : Nat := 4983230072969 + 3 ^ 40 * 503490 * 2
def baseEnd_503490 : Nat := 229806555317635846008443

theorem tailTrace_503490 : CollatzResearch.WordTrace tailWord_503490 prefixEnd_503490 229806555317635846008443 := by
  unfold tailWord_503490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590947236487298522788981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12242525963966129394103949 4590947236487298522788981)
  ·
    refine ⟨430401303420684236511467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4590947236487298522788981 430401303420684236511467)
    ·
      refine ⟨645601955131026354767201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430401303420684236511467 645601955131026354767201)
      ·
        refine ⟨484201466348269766075401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 645601955131026354767201 484201466348269766075401)
        ·
          refine ⟨363151099761202324556551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484201466348269766075401 363151099761202324556551)
          ·
            refine ⟨544726649641803486834827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363151099761202324556551 544726649641803486834827)
            ·
              refine ⟨817089974462705230252241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544726649641803486834827 817089974462705230252241)
              ·
                refine ⟨612817480847028922689181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817089974462705230252241 612817480847028922689181)
                ·
                  refine ⟨229806555317635846008443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612817480847028922689181 229806555317635846008443)
                  ·
                    rfl

theorem cell20_503490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_503490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503490 prefixEnd_503490 := by exact prefixLift 503490
  have htrace : WordTrace (prefixWord ++ tailWord_503490) baseStart_503490 baseEnd_503490 := by
    simpa [prefixWord, tailWord_503490, baseEnd_503490] using wordTrace_append hprefix tailTrace_503490
  have hstable : (prefixWord ++ tailWord_503490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503490).length < 2 ^ (prefixWord ++ tailWord_503490).sum := by decide
  have hdescent : baseEnd_503490 < baseStart_503490 := by decide
  rcases family_descends (prefixWord ++ tailWord_503490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503494 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_503494 : Nat := 118140960795 + 503494 * 2 ^ 59
def prefixEnd_503494 : Nat := 4983230072969 + 3 ^ 40 * 503494 * 2
def baseEnd_503494 : Nat := 229808381026629609875093

theorem tailTrace_503494 : CollatzResearch.WordTrace tailWord_503494 prefixEnd_503494 229808381026629609875093 := by
  unfold tailWord_503494
  simp only [CollatzResearch.WordTrace]
  refine ⟨573872963685459461696923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12242623225289801849534357 573872963685459461696923)
  ·
    refine ⟨860809445528189192545385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 573872963685459461696923 860809445528189192545385)
    ·
      refine ⟨645607084146141894409039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 860809445528189192545385 645607084146141894409039)
      ·
        refine ⟨968410626219212841613559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645607084146141894409039 968410626219212841613559)
        ·
          refine ⟨1452615939328819262420339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968410626219212841613559 1452615939328819262420339)
          ·
            refine ⟨2178923908993228893630509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452615939328819262420339 2178923908993228893630509)
            ·
              refine ⟨817096465872460835111441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2178923908993228893630509 817096465872460835111441)
              ·
                refine ⟨612822349404345626333581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817096465872460835111441 612822349404345626333581)
                ·
                  refine ⟨229808381026629609875093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612822349404345626333581 229808381026629609875093)
                  ·
                    rfl

theorem cell20_503494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_503494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503494 prefixEnd_503494 := by exact prefixLift 503494
  have htrace : WordTrace (prefixWord ++ tailWord_503494) baseStart_503494 baseEnd_503494 := by
    simpa [prefixWord, tailWord_503494, baseEnd_503494] using wordTrace_append hprefix tailTrace_503494
  have hstable : (prefixWord ++ tailWord_503494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503494).length < 2 ^ (prefixWord ++ tailWord_503494).sum := by decide
  have hdescent : baseEnd_503494 < baseStart_503494 := by decide
  rcases family_descends (prefixWord ++ tailWord_503494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503501 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 2]
def baseStart_503501 : Nat := 118140960795 + 503501 * 2 ^ 59
def prefixEnd_503501 : Nat := 4983230072969 + 3 ^ 40 * 503501 * 2
def baseEnd_503501 : Nat := 229811576017368696641731

theorem tailTrace_503501 : CollatzResearch.WordTrace tailWord_503501 prefixEnd_503501 229811576017368696641731 := by
  unfold tailWord_503501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364190148909342969806357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12242793432606228646537571 18364190148909342969806357)
  ·
    refine ⟨860821413230125451709673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18364190148909342969806357 860821413230125451709673)
    ·
      refine ⟨645616059922594088782255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 860821413230125451709673 645616059922594088782255)
      ·
        refine ⟨968424089883891133173383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645616059922594088782255 968424089883891133173383)
        ·
          refine ⟨1452636134825836699760075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968424089883891133173383 1452636134825836699760075)
          ·
            refine ⟨2178954202238755049640113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452636134825836699760075 2178954202238755049640113)
            ·
              refine ⟨1634215651679066287230085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178954202238755049640113 1634215651679066287230085)
              ·
                refine ⟨306415434689824928855641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1634215651679066287230085 306415434689824928855641)
                ·
                  refine ⟨229811576017368696641731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306415434689824928855641 229811576017368696641731)
                  ·
                    rfl

theorem cell20_503501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_503501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503501 prefixEnd_503501 := by exact prefixLift 503501
  have htrace : WordTrace (prefixWord ++ tailWord_503501) baseStart_503501 baseEnd_503501 := by
    simpa [prefixWord, tailWord_503501, baseEnd_503501] using wordTrace_append hprefix tailTrace_503501
  have hstable : (prefixWord ++ tailWord_503501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503501).length < 2 ^ (prefixWord ++ tailWord_503501).sum := by decide
  have hdescent : baseEnd_503501 < baseStart_503501 := by decide
  rcases family_descends (prefixWord ++ tailWord_503501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503505 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 2]
def baseStart_503505 : Nat := 118140960795 + 503505 * 2 ^ 59
def prefixEnd_503505 : Nat := 4983230072969 + 3 ^ 40 * 503505 * 2
def baseEnd_503505 : Nat := 229813401726362460508381

theorem tailTrace_503505 : CollatzResearch.WordTrace tailWord_503505 prefixEnd_503505 229813401726362460508381 := by
  unfold tailWord_503505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364336040894851652951969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12242890693929901101967979 18364336040894851652951969)
  ·
    refine ⟨13773252030671138739713977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18364336040894851652951969 13773252030671138739713977)
    ·
      refine ⟨10329939023003354054785483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13773252030671138739713977 10329939023003354054785483)
      ·
        refine ⟨15494908534505031082178225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329939023003354054785483 15494908534505031082178225)
        ·
          refine ⟨11621181400878773311633669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15494908534505031082178225 11621181400878773311633669)
          ·
            refine ⟨2178971512664769995931313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11621181400878773311633669 2178971512664769995931313)
            ·
              refine ⟨1634228634498577496948485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178971512664769995931313 1634228634498577496948485)
              ·
                refine ⟨306417868968483280677841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1634228634498577496948485 306417868968483280677841)
                ·
                  refine ⟨229813401726362460508381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306417868968483280677841 229813401726362460508381)
                  ·
                    rfl

theorem cell20_503505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_503505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503505 prefixEnd_503505 := by exact prefixLift 503505
  have htrace : WordTrace (prefixWord ++ tailWord_503505) baseStart_503505 baseEnd_503505 := by
    simpa [prefixWord, tailWord_503505, baseEnd_503505] using wordTrace_append hprefix tailTrace_503505
  have hstable : (prefixWord ++ tailWord_503505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503505).length < 2 ^ (prefixWord ++ tailWord_503505).sum := by decide
  have hdescent : baseEnd_503505 < baseStart_503505 := by decide
  rcases family_descends (prefixWord ++ tailWord_503505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503543 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 2]
def baseStart_503543 : Nat := 118140960795 + 503543 * 2 ^ 59
def prefixEnd_503543 : Nat := 4983230072969 + 3 ^ 40 * 503543 * 2
def baseEnd_503543 : Nat := 229830745961803217241559

theorem tailTrace_503543 : CollatzResearch.WordTrace tailWord_503543 prefixEnd_503543 229830745961803217241559 := by
  unfold tailWord_503543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18365722014757184142835283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12243814676504789428556855 18365722014757184142835283)
  ·
    refine ⟨27548583022135776214252925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18365722014757184142835283 27548583022135776214252925)
    ·
      refine ⟨10330718633300916080344847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27548583022135776214252925 10330718633300916080344847)
      ·
        refine ⟨15496077949951374120517271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330718633300916080344847 15496077949951374120517271)
        ·
          refine ⟨23244116924927061180775907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15496077949951374120517271 23244116924927061180775907)
          ·
            refine ⟨34866175387390591771163861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23244116924927061180775907 34866175387390591771163861)
            ·
              refine ⟨817175985641966994636653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34866175387390591771163861 817175985641966994636653)
              ·
                refine ⟨306440994615737622988745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 817175985641966994636653 306440994615737622988745)
                ·
                  refine ⟨229830745961803217241559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306440994615737622988745 229830745961803217241559)
                  ·
                    rfl

theorem cell20_503543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 2].length) (baseStart_503543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503543 prefixEnd_503543 := by exact prefixLift 503543
  have htrace : WordTrace (prefixWord ++ tailWord_503543) baseStart_503543 baseEnd_503543 := by
    simpa [prefixWord, tailWord_503543, baseEnd_503543] using wordTrace_append hprefix tailTrace_503543
  have hstable : (prefixWord ++ tailWord_503543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503543).length < 2 ^ (prefixWord ++ tailWord_503543).sum := by decide
  have hdescent : baseEnd_503543 < baseStart_503543 := by decide
  rcases family_descends (prefixWord ++ tailWord_503543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503560 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 2]
def baseStart_503560 : Nat := 118140960795 + 503560 * 2 ^ 59
def prefixEnd_503560 : Nat := 4983230072969 + 3 ^ 40 * 503560 * 2
def baseEnd_503560 : Nat := 229838505225026713674823

theorem tailTrace_503560 : CollatzResearch.WordTrace tailWord_503560 prefixEnd_503560 229838505225026713674823 := by
  unfold tailWord_503560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183171027847798023102067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12244228037130397364136089 9183171027847798023102067)
  ·
    refine ⟨13774756541771697034653101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9183171027847798023102067 13774756541771697034653101)
    ·
      refine ⟨5165533703164386387994913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13774756541771697034653101 5165533703164386387994913)
      ·
        refine ⟨3874150277373289790996185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5165533703164386387994913 3874150277373289790996185)
        ·
          refine ⟨2905612708029967343247139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3874150277373289790996185 2905612708029967343247139)
          ·
            refine ⟨4358419062044951014870709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905612708029967343247139 4358419062044951014870709)
            ·
              refine ⟨408601787066714157644129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4358419062044951014870709 408601787066714157644129)
              ·
                refine ⟨306451340300035618233097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408601787066714157644129 306451340300035618233097)
                ·
                  refine ⟨229838505225026713674823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306451340300035618233097 229838505225026713674823)
                  ·
                    rfl

theorem cell20_503560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_503560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503560 prefixEnd_503560 := by exact prefixLift 503560
  have htrace : WordTrace (prefixWord ++ tailWord_503560) baseStart_503560 baseEnd_503560 := by
    simpa [prefixWord, tailWord_503560, baseEnd_503560] using wordTrace_append hprefix tailTrace_503560
  have hstable : (prefixWord ++ tailWord_503560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503560).length < 2 ^ (prefixWord ++ tailWord_503560).sum := by decide
  have hdescent : baseEnd_503560 < baseStart_503560 := by decide
  rcases family_descends (prefixWord ++ tailWord_503560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503564 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_503564 : Nat := 118140960795 + 503564 * 2 ^ 59
def prefixEnd_503564 : Nat := 4983230072969 + 3 ^ 40 * 503564 * 2
def baseEnd_503564 : Nat := 229840330934020477541473

theorem tailTrace_503564 : CollatzResearch.WordTrace tailWord_503564 prefixEnd_503564 229840330934020477541473 := by
  unfold tailWord_503564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183243973840552364674873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12244325298454069819566497 9183243973840552364674873)
  ·
    refine ⟨6887432980380414273506155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9183243973840552364674873 6887432980380414273506155)
    ·
      refine ⟨10331149470570621410259233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887432980380414273506155 10331149470570621410259233)
      ·
        refine ⟨7748362102927966057694425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10331149470570621410259233 7748362102927966057694425)
        ·
          refine ⟨5811271577195974543270819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7748362102927966057694425 5811271577195974543270819)
          ·
            refine ⟨8716907365793961814906229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811271577195974543270819 8716907365793961814906229)
            ·
              refine ⟨817210065543183920147459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8716907365793961814906229 817210065543183920147459)
              ·
                refine ⟨1225815098314775880221189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817210065543183920147459 1225815098314775880221189)
                ·
                  refine ⟨229840330934020477541473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1225815098314775880221189 229840330934020477541473)
                  ·
                    rfl

theorem cell20_503564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_503564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503564 prefixEnd_503564 := by exact prefixLift 503564
  have htrace : WordTrace (prefixWord ++ tailWord_503564) baseStart_503564 baseEnd_503564 := by
    simpa [prefixWord, tailWord_503564, baseEnd_503564] using wordTrace_append hprefix tailTrace_503564
  have hstable : (prefixWord ++ tailWord_503564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503564).length < 2 ^ (prefixWord ++ tailWord_503564).sum := by decide
  have hdescent : baseEnd_503564 < baseStart_503564 := by decide
  rcases family_descends (prefixWord ++ tailWord_503564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503570 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_503570 : Nat := 118140960795 + 503570 * 2 ^ 59
def prefixEnd_503570 : Nat := 4983230072969 + 3 ^ 40 * 503570 * 2
def baseEnd_503570 : Nat := 229843069497511123341449

theorem tailTrace_503570 : CollatzResearch.WordTrace tailWord_503570 prefixEnd_503570 229843069497511123341449 := by
  unfold tailWord_503570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591676696414841938517041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12244471190439578502712109 4591676696414841938517041)
  ·
    refine ⟨3443757522311131453887781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4591676696414841938517041 3443757522311131453887781)
    ·
      refine ⟨645704535433337147603959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3443757522311131453887781 645704535433337147603959)
      ·
        refine ⟨968556803150005721405939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645704535433337147603959 968556803150005721405939)
        ·
          refine ⟨1452835204725008582108909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968556803150005721405939 1452835204725008582108909)
          ·
            refine ⟨544813201771878218290841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1452835204725008582108909 544813201771878218290841)
            ·
              refine ⟨408609901328908663718131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544813201771878218290841 408609901328908663718131)
              ·
                refine ⟨612914851993362995577197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408609901328908663718131 612914851993362995577197)
                ·
                  refine ⟨229843069497511123341449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612914851993362995577197 229843069497511123341449)
                  ·
                    rfl

theorem cell20_503570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_503570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503570 prefixEnd_503570 := by exact prefixLift 503570
  have htrace : WordTrace (prefixWord ++ tailWord_503570) baseStart_503570 baseEnd_503570 := by
    simpa [prefixWord, tailWord_503570, baseEnd_503570] using wordTrace_append hprefix tailTrace_503570
  have hstable : (prefixWord ++ tailWord_503570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503570).length < 2 ^ (prefixWord ++ tailWord_503570).sum := by decide
  have hdescent : baseEnd_503570 < baseStart_503570 := by decide
  rcases family_descends (prefixWord ++ tailWord_503570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503609 : List Nat := [1, 2, 1, 7, 9]
def baseStart_503609 : Nat := 118140960795 + 503609 * 2 ^ 59
def prefixEnd_503609 : Nat := 4983230072969 + 3 ^ 40 * 503609 * 2
def baseEnd_503609 : Nat := 2837788520496300259769

theorem tailTrace_503609 : CollatzResearch.WordTrace tailWord_503609 prefixEnd_503609 2837788520496300259769 := by
  unfold tailWord_503609
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368129232518077414737881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12245419488345384943158587 18368129232518077414737881)
  ·
    refine ⟨13776096924388558061053411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18368129232518077414737881 13776096924388558061053411)
    ·
      refine ⟨20664145386582837091580117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13776096924388558061053411 20664145386582837091580117)
      ·
        refine ⟨484315907498035244333909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20664145386582837091580117 484315907498035244333909)
        ·
          refine ⟨2837788520496300259769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 484315907498035244333909 2837788520496300259769)
          ·
            rfl

theorem cell20_503609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 9].length) (baseStart_503609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503609 prefixEnd_503609 := by exact prefixLift 503609
  have htrace : WordTrace (prefixWord ++ tailWord_503609) baseStart_503609 baseEnd_503609 := by
    simpa [prefixWord, tailWord_503609, baseEnd_503609] using wordTrace_append hprefix tailTrace_503609
  have hstable : (prefixWord ++ tailWord_503609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503609).length < 2 ^ (prefixWord ++ tailWord_503609).sum := by decide
  have hdescent : baseEnd_503609 < baseStart_503609 := by decide
  rcases family_descends (prefixWord ++ tailWord_503609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503615 : List Nat := [1, 1, 2, 2, 6, 2, 2, 2, 2]
def baseStart_503615 : Nat := 118140960795 + 503615 * 2 ^ 59
def prefixEnd_503615 : Nat := 4983230072969 + 3 ^ 40 * 503615 * 2
def baseEnd_503615 : Nat := 229863608723690966841265

theorem tailTrace_503615 : CollatzResearch.WordTrace tailWord_503615 prefixEnd_503615 229863608723690966841265 := by
  unfold tailWord_503615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368348070496340439456299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12245565380330893626304199 18368348070496340439456299)
  ·
    refine ⟨27552522105744510659184449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18368348070496340439456299 27552522105744510659184449)
    ·
      refine ⟨20664391579308382994388337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27552522105744510659184449 20664391579308382994388337)
      ·
        refine ⟨15498293684481287245791253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20664391579308382994388337 15498293684481287245791253)
        ·
          refine ⟨726482516460060339646465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15498293684481287245791253 726482516460060339646465)
          ·
            refine ⟨544861887345045254734849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726482516460060339646465 544861887345045254734849)
            ·
              refine ⟨408646415508783941051137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544861887345045254734849 408646415508783941051137)
              ·
                refine ⟨306484811631587955788353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408646415508783941051137 306484811631587955788353)
                ·
                  refine ⟨229863608723690966841265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306484811631587955788353 229863608723690966841265)
                  ·
                    rfl

theorem cell20_503615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 2].length) (baseStart_503615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503615 prefixEnd_503615 := by exact prefixLift 503615
  have htrace : WordTrace (prefixWord ++ tailWord_503615) baseStart_503615 baseEnd_503615 := by
    simpa [prefixWord, tailWord_503615, baseEnd_503615] using wordTrace_append hprefix tailTrace_503615
  have hstable : (prefixWord ++ tailWord_503615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503615).length < 2 ^ (prefixWord ++ tailWord_503615).sum := by decide
  have hdescent : baseEnd_503615 < baseStart_503615 := by decide
  rcases family_descends (prefixWord ++ tailWord_503615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503619 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 2]
def baseStart_503619 : Nat := 118140960795 + 503619 * 2 ^ 59
def prefixEnd_503619 : Nat := 4983230072969 + 3 ^ 40 * 503619 * 2
def baseEnd_503619 : Nat := 229865434432684730707915

theorem tailTrace_503619 : CollatzResearch.WordTrace tailWord_503619 prefixEnd_503619 229865434432684730707915 := by
  unfold tailWord_503619
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368493962481849122601911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12245662641654566081734607 18368493962481849122601911)
  ·
    refine ⟨27552740943722773683902867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18368493962481849122601911 27552740943722773683902867)
    ·
      refine ⟨41329111415584160525854301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552740943722773683902867 41329111415584160525854301)
      ·
        refine ⟨15498416780844060197195363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41329111415584160525854301 15498416780844060197195363)
        ·
          refine ⟨23247625171266090295793045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15498416780844060197195363 23247625171266090295793045)
          ·
            refine ⟨1089732429903097982615299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23247625171266090295793045 1089732429903097982615299)
            ·
              refine ⟨1634598644854646973922949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089732429903097982615299 1634598644854646973922949)
              ·
                refine ⟨306487245910246307610553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1634598644854646973922949 306487245910246307610553)
                ·
                  refine ⟨229865434432684730707915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306487245910246307610553 229865434432684730707915)
                  ·
                    rfl

theorem cell20_503619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 2].length) (baseStart_503619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503619 prefixEnd_503619 := by exact prefixLift 503619
  have htrace : WordTrace (prefixWord ++ tailWord_503619) baseStart_503619 baseEnd_503619 := by
    simpa [prefixWord, tailWord_503619, baseEnd_503619] using wordTrace_append hprefix tailTrace_503619
  have hstable : (prefixWord ++ tailWord_503619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503619).length < 2 ^ (prefixWord ++ tailWord_503619).sum := by decide
  have hdescent : baseEnd_503619 < baseStart_503619 := by decide
  rcases family_descends (prefixWord ++ tailWord_503619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503622 : List Nat := [6, 1, 1, 2, 1, 3, 1, 5]
def baseStart_503622 : Nat := 118140960795 + 503622 * 2 ^ 59
def prefixEnd_503622 : Nat := 4983230072969 + 3 ^ 40 * 503622 * 2
def baseEnd_503622 : Nat := 76622267904810017869301

theorem tailTrace_503622 : CollatzResearch.WordTrace tailWord_503622 prefixEnd_503622 76622267904810017869301 := by
  unfold tailWord_503622
  simp only [CollatzResearch.WordTrace]
  refine ⟨574018855670968144842535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12245735587647320423307413 574018855670968144842535)
  ·
    refine ⟨861028283506452217263803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574018855670968144842535 861028283506452217263803)
    ·
      refine ⟨1291542425259678325895705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861028283506452217263803 1291542425259678325895705)
      ·
        refine ⟨968656818944758744421779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1291542425259678325895705 968656818944758744421779)
        ·
          refine ⟨1452985228417138116632669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968656818944758744421779 1452985228417138116632669)
          ·
            refine ⟨544869460656426793737251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1452985228417138116632669 544869460656426793737251)
            ·
              refine ⟨817304190984640190605877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544869460656426793737251 817304190984640190605877)
              ·
                refine ⟨76622267904810017869301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 817304190984640190605877 76622267904810017869301)
                ·
                  rfl

theorem cell20_503622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_503622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503622 prefixEnd_503622 := by exact prefixLift 503622
  have htrace : WordTrace (prefixWord ++ tailWord_503622) baseStart_503622 baseEnd_503622 := by
    simpa [prefixWord, tailWord_503622, baseEnd_503622] using wordTrace_append hprefix tailTrace_503622
  have hstable : (prefixWord ++ tailWord_503622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503622).length < 2 ^ (prefixWord ++ tailWord_503622).sum := by decide
  have hdescent : baseEnd_503622 < baseStart_503622 := by decide
  rcases family_descends (prefixWord ++ tailWord_503622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503633 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_503633 : Nat := 118140960795 + 503633 * 2 ^ 59
def prefixEnd_503633 : Nat := 4983230072969 + 3 ^ 40 * 503633 * 2
def baseEnd_503633 : Nat := 229871824414162904241191

theorem tailTrace_503633 : CollatzResearch.WordTrace tailWord_503633 prefixEnd_503633 229871824414162904241191 := by
  unfold tailWord_503633
  simp only [CollatzResearch.WordTrace]
  refine ⟨18369004584431129513611553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12246003056287419675741035 18369004584431129513611553)
  ·
    refine ⟨13776753438323347135208665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18369004584431129513611553 13776753438323347135208665)
    ·
      refine ⟨10332565078742510351406499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13776753438323347135208665 10332565078742510351406499)
      ·
        refine ⟨15498847618113765527109749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10332565078742510351406499 15498847618113765527109749)
        ·
          refine ⟨1453016964198165518166539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15498847618113765527109749 1453016964198165518166539)
          ·
            refine ⟨2179525446297248277249809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453016964198165518166539 2179525446297248277249809)
            ·
              refine ⟨1634644084722936207937357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179525446297248277249809 1634644084722936207937357)
              ·
                refine ⟨612991531771101077976509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1634644084722936207937357 612991531771101077976509)
                ·
                  refine ⟨229871824414162904241191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612991531771101077976509 229871824414162904241191)
                  ·
                    rfl

theorem cell20_503633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_503633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503633 prefixEnd_503633 := by exact prefixLift 503633
  have htrace : WordTrace (prefixWord ++ tailWord_503633) baseStart_503633 baseEnd_503633 := by
    simpa [prefixWord, tailWord_503633, baseEnd_503633] using wordTrace_append hprefix tailTrace_503633
  have hstable : (prefixWord ++ tailWord_503633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503633).length < 2 ^ (prefixWord ++ tailWord_503633).sum := by decide
  have hdescent : baseEnd_503633 < baseStart_503633 := by decide
  rcases family_descends (prefixWord ++ tailWord_503633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503733 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 4]
def baseStart_503733 : Nat := 118140960795 + 503733 * 2 ^ 59
def prefixEnd_503733 : Nat := 4983230072969 + 3 ^ 40 * 503733 * 2
def baseEnd_503733 : Nat := 229917467139007000907449

theorem tailTrace_503733 : CollatzResearch.WordTrace tailWord_503733 prefixEnd_503733 229917467139007000907449 := by
  unfold tailWord_503733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372651884068846592251853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12248434589379231061501235 18372651884068846592251853)
  ·
    refine ⟨6889744456525817472094445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18372651884068846592251853 6889744456525817472094445)
    ·
      refine ⟨2583654171197181552035417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6889744456525817472094445 2583654171197181552035417)
      ·
        refine ⟨1937740628397886164026563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2583654171197181552035417 1937740628397886164026563)
        ·
          refine ⟨2906610942596829246039845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937740628397886164026563 2906610942596829246039845)
          ·
            refine ⟨544989551736905483632471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2906610942596829246039845 544989551736905483632471)
            ·
              refine ⟨817484327605358225448707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544989551736905483632471 817484327605358225448707)
              ·
                refine ⟨1226226491408037338173061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817484327605358225448707 1226226491408037338173061)
                ·
                  refine ⟨229917467139007000907449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226226491408037338173061 229917467139007000907449)
                  ·
                    rfl

theorem cell20_503733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_503733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503733 prefixEnd_503733 := by exact prefixLift 503733
  have htrace : WordTrace (prefixWord ++ tailWord_503733) baseStart_503733 baseEnd_503733 := by
    simpa [prefixWord, tailWord_503733, baseEnd_503733] using wordTrace_append hprefix tailTrace_503733
  have hstable : (prefixWord ++ tailWord_503733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503733).length < 2 ^ (prefixWord ++ tailWord_503733).sum := by decide
  have hdescent : baseEnd_503733 < baseStart_503733 := by decide
  rcases family_descends (prefixWord ++ tailWord_503733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503778 : List Nat := [3, 3, 3, 1, 2, 8]
def baseStart_503778 : Nat := 118140960795 + 503778 * 2 ^ 59
def prefixEnd_503778 : Nat := 4983230072969 + 3 ^ 40 * 503778 * 2
def baseEnd_503778 : Nat := 8516222457969883126195

theorem tailTrace_503778 : CollatzResearch.WordTrace tailWord_503778 prefixEnd_503778 8516222457969883126195 := by
  unfold tailWord_503778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4593573292226454819409997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12249528779270546185093325 4593573292226454819409997)
  ·
    refine ⟨1722589984584920557278749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4593573292226454819409997 1722589984584920557278749)
    ·
      refine ⟨645971244219345208979531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1722589984584920557278749 645971244219345208979531)
      ·
        refine ⟨968956866329017813469297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645971244219345208979531 968956866329017813469297)
        ·
          refine ⟨726717649746763360101973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968956866329017813469297 726717649746763360101973)
          ·
            refine ⟨8516222457969883126195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 726717649746763360101973 8516222457969883126195)
            ·
              rfl

theorem cell20_503778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 8].length) (baseStart_503778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503778 prefixEnd_503778 := by exact prefixLift 503778
  have htrace : WordTrace (prefixWord ++ tailWord_503778) baseStart_503778 baseEnd_503778 := by
    simpa [prefixWord, tailWord_503778, baseEnd_503778] using wordTrace_append hprefix tailTrace_503778
  have hstable : (prefixWord ++ tailWord_503778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503778).length < 2 ^ (prefixWord ++ tailWord_503778).sum := by decide
  have hdescent : baseEnd_503778 < baseStart_503778 := by decide
  rcases family_descends (prefixWord ++ tailWord_503778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503813 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_503813 : Nat := 118140960795 + 503813 * 2 ^ 59
def prefixEnd_503813 : Nat := 4983230072969 + 3 ^ 40 * 503813 * 2
def baseEnd_503813 : Nat := 229953981318882278240455

theorem tailTrace_503813 : CollatzResearch.WordTrace tailWord_503813 prefixEnd_503813 229953981318882278240455 := by
  unfold tailWord_503813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375569723779020255164093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12250379815852680170109395 18375569723779020255164093)
  ·
    refine ⟨6890838646417132595686535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18375569723779020255164093 6890838646417132595686535)
    ·
      refine ⟨10336257969625698893529803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6890838646417132595686535 10336257969625698893529803)
      ·
        refine ⟨15504386954438548340294705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10336257969625698893529803 15504386954438548340294705)
        ·
          refine ⟨11628290215828911255221029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15504386954438548340294705 11628290215828911255221029)
          ·
            refine ⟨2180304415467920860353943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11628290215828911255221029 2180304415467920860353943)
            ·
              refine ⟨3270456623201881290530915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180304415467920860353943 3270456623201881290530915)
              ·
                refine ⟨4905684934802821935796373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270456623201881290530915 4905684934802821935796373)
                ·
                  refine ⟨229953981318882278240455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4905684934802821935796373 229953981318882278240455)
                  ·
                    rfl

theorem cell20_503813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_503813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503813 prefixEnd_503813 := by exact prefixLift 503813
  have htrace : WordTrace (prefixWord ++ tailWord_503813) baseStart_503813 baseEnd_503813 := by
    simpa [prefixWord, tailWord_503813, baseEnd_503813] using wordTrace_append hprefix tailTrace_503813
  have hstable : (prefixWord ++ tailWord_503813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503813).length < 2 ^ (prefixWord ++ tailWord_503813).sum := by decide
  have hdescent : baseEnd_503813 < baseStart_503813 := by decide
  rcases family_descends (prefixWord ++ tailWord_503813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503837 : List Nat := [1, 4, 2, 2, 2, 2, 7]
def baseStart_503837 : Nat := 118140960795 + 503837 * 2 ^ 59
def prefixEnd_503837 : Nat := 4983230072969 + 3 ^ 40 * 503837 * 2
def baseEnd_503837 : Nat := 25551659508093873493373

theorem tailTrace_503837 : CollatzResearch.WordTrace tailWord_503837 prefixEnd_503837 25551659508093873493373 := by
  unfold tailWord_503837
  simp only [CollatzResearch.WordTrace]
  refine ⟨18376445075692072354037765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12250963383794714902691843 18376445075692072354037765)
  ·
    refine ⟨3445583451692263566382081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18376445075692072354037765 3445583451692263566382081)
    ·
      refine ⟨2584187588769197674786561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3445583451692263566382081 2584187588769197674786561)
      ·
        refine ⟨1938140691576898256089921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2584187588769197674786561 1938140691576898256089921)
        ·
          refine ⟨1453605518682673692067441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938140691576898256089921 1453605518682673692067441)
          ·
            refine ⟨1090204139012005269050581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453605518682673692067441 1090204139012005269050581)
            ·
              refine ⟨25551659508093873493373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1090204139012005269050581 25551659508093873493373)
              ·
                rfl

theorem cell20_503837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_503837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503837 prefixEnd_503837 := by exact prefixLift 503837
  have htrace : WordTrace (prefixWord ++ tailWord_503837) baseStart_503837 baseEnd_503837 := by
    simpa [prefixWord, tailWord_503837, baseEnd_503837] using wordTrace_append hprefix tailTrace_503837
  have hstable : (prefixWord ++ tailWord_503837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503837).length < 2 ^ (prefixWord ++ tailWord_503837).sum := by decide
  have hdescent : baseEnd_503837 < baseStart_503837 := by decide
  rcases family_descends (prefixWord ++ tailWord_503837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503896 : List Nat := [2, 1, 2, 2, 1, 4, 8]
def baseStart_503896 : Nat := 118140960795 + 503896 * 2 ^ 59
def prefixEnd_503896 : Nat := 4983230072969 + 3 ^ 40 * 503896 * 2
def baseEnd_503896 : Nat := 25554651642278097608161

theorem tailTrace_503896 : CollatzResearch.WordTrace tailWord_503896 prefixEnd_503896 25554651642278097608161 := by
  unfold tailWord_503896
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189298491239162715217771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12252397988318883620290361 9189298491239162715217771)
  ·
    refine ⟨13783947736858744072826657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9189298491239162715217771 13783947736858744072826657)
    ·
      refine ⟨10337960802644058054619993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13783947736858744072826657 10337960802644058054619993)
      ·
        refine ⟨7753470601983043540964995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10337960802644058054619993 7753470601983043540964995)
        ·
          refine ⟨11630205902974565311447493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753470601983043540964995 11630205902974565311447493)
          ·
            refine ⟨2180663606807730995896405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11630205902974565311447493 2180663606807730995896405)
            ·
              refine ⟨25554651642278097608161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2180663606807730995896405 25554651642278097608161)
              ·
                rfl

theorem cell20_503896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_503896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503896 prefixEnd_503896 := by exact prefixLift 503896
  have htrace : WordTrace (prefixWord ++ tailWord_503896) baseStart_503896 baseEnd_503896 := by
    simpa [prefixWord, tailWord_503896, baseEnd_503896] using wordTrace_append hprefix tailTrace_503896
  have hstable : (prefixWord ++ tailWord_503896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503896).length < 2 ^ (prefixWord ++ tailWord_503896).sum := by decide
  have hdescent : baseEnd_503896 < baseStart_503896 := by decide
  rcases family_descends (prefixWord ++ tailWord_503896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503916 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_503916 : Nat := 118140960795 + 503916 * 2 ^ 59
def prefixEnd_503916 : Nat := 4983230072969 + 3 ^ 40 * 503916 * 2
def baseEnd_503916 : Nat := 230000993325471697806701

theorem tailTrace_503916 : CollatzResearch.WordTrace tailWord_503916 prefixEnd_503916 230000993325471697806701 := by
  unfold tailWord_503916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189663221202934423081801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12252884294937245897442401 9189663221202934423081801)
  ·
    refine ⟨6892247415902200817311351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9189663221202934423081801 6892247415902200817311351)
    ·
      refine ⟨10338371123853301225967027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6892247415902200817311351 10338371123853301225967027)
      ·
        refine ⟨15507556685779951838950541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338371123853301225967027 15507556685779951838950541)
        ·
          refine ⟨5815333757167481939606453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15507556685779951838950541 5815333757167481939606453)
          ·
            refine ⟨545187539734451431838105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5815333757167481939606453 545187539734451431838105)
            ·
              refine ⟨408890654800838573878579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545187539734451431838105 408890654800838573878579)
              ·
                refine ⟨613335982201257860817869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408890654800838573878579 613335982201257860817869)
                ·
                  refine ⟨230000993325471697806701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613335982201257860817869 230000993325471697806701)
                  ·
                    rfl

theorem cell20_503916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_503916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_503916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_503916 prefixEnd_503916 := by exact prefixLift 503916
  have htrace : WordTrace (prefixWord ++ tailWord_503916) baseStart_503916 baseEnd_503916 := by
    simpa [prefixWord, tailWord_503916, baseEnd_503916] using wordTrace_append hprefix tailTrace_503916
  have hstable : (prefixWord ++ tailWord_503916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503916).length < 2 ^ (prefixWord ++ tailWord_503916).sum := by decide
  have hdescent : baseEnd_503916 < baseStart_503916 := by decide
  rcases family_descends (prefixWord ++ tailWord_503916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504010 : List Nat := [3, 1, 2, 1, 3, 1, 9]
def baseStart_504010 : Nat := 118140960795 + 504010 * 2 ^ 59
def prefixEnd_504010 : Nat := 4983230072969 + 3 ^ 40 * 504010 * 2
def baseEnd_504010 : Nat := 25560433054091683185887

theorem tailTrace_504010 : CollatzResearch.WordTrace tailWord_504010 prefixEnd_504010 25560433054091683185887 := by
  unfold tailWord_504010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595688726016330725021371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12255169936043548600056989 4595688726016330725021371)
  ·
    refine ⟨6893533089024496087532057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4595688726016330725021371 6893533089024496087532057)
    ·
      refine ⟨5170149816768372065649043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6893533089024496087532057 5170149816768372065649043)
      ·
        refine ⟨7755224725152558098473565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170149816768372065649043 7755224725152558098473565)
        ·
          refine ⟨2908209271932209286927587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7755224725152558098473565 2908209271932209286927587)
          ·
            refine ⟨4362313907898313930391381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908209271932209286927587 4362313907898313930391381)
            ·
              refine ⟨25560433054091683185887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4362313907898313930391381 25560433054091683185887)
              ·
                rfl

theorem cell20_504010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_504010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504010 prefixEnd_504010 := by exact prefixLift 504010
  have htrace : WordTrace (prefixWord ++ tailWord_504010) baseStart_504010 baseEnd_504010 := by
    simpa [prefixWord, tailWord_504010, baseEnd_504010] using wordTrace_append hprefix tailTrace_504010
  have hstable : (prefixWord ++ tailWord_504010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504010).length < 2 ^ (prefixWord ++ tailWord_504010).sum := by decide
  have hdescent : baseEnd_504010 < baseStart_504010 := by decide
  rcases family_descends (prefixWord ++ tailWord_504010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504071 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 2]
def baseStart_504071 : Nat := 118140960795 + 504071 * 2 ^ 59
def prefixEnd_504071 : Nat := 4983230072969 + 3 ^ 40 * 504071 * 2
def baseEnd_504071 : Nat := 230071739548980047639401

theorem tailTrace_504071 : CollatzResearch.WordTrace tailWord_504071 prefixEnd_504071 230071739548980047639401 := by
  unfold tailWord_504071
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384979756844330318056067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12256653171229553545370711 18384979756844330318056067)
  ·
    refine ⟨27577469635266495477084101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18384979756844330318056067 27577469635266495477084101)
    ·
      refine ⟨5170775556612467901953269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27577469635266495477084101 5170775556612467901953269)
      ·
        refine ⟨484760208432418865808119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5170775556612467901953269 484760208432418865808119)
        ·
          refine ⟨727140312648628298712179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484760208432418865808119 727140312648628298712179)
          ·
            refine ⟨1090710468972942448068269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727140312648628298712179 1090710468972942448068269)
            ·
              refine ⟨409016425864853418025601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090710468972942448068269 409016425864853418025601)
              ·
                refine ⟨306762319398640063519201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409016425864853418025601 306762319398640063519201)
                ·
                  refine ⟨230071739548980047639401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306762319398640063519201 230071739548980047639401)
                  ·
                    rfl

theorem cell20_504071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 2].length) (baseStart_504071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504071 prefixEnd_504071 := by exact prefixLift 504071
  have htrace : WordTrace (prefixWord ++ tailWord_504071) baseStart_504071 baseEnd_504071 := by
    simpa [prefixWord, tailWord_504071, baseEnd_504071] using wordTrace_append hprefix tailTrace_504071
  have hstable : (prefixWord ++ tailWord_504071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504071).length < 2 ^ (prefixWord ++ tailWord_504071).sum := by decide
  have hdescent : baseEnd_504071 < baseStart_504071 := by decide
  rcases family_descends (prefixWord ++ tailWord_504071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504072 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_504072 : Nat := 118140960795 + 504072 * 2 ^ 59
def prefixEnd_504072 : Nat := 4983230072969 + 3 ^ 40 * 504072 * 2
def baseEnd_504072 : Nat := 230072195976228488606063

theorem tailTrace_504072 : CollatzResearch.WordTrace tailWord_504072 prefixEnd_504072 230072195976228488606063 := by
  unfold tailWord_504072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192508114920353744421235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12256677486560471659228313 9192508114920353744421235)
  ·
    refine ⟨13788762172380530616631853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9192508114920353744421235 13788762172380530616631853)
    ·
      refine ⟨5170785814642698981236945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13788762172380530616631853 5170785814642698981236945)
      ·
        refine ⟨3878089360982024235927709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5170785814642698981236945 3878089360982024235927709)
        ·
          refine ⟨1454283510368259088472891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3878089360982024235927709 1454283510368259088472891)
          ·
            refine ⟨2181425265552388632709337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454283510368259088472891 2181425265552388632709337)
            ·
              refine ⟨1636068949164291474532003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181425265552388632709337 1636068949164291474532003)
              ·
                refine ⟨2454103423746437211798005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636068949164291474532003 2454103423746437211798005)
                ·
                  refine ⟨230072195976228488606063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454103423746437211798005 230072195976228488606063)
                  ·
                    rfl

theorem cell20_504072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_504072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504072 prefixEnd_504072 := by exact prefixLift 504072
  have htrace : WordTrace (prefixWord ++ tailWord_504072) baseStart_504072 baseEnd_504072 := by
    simpa [prefixWord, tailWord_504072, baseEnd_504072] using wordTrace_append hprefix tailTrace_504072
  have hstable : (prefixWord ++ tailWord_504072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504072).length < 2 ^ (prefixWord ++ tailWord_504072).sum := by decide
  have hdescent : baseEnd_504072 < baseStart_504072 := by decide
  rcases family_descends (prefixWord ++ tailWord_504072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504075 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 2]
def baseStart_504075 : Nat := 118140960795 + 504075 * 2 ^ 59
def prefixEnd_504075 : Nat := 4983230072969 + 3 ^ 40 * 504075 * 2
def baseEnd_504075 : Nat := 230073565257973811506051

theorem tailTrace_504075 : CollatzResearch.WordTrace tailWord_504075 prefixEnd_504075 230073565257973811506051 := by
  unfold tailWord_504075
  simp only [CollatzResearch.WordTrace]
  refine ⟨18385125648829839001201679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12256750432553226000801119 18385125648829839001201679)
  ·
    refine ⟨27577688473244758501802519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18385125648829839001201679 27577688473244758501802519)
    ·
      refine ⟨41366532709867137752703779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27577688473244758501802519 41366532709867137752703779)
      ·
        refine ⟨62049799064800706629055669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41366532709867137752703779 62049799064800706629055669)
        ·
          refine ⟨5817168662325066246473969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62049799064800706629055669 5817168662325066246473969)
          ·
            refine ⟨4362876496743799684855477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817168662325066246473969 4362876496743799684855477)
            ·
              refine ⟨409019671569731220455201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4362876496743799684855477 409019671569731220455201)
              ·
                refine ⟨306764753677298415341401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409019671569731220455201 306764753677298415341401)
                ·
                  refine ⟨230073565257973811506051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306764753677298415341401 230073565257973811506051)
                  ·
                    rfl

theorem cell20_504075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 2].length) (baseStart_504075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504075 prefixEnd_504075 := by exact prefixLift 504075
  have htrace : WordTrace (prefixWord ++ tailWord_504075) baseStart_504075 baseEnd_504075 := by
    simpa [prefixWord, tailWord_504075, baseEnd_504075] using wordTrace_append hprefix tailTrace_504075
  have hstable : (prefixWord ++ tailWord_504075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504075).length < 2 ^ (prefixWord ++ tailWord_504075).sum := by decide
  have hdescent : baseEnd_504075 < baseStart_504075 := by decide
  rcases family_descends (prefixWord ++ tailWord_504075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504131 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_504131 : Nat := 118140960795 + 504131 * 2 ^ 59
def prefixEnd_504131 : Nat := 4983230072969 + 3 ^ 40 * 504131 * 2
def baseEnd_504131 : Nat := 230099125183886505639155

theorem tailTrace_504131 : CollatzResearch.WordTrace tailWord_504131 prefixEnd_504131 230099125183886505639155 := by
  unfold tailWord_504131
  simp only [CollatzResearch.WordTrace]
  refine ⟨18387168136626960565240247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12258112091084640376826831 18387168136626960565240247)
  ·
    refine ⟨27580752204940440847860371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18387168136626960565240247 27580752204940440847860371)
    ·
      refine ⟨41371128307410661271790557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27580752204940440847860371 41371128307410661271790557)
      ·
        refine ⟨15514173115278997976921459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41371128307410661271790557 15514173115278997976921459)
        ·
          refine ⟨23271259672918496965382189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514173115278997976921459 23271259672918496965382189)
          ·
            refine ⟨8726722377344436362018321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23271259672918496965382189 8726722377344436362018321)
            ·
              refine ⟨6545041783008327271513741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726722377344436362018321 6545041783008327271513741)
              ·
                refine ⟨2454390668628122726817653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6545041783008327271513741 2454390668628122726817653)
                ·
                  refine ⟨230099125183886505639155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454390668628122726817653 230099125183886505639155)
                  ·
                    rfl

theorem cell20_504131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_504131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504131 prefixEnd_504131 := by exact prefixLift 504131
  have htrace : WordTrace (prefixWord ++ tailWord_504131) baseStart_504131 baseEnd_504131 := by
    simpa [prefixWord, tailWord_504131, baseEnd_504131] using wordTrace_append hprefix tailTrace_504131
  have hstable : (prefixWord ++ tailWord_504131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504131).length < 2 ^ (prefixWord ++ tailWord_504131).sum := by decide
  have hdescent : baseEnd_504131 < baseStart_504131 := by decide
  rcases family_descends (prefixWord ++ tailWord_504131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504169 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_504169 : Nat := 118140960795 + 504169 * 2 ^ 59
def prefixEnd_504169 : Nat := 4983230072969 + 3 ^ 40 * 504169 * 2
def baseEnd_504169 : Nat := 230116469419327262372333

theorem tailTrace_504169 : CollatzResearch.WordTrace tailWord_504169 prefixEnd_504169 230116469419327262372333 := by
  unfold tailWord_504169
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388554110489293055123561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12259036073659528703415707 18388554110489293055123561)
  ·
    refine ⟨13791415582866969791342671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18388554110489293055123561 13791415582866969791342671)
    ·
      refine ⟨20687123374300454687014007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13791415582866969791342671 20687123374300454687014007)
      ·
        refine ⟨31030685061450682030521011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20687123374300454687014007 31030685061450682030521011)
        ·
          refine ⟨46546027592176023045781517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31030685061450682030521011 46546027592176023045781517)
          ·
            refine ⟨17454760347066008642168069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46546027592176023045781517 17454760347066008642168069)
            ·
              refine ⟨3272767565074876620406513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17454760347066008642168069 3272767565074876620406513)
              ·
                refine ⟨2454575673806157465304885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272767565074876620406513 2454575673806157465304885)
                ·
                  refine ⟨230116469419327262372333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454575673806157465304885 230116469419327262372333)
                  ·
                    rfl

theorem cell20_504169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_504169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504169 prefixEnd_504169 := by exact prefixLift 504169
  have htrace : WordTrace (prefixWord ++ tailWord_504169) baseStart_504169 baseEnd_504169 := by
    simpa [prefixWord, tailWord_504169, baseEnd_504169] using wordTrace_append hprefix tailTrace_504169
  have hstable : (prefixWord ++ tailWord_504169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504169).length < 2 ^ (prefixWord ++ tailWord_504169).sum := by decide
  have hdescent : baseEnd_504169 < baseStart_504169 := by decide
  rcases family_descends (prefixWord ++ tailWord_504169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504182 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_504182 : Nat := 118140960795 + 504182 * 2 ^ 59
def prefixEnd_504182 : Nat := 4983230072969 + 3 ^ 40 * 504182 * 2
def baseEnd_504182 : Nat := 230122402973556994938947

theorem tailTrace_504182 : CollatzResearch.WordTrace tailWord_504182 prefixEnd_504182 230122402973556994938947 := by
  unfold tailWord_504182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149314266215137267209175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12259352172961464183564533 1149314266215137267209175)
  ·
    refine ⟨1723971399322705900813763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1149314266215137267209175 1723971399322705900813763)
    ·
      refine ⟨2585957098984058851220645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723971399322705900813763 2585957098984058851220645)
      ·
        refine ⟨484866956059511034603871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2585957098984058851220645 484866956059511034603871)
        ·
          refine ⟨727300434089266551905807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484866956059511034603871 727300434089266551905807)
          ·
            refine ⟨1090950651133899827858711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727300434089266551905807 1090950651133899827858711)
            ·
              refine ⟨1636425976700849741788067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090950651133899827858711 1636425976700849741788067)
              ·
                refine ⟨2454638965051274612682101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636425976700849741788067 2454638965051274612682101)
                ·
                  refine ⟨230122402973556994938947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454638965051274612682101 230122402973556994938947)
                  ·
                    rfl

theorem cell20_504182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_504182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504182 prefixEnd_504182 := by exact prefixLift 504182
  have htrace : WordTrace (prefixWord ++ tailWord_504182) baseStart_504182 baseEnd_504182 := by
    simpa [prefixWord, tailWord_504182, baseEnd_504182] using wordTrace_append hprefix tailTrace_504182
  have hstable : (prefixWord ++ tailWord_504182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504182).length < 2 ^ (prefixWord ++ tailWord_504182).sum := by decide
  have hdescent : baseEnd_504182 < baseStart_504182 := by decide
  rcases family_descends (prefixWord ++ tailWord_504182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504200 : List Nat := [2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_504200 : Nat := 118140960795 + 504200 * 2 ^ 59
def prefixEnd_504200 : Nat := 4983230072969 + 3 ^ 40 * 504200 * 2
def baseEnd_504200 : Nat := 76710206221342977446291

theorem tailTrace_504200 : CollatzResearch.WordTrace tailWord_504200 prefixEnd_504200 76710206221342977446291 := by
  unfold tailWord_504200
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194842386688492674751027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12259789848917990233001369 9194842386688492674751027)
  ·
    refine ⟨13792263580032739012126541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9194842386688492674751027 13792263580032739012126541)
    ·
      refine ⟨5172098842512277129547453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13792263580032739012126541 5172098842512277129547453)
      ·
        refine ⟨1939537065942103923580295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5172098842512277129547453 1939537065942103923580295)
        ·
          refine ⟨2909305598913155885370443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939537065942103923580295 2909305598913155885370443)
          ·
            refine ⟨4363958398369733828055665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909305598913155885370443 4363958398369733828055665)
            ·
              refine ⟨3272968798777300371041749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363958398369733828055665 3272968798777300371041749)
              ·
                refine ⟨76710206221342977446291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3272968798777300371041749 76710206221342977446291)
                ·
                  rfl

theorem cell20_504200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_504200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504200 prefixEnd_504200 := by exact prefixLift 504200
  have htrace : WordTrace (prefixWord ++ tailWord_504200) baseStart_504200 baseEnd_504200 := by
    simpa [prefixWord, tailWord_504200, baseEnd_504200] using wordTrace_append hprefix tailTrace_504200
  have hstable : (prefixWord ++ tailWord_504200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504200).length < 2 ^ (prefixWord ++ tailWord_504200).sum := by decide
  have hdescent : baseEnd_504200 < baseStart_504200 := by decide
  rcases family_descends (prefixWord ++ tailWord_504200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504203 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 3]
def baseStart_504203 : Nat := 118140960795 + 504203 * 2 ^ 59
def prefixEnd_504203 : Nat := 4983230072969 + 3 ^ 40 * 504203 * 2
def baseEnd_504203 : Nat := 230131987945774255238861

theorem tailTrace_504203 : CollatzResearch.WordTrace tailWord_504203 prefixEnd_504203 230131987945774255238861 := by
  unfold tailWord_504203
  simp only [CollatzResearch.WordTrace]
  refine ⟨18389794192366116861861263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12259862794910744574574175 18389794192366116861861263)
  ·
    refine ⟨27584691288549175292791895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18389794192366116861861263 27584691288549175292791895)
    ·
      refine ⟨41377036932823762939187843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27584691288549175292791895 41377036932823762939187843)
      ·
        refine ⟨62065555399235644408781765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41377036932823762939187843 62065555399235644408781765)
        ·
          refine ⟨11637291637356683326646581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62065555399235644408781765 11637291637356683326646581)
          ·
            refine ⟨1090996091002189061873117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11637291637356683326646581 1090996091002189061873117)
            ·
              refine ⟨409123534125820898202419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090996091002189061873117 409123534125820898202419)
              ·
                refine ⟨613685301188731347303629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409123534125820898202419 613685301188731347303629)
                ·
                  refine ⟨230131987945774255238861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613685301188731347303629 230131987945774255238861)
                  ·
                    rfl

theorem cell20_504203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_504203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504203 prefixEnd_504203 := by exact prefixLift 504203
  have htrace : WordTrace (prefixWord ++ tailWord_504203) baseStart_504203 baseEnd_504203 := by
    simpa [prefixWord, tailWord_504203, baseEnd_504203] using wordTrace_append hprefix tailTrace_504203
  have hstable : (prefixWord ++ tailWord_504203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504203).length < 2 ^ (prefixWord ++ tailWord_504203).sum := by decide
  have hdescent : baseEnd_504203 < baseStart_504203 := by decide
  rcases family_descends (prefixWord ++ tailWord_504203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504227 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 2]
def baseStart_504227 : Nat := 118140960795 + 504227 * 2 ^ 59
def prefixEnd_504227 : Nat := 4983230072969 + 3 ^ 40 * 504227 * 2
def baseEnd_504227 : Nat := 230142942199736838438763

theorem tailTrace_504227 : CollatzResearch.WordTrace tailWord_504227 prefixEnd_504227 230142942199736838438763 := by
  unfold tailWord_504227
  simp only [CollatzResearch.WordTrace]
  refine ⟨18390669544279168960734935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12260446362852779307156623 18390669544279168960734935)
  ·
    refine ⟨27586004316418753441102403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18390669544279168960734935 27586004316418753441102403)
    ·
      refine ⟨41379006474628130161653605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27586004316418753441102403 41379006474628130161653605)
      ·
        refine ⟨7758563713992774405310051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41379006474628130161653605 7758563713992774405310051)
        ·
          refine ⟨11637845570989161607965077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758563713992774405310051 11637845570989161607965077)
          ·
            refine ⟨545524011140116950373363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11637845570989161607965077 545524011140116950373363)
            ·
              refine ⟨818286016710175425560045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545524011140116950373363 818286016710175425560045)
              ·
                refine ⟨306857256266315784585017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818286016710175425560045 306857256266315784585017)
                ·
                  refine ⟨230142942199736838438763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306857256266315784585017 230142942199736838438763)
                  ·
                    rfl

theorem cell20_504227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 2].length) (baseStart_504227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504227 prefixEnd_504227 := by exact prefixLift 504227
  have htrace : WordTrace (prefixWord ++ tailWord_504227) baseStart_504227 baseEnd_504227 := by
    simpa [prefixWord, tailWord_504227, baseEnd_504227] using wordTrace_append hprefix tailTrace_504227
  have hstable : (prefixWord ++ tailWord_504227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504227).length < 2 ^ (prefixWord ++ tailWord_504227).sum := by decide
  have hdescent : baseEnd_504227 < baseStart_504227 := by decide
  rcases family_descends (prefixWord ++ tailWord_504227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504293 : List Nat := [1, 3, 1, 5, 3, 7]
def baseStart_504293 : Nat := 118140960795 + 504293 * 2 ^ 59
def prefixEnd_504293 : Nat := 4983230072969 + 3 ^ 40 * 504293 * 2
def baseEnd_504293 : Nat := 8524928385116071934759

theorem tailTrace_504293 : CollatzResearch.WordTrace tailWord_504293 prefixEnd_504293 8524928385116071934759 := by
  unfold tailWord_504293
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393076762040062232637533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12262051174693374821758355 18393076762040062232637533)
  ·
    refine ⟨6897403785765023337239075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18393076762040062232637533 6897403785765023337239075)
    ·
      refine ⟨10346105678647535005858613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6897403785765023337239075 10346105678647535005858613)
      ·
        refine ⟨969947407373206406799245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10346105678647535005858613 969947407373206406799245)
        ·
          refine ⟨363730277764952402549717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 969947407373206406799245 363730277764952402549717)
          ·
            refine ⟨8524928385116071934759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 363730277764952402549717 8524928385116071934759)
            ·
              rfl

theorem cell20_504293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 7].length) (baseStart_504293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504293 prefixEnd_504293 := by exact prefixLift 504293
  have htrace : WordTrace (prefixWord ++ tailWord_504293) baseStart_504293 baseEnd_504293 := by
    simpa [prefixWord, tailWord_504293, baseEnd_504293] using wordTrace_append hprefix tailTrace_504293
  have hstable : (prefixWord ++ tailWord_504293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504293).length < 2 ^ (prefixWord ++ tailWord_504293).sum := by decide
  have hdescent : baseEnd_504293 < baseStart_504293 := by decide
  rcases family_descends (prefixWord ++ tailWord_504293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504300 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_504300 : Nat := 118140960795 + 504300 * 2 ^ 59
def prefixEnd_504300 : Nat := 4983230072969 + 3 ^ 40 * 504300 * 2
def baseEnd_504300 : Nat := 230176261388873029005131

theorem tailTrace_504300 : CollatzResearch.WordTrace tailWord_504300 prefixEnd_504300 230176261388873029005131 := by
  unfold tailWord_504300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196666036507351214071177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12262221382009801618761569 9196666036507351214071177)
  ·
    refine ⟨6897499527380513410553383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9196666036507351214071177 6897499527380513410553383)
    ·
      refine ⟨10346249291070770115830075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6897499527380513410553383 10346249291070770115830075)
      ·
        refine ⟨15519373936606155173745113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10346249291070770115830075 15519373936606155173745113)
        ·
          refine ⟨11639530452454616380308835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15519373936606155173745113 11639530452454616380308835)
          ·
            refine ⟨17459295678681924570463253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639530452454616380308835 17459295678681924570463253)
            ·
              refine ⟨818404484938215214240465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17459295678681924570463253 818404484938215214240465)
              ·
                refine ⟨613803363703661410680349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818404484938215214240465 613803363703661410680349)
                ·
                  refine ⟨230176261388873029005131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613803363703661410680349 230176261388873029005131)
                  ·
                    rfl

theorem cell20_504300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_504300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504300 prefixEnd_504300 := by exact prefixLift 504300
  have htrace : WordTrace (prefixWord ++ tailWord_504300) baseStart_504300 baseEnd_504300 := by
    simpa [prefixWord, tailWord_504300, baseEnd_504300] using wordTrace_append hprefix tailTrace_504300
  have hstable : (prefixWord ++ tailWord_504300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504300).length < 2 ^ (prefixWord ++ tailWord_504300).sum := by decide
  have hdescent : baseEnd_504300 < baseStart_504300 := by decide
  rcases family_descends (prefixWord ++ tailWord_504300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504324 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_504324 : Nat := 118140960795 + 504324 * 2 ^ 59
def prefixEnd_504324 : Nat := 4983230072969 + 3 ^ 40 * 504324 * 2
def baseEnd_504324 : Nat := 230187215642835612205033

theorem tailTrace_504324 : CollatzResearch.WordTrace tailWord_504324 prefixEnd_504324 230187215642835612205033 := by
  unfold tailWord_504324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197103712463877263508013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12262804949951836351344017 9197103712463877263508013)
  ·
    refine ⟨3448913892173953973815505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9197103712463877263508013 3448913892173953973815505)
    ·
      refine ⟨2586685419130465480361629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3448913892173953973815505 2586685419130465480361629)
      ·
        refine ⟨970007032173924555135611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2586685419130465480361629 970007032173924555135611)
        ·
          refine ⟨1455010548260886832703417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970007032173924555135611 1455010548260886832703417)
          ·
            refine ⟨1091257911195665124527563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455010548260886832703417 1091257911195665124527563)
            ·
              refine ⟨1636886866793497686791345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091257911195665124527563 1636886866793497686791345)
              ·
                refine ⟨1227665150095123265093509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636886866793497686791345 1227665150095123265093509)
                ·
                  refine ⟨230187215642835612205033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227665150095123265093509 230187215642835612205033)
                  ·
                    rfl

theorem cell20_504324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_504324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504324 prefixEnd_504324 := by exact prefixLift 504324
  have htrace : WordTrace (prefixWord ++ tailWord_504324) baseStart_504324 baseEnd_504324 := by
    simpa [prefixWord, tailWord_504324, baseEnd_504324] using wordTrace_append hprefix tailTrace_504324
  have hstable : (prefixWord ++ tailWord_504324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504324).length < 2 ^ (prefixWord ++ tailWord_504324).sum := by decide
  have hdescent : baseEnd_504324 < baseStart_504324 := by decide
  rcases family_descends (prefixWord ++ tailWord_504324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504331 : List Nat := [1, 1, 1, 1, 7, 2, 3, 4]
def baseStart_504331 : Nat := 118140960795 + 504331 * 2 ^ 59
def prefixEnd_504331 : Nat := 4983230072969 + 3 ^ 40 * 504331 * 2
def baseEnd_504331 : Nat := 76730136877858232990557

theorem tailTrace_504331 : CollatzResearch.WordTrace tailWord_504331 prefixEnd_504331 76730136877858232990557 := by
  unfold tailWord_504331
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394462735902394722520847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12262975157268263148347231 18394462735902394722520847)
  ·
    refine ⟨27591694103853592083781271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18394462735902394722520847 27591694103853592083781271)
    ·
      refine ⟨41387541155780388125671907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27591694103853592083781271 41387541155780388125671907)
      ·
        refine ⟨62081311733670582188507861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41387541155780388125671907 62081311733670582188507861)
        ·
          refine ⟨1455030743757904270043153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62081311733670582188507861 1455030743757904270043153)
          ·
            refine ⟨1091273057818428202532365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455030743757904270043153 1091273057818428202532365)
            ·
              refine ⟨409227396681910575949637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091273057818428202532365 409227396681910575949637)
              ·
                refine ⟨76730136877858232990557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409227396681910575949637 76730136877858232990557)
                ·
                  rfl

theorem cell20_504331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_504331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504331 prefixEnd_504331 := by exact prefixLift 504331
  have htrace : WordTrace (prefixWord ++ tailWord_504331) baseStart_504331 baseEnd_504331 := by
    simpa [prefixWord, tailWord_504331, baseEnd_504331] using wordTrace_append hprefix tailTrace_504331
  have hstable : (prefixWord ++ tailWord_504331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504331).length < 2 ^ (prefixWord ++ tailWord_504331).sum := by decide
  have hdescent : baseEnd_504331 < baseStart_504331 := by decide
  rcases family_descends (prefixWord ++ tailWord_504331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504355 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 3]
def baseStart_504355 : Nat := 118140960795 + 504355 * 2 ^ 59
def prefixEnd_504355 : Nat := 4983230072969 + 3 ^ 40 * 504355 * 2
def baseEnd_504355 : Nat := 230201364887537282171573

theorem tailTrace_504355 : CollatzResearch.WordTrace tailWord_504355 prefixEnd_504355 230201364887537282171573 := by
  unfold tailWord_504355
  simp only [CollatzResearch.WordTrace]
  refine ⟨18395338087815446821394519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12263558725210297880929679 18395338087815446821394519)
  ·
    refine ⟨27593007131723170232091779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18395338087815446821394519 27593007131723170232091779)
    ·
      refine ⟨41389510697584755348137669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27593007131723170232091779 41389510697584755348137669)
      ·
        refine ⟨7760533255797141627775813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41389510697584755348137669 7760533255797141627775813)
        ·
          refine ⟨1455099985461964055207965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7760533255797141627775813 1455099985461964055207965)
          ·
            refine ⟨545662494548236520702987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1455099985461964055207965 545662494548236520702987)
            ·
              refine ⟨818493741822354781054481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545662494548236520702987 818493741822354781054481)
              ·
                refine ⟨613870306366766085790861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818493741822354781054481 613870306366766085790861)
                ·
                  refine ⟨230201364887537282171573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613870306366766085790861 230201364887537282171573)
                  ·
                    rfl

theorem cell20_504355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_504355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504355 prefixEnd_504355 := by exact prefixLift 504355
  have htrace : WordTrace (prefixWord ++ tailWord_504355) baseStart_504355 baseEnd_504355 := by
    simpa [prefixWord, tailWord_504355, baseEnd_504355] using wordTrace_append hprefix tailTrace_504355
  have hstable : (prefixWord ++ tailWord_504355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504355).length < 2 ^ (prefixWord ++ tailWord_504355).sum := by decide
  have hdescent : baseEnd_504355 < baseStart_504355 := by decide
  rcases family_descends (prefixWord ++ tailWord_504355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504362 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_504362 : Nat := 118140960795 + 504362 * 2 ^ 59
def prefixEnd_504362 : Nat := 4983230072969 + 3 ^ 40 * 504362 * 2
def baseEnd_504362 : Nat := 230204559878276368938211

theorem tailTrace_504362 : CollatzResearch.WordTrace tailWord_504362 prefixEnd_504362 230204559878276368938211 := by
  unfold tailWord_504362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598898349697521754224835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12263728932526724677932893 4598898349697521754224835)
  ·
    refine ⟨6898347524546282631337253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4598898349697521754224835 6898347524546282631337253)
    ·
      refine ⟨1293440160852427993375735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6898347524546282631337253 1293440160852427993375735)
      ·
        refine ⟨1940160241278641990063603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293440160852427993375735 1940160241278641990063603)
        ·
          refine ⟨2910240361917962985095405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940160241278641990063603 2910240361917962985095405)
          ·
            refine ⟨1091340135719236119410777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2910240361917962985095405 1091340135719236119410777)
            ·
              refine ⟨818505101789427089558083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091340135719236119410777 818505101789427089558083)
              ·
                refine ⟨1227757652684140634337125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818505101789427089558083 1227757652684140634337125)
                ·
                  refine ⟨230204559878276368938211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227757652684140634337125 230204559878276368938211)
                  ·
                    rfl

theorem cell20_504362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_504362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504362 prefixEnd_504362 := by exact prefixLift 504362
  have htrace : WordTrace (prefixWord ++ tailWord_504362) baseStart_504362 baseEnd_504362 := by
    simpa [prefixWord, tailWord_504362, baseEnd_504362] using wordTrace_append hprefix tailTrace_504362
  have hstable : (prefixWord ++ tailWord_504362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504362).length < 2 ^ (prefixWord ++ tailWord_504362).sum := by decide
  have hdescent : baseEnd_504362 < baseStart_504362 := by decide
  rcases family_descends (prefixWord ++ tailWord_504362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504382 : List Nat := [4, 2, 1, 4, 2, 1, 2, 4]
def baseStart_504382 : Nat := 118140960795 + 504382 * 2 ^ 59
def prefixEnd_504382 : Nat := 4983230072969 + 3 ^ 40 * 504382 * 2
def baseEnd_504382 : Nat := 76737896141081729423821

theorem tailTrace_504382 : CollatzResearch.WordTrace tailWord_504382 prefixEnd_504382 76737896141081729423821 := by
  unfold tailWord_504382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299540357339703804078425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12264215239145086955084933 2299540357339703804078425)
  ·
    refine ⟨1724655268004777853058819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2299540357339703804078425 1724655268004777853058819)
    ·
      refine ⟨2586982902007166779588229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724655268004777853058819 2586982902007166779588229)
      ·
        refine ⟨485059294126343771172793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2586982902007166779588229 485059294126343771172793)
        ·
          refine ⟨363794470594757828379595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485059294126343771172793 363794470594757828379595)
          ·
            refine ⟨545691705892136742569393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363794470594757828379595 545691705892136742569393)
            ·
              refine ⟨409268779419102556927045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545691705892136742569393 409268779419102556927045)
              ·
                refine ⟨76737896141081729423821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409268779419102556927045 76737896141081729423821)
                ·
                  rfl

theorem cell20_504382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_504382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504382 prefixEnd_504382 := by exact prefixLift 504382
  have htrace : WordTrace (prefixWord ++ tailWord_504382) baseStart_504382 baseEnd_504382 := by
    simpa [prefixWord, tailWord_504382, baseEnd_504382] using wordTrace_append hprefix tailTrace_504382
  have hstable : (prefixWord ++ tailWord_504382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504382).length < 2 ^ (prefixWord ++ tailWord_504382).sum := by decide
  have hdescent : baseEnd_504382 < baseStart_504382 := by decide
  rcases family_descends (prefixWord ++ tailWord_504382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504417 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 2]
def baseStart_504417 : Nat := 118140960795 + 504417 * 2 ^ 59
def prefixEnd_504417 : Nat := 4983230072969 + 3 ^ 40 * 504417 * 2
def baseEnd_504417 : Nat := 230229663376940622104653

theorem tailTrace_504417 : CollatzResearch.WordTrace tailWord_504417 prefixEnd_504417 230229663376940622104653 := by
  unfold tailWord_504417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397599413590831410151505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12265066275727220940101003 18397599413590831410151505)
  ·
    refine ⟨13798199560193123557613629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18397599413590831410151505 13798199560193123557613629)
    ·
      refine ⟨5174324835072421334105111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13798199560193123557613629 5174324835072421334105111)
      ·
        refine ⟨7761487252608632001157667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174324835072421334105111 7761487252608632001157667)
        ·
          refine ⟨11642230878912948001736501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761487252608632001157667 11642230878912948001736501)
          ·
            refine ⟨1091459144898088875162797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11642230878912948001736501 1091459144898088875162797)
            ·
              refine ⟨409297179336783328186049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091459144898088875162797 409297179336783328186049)
              ·
                refine ⟨306972884502587496139537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409297179336783328186049 306972884502587496139537)
                ·
                  refine ⟨230229663376940622104653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306972884502587496139537 230229663376940622104653)
                  ·
                    rfl

theorem cell20_504417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_504417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504417 prefixEnd_504417 := by exact prefixLift 504417
  have htrace : WordTrace (prefixWord ++ tailWord_504417) baseStart_504417 baseEnd_504417 := by
    simpa [prefixWord, tailWord_504417, baseEnd_504417] using wordTrace_append hprefix tailTrace_504417
  have hstable : (prefixWord ++ tailWord_504417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504417).length < 2 ^ (prefixWord ++ tailWord_504417).sum := by decide
  have hdescent : baseEnd_504417 < baseStart_504417 := by decide
  rcases family_descends (prefixWord ++ tailWord_504417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504466 : List Nat := [3, 2, 3, 1, 2, 9]
def baseStart_504466 : Nat := 118140960795 + 504466 * 2 ^ 59
def prefixEnd_504466 : Nat := 4983230072969 + 3 ^ 40 * 504466 * 2
def baseEnd_504466 : Nat := 8527852900448675165597

theorem tailTrace_504466 : CollatzResearch.WordTrace tailWord_504466 prefixEnd_504466 8527852900448675165597 := by
  unfold tailWord_504466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599846647603328194671313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12266257726942208519123501 4599846647603328194671313)
  ·
    refine ⟨3449884985702496146003485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4599846647603328194671313 3449884985702496146003485)
    ·
      refine ⟨1293706869638436054751307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3449884985702496146003485 1293706869638436054751307)
      ·
        refine ⟨1940560304457654082126961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293706869638436054751307 1940560304457654082126961)
        ·
          refine ⟨1455420228343240561595221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940560304457654082126961 1455420228343240561595221)
          ·
            refine ⟨8527852900448675165597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1455420228343240561595221 8527852900448675165597)
            ·
              rfl

theorem cell20_504466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 9].length) (baseStart_504466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504466 prefixEnd_504466 := by exact prefixLift 504466
  have htrace : WordTrace (prefixWord ++ tailWord_504466) baseStart_504466 baseEnd_504466 := by
    simpa [prefixWord, tailWord_504466, baseEnd_504466] using wordTrace_append hprefix tailTrace_504466
  have hstable : (prefixWord ++ tailWord_504466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504466).length < 2 ^ (prefixWord ++ tailWord_504466).sum := by decide
  have hdescent : baseEnd_504466 < baseStart_504466 := by decide
  rcases family_descends (prefixWord ++ tailWord_504466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504535 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_504535 : Nat := 118140960795 + 504535 * 2 ^ 59
def prefixEnd_504535 : Nat := 4983230072969 + 3 ^ 40 * 504535 * 2
def baseEnd_504535 : Nat := 230283521792256656170837

theorem tailTrace_504535 : CollatzResearch.WordTrace tailWord_504535 prefixEnd_504535 230283521792256656170837 := by
  unfold tailWord_504535
  simp only [CollatzResearch.WordTrace]
  refine ⟨18401903227163337562947059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12267935484775558375298039 18401903227163337562947059)
  ·
    refine ⟨27602854840745006344420589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18401903227163337562947059 27602854840745006344420589)
    ·
      refine ⟨10351070565279377379157721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27602854840745006344420589 10351070565279377379157721)
      ·
        refine ⟨7763302923959533034368291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10351070565279377379157721 7763302923959533034368291)
        ·
          refine ⟨11644954385939299551552437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7763302923959533034368291 11644954385939299551552437)
          ·
            refine ⟨1091714473681809332958041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11644954385939299551552437 1091714473681809332958041)
            ·
              refine ⟨818785855261356999718531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091714473681809332958041 818785855261356999718531)
              ·
                refine ⟨1228178782892035499577797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818785855261356999718531 1228178782892035499577797)
                ·
                  refine ⟨230283521792256656170837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1228178782892035499577797 230283521792256656170837)
                  ·
                    rfl

theorem cell20_504535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_504535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504535 prefixEnd_504535 := by exact prefixLift 504535
  have htrace : WordTrace (prefixWord ++ tailWord_504535) baseStart_504535 baseEnd_504535 := by
    simpa [prefixWord, tailWord_504535, baseEnd_504535] using wordTrace_append hprefix tailTrace_504535
  have hstable : (prefixWord ++ tailWord_504535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504535).length < 2 ^ (prefixWord ++ tailWord_504535).sum := by decide
  have hdescent : baseEnd_504535 < baseStart_504535 := by decide
  rcases family_descends (prefixWord ++ tailWord_504535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504545 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 3]
def baseStart_504545 : Nat := 118140960795 + 504545 * 2 ^ 59
def prefixEnd_504545 : Nat := 4983230072969 + 3 ^ 40 * 504545 * 2
def baseEnd_504545 : Nat := 230288086064741065837463

theorem tailTrace_504545 : CollatzResearch.WordTrace tailWord_504545 prefixEnd_504545 230288086064741065837463 := by
  unfold tailWord_504545
  simp only [CollatzResearch.WordTrace]
  refine ⟨18402267957127109270811089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12268178638084739513874059 18402267957127109270811089)
  ·
    refine ⟨13801700967845331953108317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18402267957127109270811089 13801700967845331953108317)
    ·
      refine ⟨5175637862941999482415619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13801700967845331953108317 5175637862941999482415619)
      ·
        refine ⟨7763456794412999223623429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175637862941999482415619 7763456794412999223623429)
        ·
          refine ⟨1455648148952437354429393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7763456794412999223623429 1455648148952437354429393)
          ·
            refine ⟨1091736111714328015822045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455648148952437354429393 1091736111714328015822045)
            ·
              refine ⟨409401041892873005933267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091736111714328015822045 409401041892873005933267)
              ·
                refine ⟨614101562839309508899901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409401041892873005933267 614101562839309508899901)
                ·
                  refine ⟨230288086064741065837463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614101562839309508899901 230288086064741065837463)
                  ·
                    rfl

theorem cell20_504545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_504545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504545 prefixEnd_504545 := by exact prefixLift 504545
  have htrace : WordTrace (prefixWord ++ tailWord_504545) baseStart_504545 baseEnd_504545 := by
    simpa [prefixWord, tailWord_504545, baseEnd_504545] using wordTrace_append hprefix tailTrace_504545
  have hstable : (prefixWord ++ tailWord_504545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504545).length < 2 ^ (prefixWord ++ tailWord_504545).sum := by decide
  have hdescent : baseEnd_504545 < baseStart_504545 := by decide
  rcases family_descends (prefixWord ++ tailWord_504545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504559 : List Nat := [1, 1, 2, 1, 5, 4, 2, 4]
def baseStart_504559 : Nat := 118140960795 + 504559 * 2 ^ 59
def prefixEnd_504559 : Nat := 4983230072969 + 3 ^ 40 * 504559 * 2
def baseEnd_504559 : Nat := 76764825348739746456913

theorem tailTrace_504559 : CollatzResearch.WordTrace tailWord_504559 prefixEnd_504559 76764825348739746456913 := by
  unfold tailWord_504559
  simp only [CollatzResearch.WordTrace]
  refine ⟨18402778579076389661820731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12268519052717593107880487 18402778579076389661820731)
  ·
    refine ⟨27604167868614584492731097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18402778579076389661820731 27604167868614584492731097)
    ·
      refine ⟨20703125901460938369548323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27604167868614584492731097 20703125901460938369548323)
      ·
        refine ⟨31054688852191407554322485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20703125901460938369548323 31054688852191407554322485)
        ·
          refine ⟨2911377079892944458217733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31054688852191407554322485 2911377079892944458217733)
          ·
            refine ⟨545883202479927085915825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2911377079892944458217733 545883202479927085915825)
            ·
              refine ⟨409412401859945314436869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545883202479927085915825 409412401859945314436869)
              ·
                refine ⟨76764825348739746456913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409412401859945314436869 76764825348739746456913)
                ·
                  rfl

theorem cell20_504559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_504559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504559 prefixEnd_504559 := by exact prefixLift 504559
  have htrace : WordTrace (prefixWord ++ tailWord_504559) baseStart_504559 baseEnd_504559 := by
    simpa [prefixWord, tailWord_504559, baseEnd_504559] using wordTrace_append hprefix tailTrace_504559
  have hstable : (prefixWord ++ tailWord_504559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504559).length < 2 ^ (prefixWord ++ tailWord_504559).sum := by decide
  have hdescent : baseEnd_504559 < baseStart_504559 := by decide
  rcases family_descends (prefixWord ++ tailWord_504559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504587 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_504587 : Nat := 118140960795 + 504587 * 2 ^ 59
def prefixEnd_504587 : Nat := 4983230072969 + 3 ^ 40 * 504587 * 2
def baseEnd_504587 : Nat := 230307256009175586437291

theorem tailTrace_504587 : CollatzResearch.WordTrace tailWord_504587 prefixEnd_504587 230307256009175586437291 := by
  unfold tailWord_504587
  simp only [CollatzResearch.WordTrace]
  refine ⟨18403799822974950443840015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12269199881983300295893343 18403799822974950443840015)
  ·
    refine ⟨27605699734462425665760023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18403799822974950443840015 27605699734462425665760023)
    ·
      refine ⟨41408549601693638498640035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27605699734462425665760023 41408549601693638498640035)
      ·
        refine ⟨62112824402540457747960053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41408549601693638498640035 62112824402540457747960053)
        ·
          refine ⟨5823077287738167913871255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62112824402540457747960053 5823077287738167913871255)
          ·
            refine ⟨8734615931607251870806883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823077287738167913871255 8734615931607251870806883)
            ·
              refine ⟨13101923897410877806210325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734615931607251870806883 13101923897410877806210325)
              ·
                refine ⟨614152682691134897166109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13101923897410877806210325 614152682691134897166109)
                ·
                  refine ⟨230307256009175586437291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614152682691134897166109 230307256009175586437291)
                  ·
                    rfl

theorem cell20_504587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_504587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504587 prefixEnd_504587 := by exact prefixLift 504587
  have htrace : WordTrace (prefixWord ++ tailWord_504587) baseStart_504587 baseEnd_504587 := by
    simpa [prefixWord, tailWord_504587, baseEnd_504587] using wordTrace_append hprefix tailTrace_504587
  have hstable : (prefixWord ++ tailWord_504587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504587).length < 2 ^ (prefixWord ++ tailWord_504587).sum := by decide
  have hdescent : baseEnd_504587 < baseStart_504587 := by decide
  rcases family_descends (prefixWord ++ tailWord_504587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504604 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_504604 : Nat := 118140960795 + 504604 * 2 ^ 59
def prefixEnd_504604 : Nat := 4983230072969 + 3 ^ 40 * 504604 * 2
def baseEnd_504604 : Nat := 230315015272399082870555

theorem tailTrace_504604 : CollatzResearch.WordTrace tailWord_504604 prefixEnd_504604 230315015272399082870555 := by
  unfold tailWord_504604
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202209931956681173604433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12269613242608908231472577 9202209931956681173604433)
  ·
    refine ⟨6901657448967510880203325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9202209931956681173604433 6901657448967510880203325)
    ·
      refine ⟨2588121543362816580076247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6901657448967510880203325 2588121543362816580076247)
      ·
        refine ⟨3882182315044224870114371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588121543362816580076247 3882182315044224870114371)
        ·
          refine ⟨5823273472566337305171557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882182315044224870114371 5823273472566337305171557)
          ·
            refine ⟨1091863776106188244719667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5823273472566337305171557 1091863776106188244719667)
            ·
              refine ⟨1637795664159282367079501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091863776106188244719667 1637795664159282367079501)
              ·
                refine ⟨614173374059730887654813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1637795664159282367079501 614173374059730887654813)
                ·
                  refine ⟨230315015272399082870555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614173374059730887654813 230315015272399082870555)
                  ·
                    rfl

theorem cell20_504604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_504604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504604 prefixEnd_504604 := by exact prefixLift 504604
  have htrace : WordTrace (prefixWord ++ tailWord_504604) baseStart_504604 baseEnd_504604 := by
    simpa [prefixWord, tailWord_504604, baseEnd_504604] using wordTrace_append hprefix tailTrace_504604
  have hstable : (prefixWord ++ tailWord_504604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504604).length < 2 ^ (prefixWord ++ tailWord_504604).sum := by decide
  have hdescent : baseEnd_504604 < baseStart_504604 := by decide
  rcases family_descends (prefixWord ++ tailWord_504604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
