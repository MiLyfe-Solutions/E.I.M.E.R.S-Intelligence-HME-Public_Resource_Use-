import V185TrunkScan22Chunk310

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2775011 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_2775011 : Nat := 118140960795 + 2775011 * 2 ^ 59
def prefixEnd_2775011 : Nat := 4983230072969 + 3 ^ 40 * 2775011 * 2
def baseEnd_2775011 : Nat := 949942976342631660266975

theorem tailTrace_2775011 : CollatzResearch.WordTrace tailWord_2775011 prefixEnd_2775011 949942976342631660266975 := by
  unfold tailWord_2775011
  simp only [CollatzResearch.WordTrace]
  refine ⟨101212966149616555992084887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67475310766411037328056591 101212966149616555992084887)
  ·
    refine ⟨151819449224424833988127331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101212966149616555992084887 151819449224424833988127331)
    ·
      refine ⟨227729173836637250982190997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151819449224424833988127331 227729173836637250982190997)
      ·
        refine ⟨10674805023592371139790203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 227729173836637250982190997 10674805023592371139790203)
        ·
          refine ⟨16012207535388556709685305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10674805023592371139790203 16012207535388556709685305)
          ·
            refine ⟨12009155651541417532263979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16012207535388556709685305 12009155651541417532263979)
            ·
              refine ⟨18013733477312126298395969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12009155651541417532263979 18013733477312126298395969)
              ·
                refine ⟨13510300107984094723796977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18013733477312126298395969 13510300107984094723796977)
                ·
                  refine ⟨10132725080988071042847733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13510300107984094723796977 10132725080988071042847733)
                  ·
                    refine ⟨949942976342631660266975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10132725080988071042847733 949942976342631660266975)
                    ·
                      rfl

theorem cell22_2775011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_2775011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775011 prefixEnd_2775011 := by exact prefixLift 2775011
  have htrace : WordTrace (prefixWord ++ tailWord_2775011) baseStart_2775011 baseEnd_2775011 := by
    simpa [prefixWord, tailWord_2775011, baseEnd_2775011] using wordTrace_append hprefix tailTrace_2775011
  have hstable : (prefixWord ++ tailWord_2775011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775011).length < 2 ^ (prefixWord ++ tailWord_2775011).sum := by decide
  have hdescent : baseEnd_2775011 < baseStart_2775011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775041 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 6]
def baseStart_2775041 : Nat := 118140960795 + 2775041 * 2 ^ 59
def prefixEnd_2775041 : Nat := 4983230072969 + 3 ^ 40 * 2775041 * 2
def baseEnd_2775041 : Nat := 316651081985240527338961

theorem tailTrace_2775041 : CollatzResearch.WordTrace tailWord_2775041 prefixEnd_2775041 316651081985240527338961 := by
  unfold tailWord_2775041
  simp only [CollatzResearch.WordTrace]
  refine ⟨101214060339507871115676977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67476040226338580743784651 101214060339507871115676977)
  ·
    refine ⟨75910545254630903336757733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101214060339507871115676977 75910545254630903336757733)
    ·
      refine ⟨14233227235243294375642075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75910545254630903336757733 14233227235243294375642075)
      ·
        refine ⟨21349840852864941563463113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14233227235243294375642075 21349840852864941563463113)
        ·
          refine ⟨16012380639648706172597335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21349840852864941563463113 16012380639648706172597335)
          ·
            refine ⟨24018570959473059258896003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16012380639648706172597335 24018570959473059258896003)
            ·
              refine ⟨36027856439209588888344005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24018570959473059258896003 36027856439209588888344005)
              ·
                refine ⟨6755223082351797916564501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36027856439209588888344005 6755223082351797916564501)
                ·
                  refine ⟨316651081985240527338961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6755223082351797916564501 316651081985240527338961)
                  ·
                    rfl

theorem cell22_2775041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_2775041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775041 prefixEnd_2775041 := by exact prefixLift 2775041
  have htrace : WordTrace (prefixWord ++ tailWord_2775041) baseStart_2775041 baseEnd_2775041 := by
    simpa [prefixWord, tailWord_2775041, baseEnd_2775041] using wordTrace_append hprefix tailTrace_2775041
  have hstable : (prefixWord ++ tailWord_2775041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775041).length < 2 ^ (prefixWord ++ tailWord_2775041).sum := by decide
  have hdescent : baseEnd_2775041 < baseStart_2775041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775075 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 4]
def baseStart_2775075 : Nat := 118140960795 + 2775075 * 2 ^ 59
def prefixEnd_2775075 : Nat := 4983230072969 + 3 ^ 40 * 2775075 * 2
def baseEnd_2775075 : Nat := 316654961616852275555593

theorem tailTrace_2775075 : CollatzResearch.WordTrace tailWord_2775075 prefixEnd_2775075 316654961616852275555593 := by
  unfold tailWord_2775075
  simp only [CollatzResearch.WordTrace]
  refine ⟨101215300421384694922414679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67476866947589796614943119 101215300421384694922414679)
  ·
    refine ⟨151822950632077042383622019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101215300421384694922414679 151822950632077042383622019)
    ·
      refine ⟨227734425948115563575433029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151822950632077042383622019 227734425948115563575433029)
      ·
        refine ⟨42700204865271668170393693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227734425948115563575433029 42700204865271668170393693)
        ·
          refine ⟨16012576824476875563897635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42700204865271668170393693 16012576824476875563897635)
          ·
            refine ⟨24018865236715313345846453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16012576824476875563897635 24018865236715313345846453)
            ·
              refine ⟨2251768615942060626173105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24018865236715313345846453 2251768615942060626173105)
              ·
                refine ⟨1688826461956545469629829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251768615942060626173105 1688826461956545469629829)
                ·
                  refine ⟨316654961616852275555593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688826461956545469629829 316654961616852275555593)
                  ·
                    rfl

theorem cell22_2775075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 4].length) (baseStart_2775075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775075 prefixEnd_2775075 := by exact prefixLift 2775075
  have htrace : WordTrace (prefixWord ++ tailWord_2775075) baseStart_2775075 baseEnd_2775075 := by
    simpa [prefixWord, tailWord_2775075, baseEnd_2775075] using wordTrace_append hprefix tailTrace_2775075
  have hstable : (prefixWord ++ tailWord_2775075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775075).length < 2 ^ (prefixWord ++ tailWord_2775075).sum := by decide
  have hdescent : baseEnd_2775075 < baseStart_2775075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775090 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2775090 : Nat := 118140960795 + 2775090 * 2 ^ 59
def prefixEnd_2775090 : Nat := 4983230072969 + 3 ^ 40 * 2775090 * 2
def baseEnd_2775090 : Nat := 949970019657101787541733

theorem tailTrace_2775090 : CollatzResearch.WordTrace tailWord_2775090 prefixEnd_2775090 949970019657101787541733 := by
  unfold tailWord_2775090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25303961879082588121052681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67477231677553568322807149 25303961879082588121052681)
  ·
    refine ⟨18977971409311941090789511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25303961879082588121052681 18977971409311941090789511)
    ·
      refine ⟨28466957113967911636184267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18977971409311941090789511 28466957113967911636184267)
      ·
        refine ⟨42700435670951867454276401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28466957113967911636184267 42700435670951867454276401)
        ·
          refine ⟨32025326753213900590707301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42700435670951867454276401 32025326753213900590707301)
          ·
            refine ⟨6004748766227606360757619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32025326753213900590707301 6004748766227606360757619)
            ·
              refine ⟨9007123149341409541136429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004748766227606360757619 9007123149341409541136429)
              ·
                refine ⟨3377671181003028577926161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9007123149341409541136429 3377671181003028577926161)
                ·
                  refine ⟨2533253385752271433444621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3377671181003028577926161 2533253385752271433444621)
                  ·
                    refine ⟨949970019657101787541733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533253385752271433444621 949970019657101787541733)
                    ·
                      rfl

theorem cell22_2775090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2775090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775090 prefixEnd_2775090 := by exact prefixLift 2775090
  have htrace : WordTrace (prefixWord ++ tailWord_2775090) baseStart_2775090 baseEnd_2775090 := by
    simpa [prefixWord, tailWord_2775090, baseEnd_2775090] using wordTrace_append hprefix tailTrace_2775090
  have hstable : (prefixWord ++ tailWord_2775090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775090).length < 2 ^ (prefixWord ++ tailWord_2775090).sum := by decide
  have hdescent : baseEnd_2775090 < baseStart_2775090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775105 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2775105 : Nat := 118140960795 + 2775105 * 2 ^ 59
def prefixEnd_2775105 : Nat := 4983230072969 + 3 ^ 40 * 2775105 * 2
def baseEnd_2775105 : Nat := 949975154463646748416687

theorem tailTrace_2775105 : CollatzResearch.WordTrace tailWord_2775105 prefixEnd_2775105 949975154463646748416687 := by
  unfold tailWord_2775105
  simp only [CollatzResearch.WordTrace]
  refine ⟨101216394611276010046006769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67477596407517340030671179 101216394611276010046006769)
  ·
    refine ⟨75912295958457007534505077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101216394611276010046006769 75912295958457007534505077)
    ·
      refine ⟨7116777746105344456359851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75912295958457007534505077 7116777746105344456359851)
      ·
        refine ⟨10675166619158016684539777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7116777746105344456359851 10675166619158016684539777)
        ·
          refine ⟨8006374964368512513404833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10675166619158016684539777 8006374964368512513404833)
          ·
            refine ⟨6004781223276384385053625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8006374964368512513404833 6004781223276384385053625)
            ·
              refine ⟨4503585917457288288790219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6004781223276384385053625 4503585917457288288790219)
              ·
                refine ⟨6755378876185932433185329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503585917457288288790219 6755378876185932433185329)
                ·
                  refine ⟨5066534157139449324888997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6755378876185932433185329 5066534157139449324888997)
                  ·
                    refine ⟨949975154463646748416687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066534157139449324888997 949975154463646748416687)
                    ·
                      rfl

theorem cell22_2775105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2775105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775105 prefixEnd_2775105 := by exact prefixLift 2775105
  have htrace : WordTrace (prefixWord ++ tailWord_2775105) baseStart_2775105 baseEnd_2775105 := by
    simpa [prefixWord, tailWord_2775105, baseEnd_2775105] using wordTrace_append hprefix tailTrace_2775105
  have hstable : (prefixWord ++ tailWord_2775105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775105).length < 2 ^ (prefixWord ++ tailWord_2775105).sum := by decide
  have hdescent : baseEnd_2775105 < baseStart_2775105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775126 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2775126 : Nat := 118140960795 + 2775126 * 2 ^ 59
def prefixEnd_2775126 : Nat := 4983230072969 + 3 ^ 40 * 2775126 * 2
def baseEnd_2775126 : Nat := 316660781064269897880541

theorem tailTrace_2775126 : CollatzResearch.WordTrace tailWord_2775126 prefixEnd_2775126 316660781064269897880541 := by
  unfold tailWord_2775126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326072534012495664532577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67478107029466620421680821 6326072534012495664532577)
  ·
    refine ⟨4744554400509371748399433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6326072534012495664532577 4744554400509371748399433)
    ·
      refine ⟨3558415800382028811299575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4744554400509371748399433 3558415800382028811299575)
      ·
        refine ⟨5337623700573043216949363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558415800382028811299575 5337623700573043216949363)
        ·
          refine ⟨8006435550859564825424045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337623700573043216949363 8006435550859564825424045)
          ·
            refine ⟨3002413331572336809534017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8006435550859564825424045 3002413331572336809534017)
            ·
              refine ⟨2251809998679252607150513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002413331572336809534017 2251809998679252607150513)
              ·
                refine ⟨1688857499009439455362885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251809998679252607150513 1688857499009439455362885)
                ·
                  refine ⟨316660781064269897880541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688857499009439455362885 316660781064269897880541)
                  ·
                    rfl

theorem cell22_2775126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2775126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775126 prefixEnd_2775126 := by exact prefixLift 2775126
  have htrace : WordTrace (prefixWord ++ tailWord_2775126) baseStart_2775126 baseEnd_2775126 := by
    simpa [prefixWord, tailWord_2775126, baseEnd_2775126] using wordTrace_append hprefix tailTrace_2775126
  have hstable : (prefixWord ++ tailWord_2775126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775126).length < 2 ^ (prefixWord ++ tailWord_2775126).sum := by decide
  have hdescent : baseEnd_2775126 < baseStart_2775126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775148 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_2775148 : Nat := 118140960795 + 2775148 * 2 ^ 59
def prefixEnd_2775148 : Nat := 4983230072969 + 3 ^ 40 * 2775148 * 2
def baseEnd_2775148 : Nat := 316663291414136323197185

theorem tailTrace_2775148 : CollatzResearch.WordTrace tailWord_2775148 prefixEnd_2775148 316663291414136323197185 := by
  unfold tailWord_2775148
  simp only [CollatzResearch.WordTrace]
  refine ⟨50608981475060114194911049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67478641966746818926548065 50608981475060114194911049)
  ·
    refine ⟨37956736106295085646183287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50608981475060114194911049 37956736106295085646183287)
    ·
      refine ⟨56935104159442628469274931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37956736106295085646183287 56935104159442628469274931)
      ·
        refine ⟨85402656239163942703912397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56935104159442628469274931 85402656239163942703912397)
        ·
          refine ⟨32025996089686478513967149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85402656239163942703912397 32025996089686478513967149)
          ·
            refine ⟨12009748533632429442737681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32025996089686478513967149 12009748533632429442737681)
            ·
              refine ⟨9007311400224322082053261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12009748533632429442737681 9007311400224322082053261)
              ·
                refine ⟨3377741775084120780769973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9007311400224322082053261 3377741775084120780769973)
                ·
                  refine ⟨316663291414136323197185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3377741775084120780769973 316663291414136323197185)
                  ·
                    rfl

theorem cell22_2775148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_2775148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775148 prefixEnd_2775148 := by exact prefixLift 2775148
  have htrace : WordTrace (prefixWord ++ tailWord_2775148) baseStart_2775148 baseEnd_2775148 := by
    simpa [prefixWord, tailWord_2775148, baseEnd_2775148] using wordTrace_append hprefix tailTrace_2775148
  have hstable : (prefixWord ++ tailWord_2775148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775148).length < 2 ^ (prefixWord ++ tailWord_2775148).sum := by decide
  have hdescent : baseEnd_2775148 < baseStart_2775148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775169 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2775169 : Nat := 118140960795 + 2775169 * 2 ^ 59
def prefixEnd_2775169 : Nat := 4983230072969 + 3 ^ 40 * 2775169 * 2
def baseEnd_2775169 : Nat := 949997062971571914816491

theorem tailTrace_2775169 : CollatzResearch.WordTrace tailWord_2775169 prefixEnd_2775169 949997062971571914816491 := by
  unfold tailWord_2775169
  simp only [CollatzResearch.WordTrace]
  refine ⟨101218728883044148976336561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67479152588696099317557707 101218728883044148976336561)
  ·
    refine ⟨75914046662283111732252421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101218728883044148976336561 75914046662283111732252421)
    ·
      refine ⟨14233883749178083449797329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75914046662283111732252421 14233883749178083449797329)
      ·
        refine ⟨10675412811883562587347997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14233883749178083449797329 10675412811883562587347997)
        ·
          refine ⟨4003279804456335970255499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10675412811883562587347997 4003279804456335970255499)
          ·
            refine ⟨6004919706684503955383249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003279804456335970255499 6004919706684503955383249)
            ·
              refine ⟨4503689780013377966537437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6004919706684503955383249 4503689780013377966537437)
              ·
                refine ⟨1688883667505016737451539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4503689780013377966537437 1688883667505016737451539)
                ·
                  refine ⟨2533325501257525106177309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688883667505016737451539 2533325501257525106177309)
                  ·
                    refine ⟨949997062971571914816491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533325501257525106177309 949997062971571914816491)
                    ·
                      rfl

theorem cell22_2775169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2775169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775169 prefixEnd_2775169 := by exact prefixLift 2775169
  have htrace : WordTrace (prefixWord ++ tailWord_2775169) baseStart_2775169 baseEnd_2775169 := by
    simpa [prefixWord, tailWord_2775169, baseEnd_2775169] using wordTrace_append hprefix tailTrace_2775169
  have hstable : (prefixWord ++ tailWord_2775169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775169).length < 2 ^ (prefixWord ++ tailWord_2775169).sum := by decide
  have hdescent : baseEnd_2775169 < baseStart_2775169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775182 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_2775182 : Nat := 118140960795 + 2775182 * 2 ^ 59
def prefixEnd_2775182 : Nat := 4983230072969 + 3 ^ 40 * 2775182 * 2
def baseEnd_2775182 : Nat := 316667171045748071413817

theorem tailTrace_2775182 : CollatzResearch.WordTrace tailWord_2775182 prefixEnd_2775182 316667171045748071413817 := by
  unfold tailWord_2775182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12652400378999631524569975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67479468687998034797706533 12652400378999631524569975)
  ·
    refine ⟨18978600568499447286854963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12652400378999631524569975 18978600568499447286854963)
    ·
      refine ⟨28467900852749170930282445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18978600568499447286854963 28467900852749170930282445)
      ·
        refine ⟨10675462819780939098855917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28467900852749170930282445 10675462819780939098855917)
        ·
          refine ⟨4003298557417852162070969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10675462819780939098855917 4003298557417852162070969)
          ·
            refine ⟨3002473918063389121553227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4003298557417852162070969 3002473918063389121553227)
            ·
              refine ⟨4503710877095083682329841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002473918063389121553227 4503710877095083682329841)
              ·
                refine ⟨3377783157821312761747381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4503710877095083682329841 3377783157821312761747381)
                ·
                  refine ⟨316667171045748071413817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3377783157821312761747381 316667171045748071413817)
                  ·
                    rfl

theorem cell22_2775182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_2775182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775182 prefixEnd_2775182 := by exact prefixLift 2775182
  have htrace : WordTrace (prefixWord ++ tailWord_2775182) baseStart_2775182 baseEnd_2775182 := by
    simpa [prefixWord, tailWord_2775182, baseEnd_2775182] using wordTrace_append hprefix tailTrace_2775182
  have hstable : (prefixWord ++ tailWord_2775182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775182).length < 2 ^ (prefixWord ++ tailWord_2775182).sum := by decide
  have hdescent : baseEnd_2775182 < baseStart_2775182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775220 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2775220 : Nat := 118140960795 + 2775220 * 2 ^ 59
def prefixEnd_2775220 : Nat := 4983230072969 + 3 ^ 40 * 2775220 * 2
def baseEnd_2775220 : Nat := 950014521313824781791335

theorem tailTrace_2775220 : CollatzResearch.WordTrace tailWord_2775220 prefixEnd_2775220 950014521313824781791335 := by
  unfold tailWord_2775220
  simp only [CollatzResearch.WordTrace]
  refine ⟨50610294502929692343221557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67480392670572923124295409 50610294502929692343221557)
  ·
    refine ⟨4744715109649658657177021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50610294502929692343221557 4744715109649658657177021)
    ·
      refine ⟨1779268166118621996441383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4744715109649658657177021 1779268166118621996441383)
      ·
        refine ⟨2668902249177932994662075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779268166118621996441383 2668902249177932994662075)
        ·
          refine ⟨4003353373766899491993113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668902249177932994662075 4003353373766899491993113)
          ·
            refine ⟨3002515030325174618994835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4003353373766899491993113 3002515030325174618994835)
            ·
              refine ⟨4503772545487761928492253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002515030325174618994835 4503772545487761928492253)
              ·
                refine ⟨1688914704557910723184595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4503772545487761928492253 1688914704557910723184595)
                ·
                  refine ⟨2533372056836866084776893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688914704557910723184595 2533372056836866084776893)
                  ·
                    refine ⟨950014521313824781791335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533372056836866084776893 950014521313824781791335)
                    ·
                      rfl

theorem cell22_2775220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2775220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775220 prefixEnd_2775220 := by exact prefixLift 2775220
  have htrace : WordTrace (prefixWord ++ tailWord_2775220) baseStart_2775220 baseEnd_2775220 := by
    simpa [prefixWord, tailWord_2775220, baseEnd_2775220] using wordTrace_append hprefix tailTrace_2775220
  have hstable : (prefixWord ++ tailWord_2775220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775220).length < 2 ^ (prefixWord ++ tailWord_2775220).sum := by decide
  have hdescent : baseEnd_2775220 < baseStart_2775220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775223 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 1, 6]
def baseStart_2775223 : Nat := 118140960795 + 2775223 * 2 ^ 59
def prefixEnd_2775223 : Nat := 4983230072969 + 3 ^ 40 * 2775223 * 2
def baseEnd_2775223 : Nat := 950015548275133773966325

theorem tailTrace_2775223 : CollatzResearch.WordTrace tailWord_2775223 prefixEnd_2775223 950015548275133773966325 := by
  unfold tailWord_2775223
  simp only [CollatzResearch.WordTrace]
  refine ⟨101220698424848516198802323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67480465616565677465868215 101220698424848516198802323)
  ·
    refine ⟨151831047637272774298203485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101220698424848516198802323 151831047637272774298203485)
    ·
      refine ⟨56936642863977290361826307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151831047637272774298203485 56936642863977290361826307)
      ·
        refine ⟨85404964295965935542739461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56936642863977290361826307 85404964295965935542739461)
        ·
          refine ⟨16013430805493612914263649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85404964295965935542739461 16013430805493612914263649)
          ·
            refine ⟨12010073104120209685697737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16013430805493612914263649 12010073104120209685697737)
            ·
              refine ⟨9007554828090157264273303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12010073104120209685697737 9007554828090157264273303)
              ·
                refine ⟨13511332242135235896409955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007554828090157264273303 13511332242135235896409955)
                ·
                  refine ⟨20266998363202853844614933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13511332242135235896409955 20266998363202853844614933)
                  ·
                    refine ⟨950015548275133773966325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20266998363202853844614933 950015548275133773966325)
                    ·
                      rfl

theorem cell22_2775223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_2775223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775223 prefixEnd_2775223 := by exact prefixLift 2775223
  have htrace : WordTrace (prefixWord ++ tailWord_2775223) baseStart_2775223 baseEnd_2775223 := by
    simpa [prefixWord, tailWord_2775223, baseEnd_2775223] using wordTrace_append hprefix tailTrace_2775223
  have hstable : (prefixWord ++ tailWord_2775223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775223).length < 2 ^ (prefixWord ++ tailWord_2775223).sum := by decide
  have hdescent : baseEnd_2775223 < baseStart_2775223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775244 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 6]
def baseStart_2775244 : Nat := 118140960795 + 2775244 * 2 ^ 59
def prefixEnd_2775244 : Nat := 4983230072969 + 3 ^ 40 * 2775244 * 2
def baseEnd_2775244 : Nat := 316674245668098906397087

theorem tailTrace_2775244 : CollatzResearch.WordTrace tailWord_2775244 prefixEnd_2775244 316674245668098906397087 := by
  unfold tailWord_2775244
  simp only [CollatzResearch.WordTrace]
  refine ⟨50610732178886218392658393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67480976238514957856877857 50610732178886218392658393)
  ·
    refine ⟨37958049134164663794493795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50610732178886218392658393 37958049134164663794493795)
    ·
      refine ⟨56937073701246995691740693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37958049134164663794493795 56937073701246995691740693)
      ·
        refine ⟨2668925329745952923050345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56937073701246995691740693 2668925329745952923050345)
        ·
          refine ⟨2001693997309464692287759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2668925329745952923050345 2001693997309464692287759)
          ·
            refine ⟨3002540995964197038431639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001693997309464692287759 3002540995964197038431639)
            ·
              refine ⟨4503811493946295557647459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002540995964197038431639 4503811493946295557647459)
              ·
                refine ⟨6755717240919443336471189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503811493946295557647459 6755717240919443336471189)
                ·
                  refine ⟨316674245668098906397087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6755717240919443336471189 316674245668098906397087)
                  ·
                    rfl

theorem cell22_2775244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_2775244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775244 prefixEnd_2775244 := by exact prefixLift 2775244
  have htrace : WordTrace (prefixWord ++ tailWord_2775244) baseStart_2775244 baseEnd_2775244 := by
    simpa [prefixWord, tailWord_2775244, baseEnd_2775244] using wordTrace_append hprefix tailTrace_2775244
  have hstable : (prefixWord ++ tailWord_2775244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775244).length < 2 ^ (prefixWord ++ tailWord_2775244).sum := by decide
  have hdescent : baseEnd_2775244 < baseStart_2775244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775304 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 1, 3]
def baseStart_2775304 : Nat := 118140960795 + 2775304 * 2 ^ 59
def prefixEnd_2775304 : Nat := 4983230072969 + 3 ^ 40 * 2775304 * 2
def baseEnd_2775304 : Nat := 950043276230476562691077

theorem tailTrace_2775304 : CollatzResearch.WordTrace tailWord_2775304 prefixEnd_2775304 950043276230476562691077 := by
  unfold tailWord_2775304
  simp only [CollatzResearch.WordTrace]
  refine ⟨50611826368777533516250483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67482435158370044688333977 50611826368777533516250483)
  ·
    refine ⟨75917739553166300274375725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50611826368777533516250483 75917739553166300274375725)
    ·
      refine ⟨28469152332437362602890897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75917739553166300274375725 28469152332437362602890897)
      ·
        refine ⟨21351864249328021952168173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28469152332437362602890897 21351864249328021952168173)
        ·
          refine ⟨8006949093498008232063065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21351864249328021952168173 8006949093498008232063065)
          ·
            refine ⟨6005211820123506174047299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8006949093498008232063065 6005211820123506174047299)
            ·
              refine ⟨9007817730185259261070949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005211820123506174047299 9007817730185259261070949)
              ·
                refine ⟨1688965824409736111450803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9007817730185259261070949 1688965824409736111450803)
                ·
                  refine ⟨2533448736614604167176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688965824409736111450803 2533448736614604167176205)
                  ·
                    refine ⟨950043276230476562691077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533448736614604167176205 950043276230476562691077)
                    ·
                      rfl

theorem cell22_2775304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_2775304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775304 prefixEnd_2775304 := by exact prefixLift 2775304
  have htrace : WordTrace (prefixWord ++ tailWord_2775304) baseStart_2775304 baseEnd_2775304 := by
    simpa [prefixWord, tailWord_2775304, baseEnd_2775304] using wordTrace_append hprefix tailTrace_2775304
  have hstable : (prefixWord ++ tailWord_2775304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775304).length < 2 ^ (prefixWord ++ tailWord_2775304).sum := by decide
  have hdescent : baseEnd_2775304 < baseStart_2775304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775377 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_2775377 : Nat := 118140960795 + 2775377 * 2 ^ 59
def prefixEnd_2775377 : Nat := 4983230072969 + 3 ^ 40 * 2775377 * 2
def baseEnd_2775377 : Nat := 950068265622328705615853

theorem tailTrace_2775377 : CollatzResearch.WordTrace tailWord_2775377 prefixEnd_2775377 950068265622328705615853 := by
  unfold tailWord_2775377
  simp only [CollatzResearch.WordTrace]
  refine ⟨101226315266290600499908385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67484210177527066999938923 101226315266290600499908385)
  ·
    refine ⟨75919736449717950374931289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101226315266290600499908385 75919736449717950374931289)
    ·
      refine ⟨56939802337288462781198467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75919736449717950374931289 56939802337288462781198467)
      ·
        refine ⟨85409703505932694171797701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56939802337288462781198467 85409703505932694171797701)
        ·
          refine ⟨16014319407362380157212069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85409703505932694171797701 16014319407362380157212069)
          ·
            refine ⟨3002684888880446279477263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16014319407362380157212069 3002684888880446279477263)
            ·
              refine ⟨4504027333320669419215895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002684888880446279477263 4504027333320669419215895)
              ·
                refine ⟨6756040999981004128823843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504027333320669419215895 6756040999981004128823843)
                ·
                  refine ⟨10134061499971506193235765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6756040999981004128823843 10134061499971506193235765)
                  ·
                    refine ⟨950068265622328705615853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10134061499971506193235765 950068265622328705615853)
                    ·
                      rfl

theorem cell22_2775377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_2775377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775377 prefixEnd_2775377 := by exact prefixLift 2775377
  have htrace : WordTrace (prefixWord ++ tailWord_2775377) baseStart_2775377 baseEnd_2775377 := by
    simpa [prefixWord, tailWord_2775377, baseEnd_2775377] using wordTrace_append hprefix tailTrace_2775377
  have hstable : (prefixWord ++ tailWord_2775377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775377).length < 2 ^ (prefixWord ++ tailWord_2775377).sum := by decide
  have hdescent : baseEnd_2775377 < baseStart_2775377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775473 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 1, 3]
def baseStart_2775473 : Nat := 118140960795 + 2775473 * 2 ^ 59
def prefixEnd_2775473 : Nat := 4983230072969 + 3 ^ 40 * 2775473 * 2
def baseEnd_2775473 : Nat := 950101128384216455215559

theorem tailTrace_2775473 : CollatzResearch.WordTrace tailWord_2775473 prefixEnd_2775473 950101128384216455215559 := by
  unfold tailWord_2775473
  simp only [CollatzResearch.WordTrace]
  refine ⟨101229816673942808895403073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67486544449295205930268715 101229816673942808895403073)
  ·
    refine ⟨75922362505457106671552305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101229816673942808895403073 75922362505457106671552305)
    ·
      refine ⟨56941771879092830003664229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75922362505457106671552305 56941771879092830003664229)
      ·
        refine ⟨10676582227329905625687043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56941771879092830003664229 10676582227329905625687043)
        ·
          refine ⟨16014873340994858438530565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10676582227329905625687043 16014873340994858438530565)
          ·
            refine ⟨3002788751436535957224481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16014873340994858438530565 3002788751436535957224481)
            ·
              refine ⟨2252091563577401967918361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002788751436535957224481 2252091563577401967918361)
              ·
                refine ⟨1689068672683051475938771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252091563577401967918361 1689068672683051475938771)
                ·
                  refine ⟨2533603009024577213908157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689068672683051475938771 2533603009024577213908157)
                  ·
                    refine ⟨950101128384216455215559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533603009024577213908157 950101128384216455215559)
                    ·
                      rfl

theorem cell22_2775473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_2775473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775473 prefixEnd_2775473 := by exact prefixLift 2775473
  have htrace : WordTrace (prefixWord ++ tailWord_2775473) baseStart_2775473 baseEnd_2775473 := by
    simpa [prefixWord, tailWord_2775473, baseEnd_2775473] using wordTrace_append hprefix tailTrace_2775473
  have hstable : (prefixWord ++ tailWord_2775473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775473).length < 2 ^ (prefixWord ++ tailWord_2775473).sum := by decide
  have hdescent : baseEnd_2775473 < baseStart_2775473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775480 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_2775480 : Nat := 118140960795 + 2775480 * 2 ^ 59
def prefixEnd_2775480 : Nat := 4983230072969 + 3 ^ 40 * 2775480 * 2
def baseEnd_2775480 : Nat := 316701174875756923430179

theorem tailTrace_2775480 : CollatzResearch.WordTrace tailWord_2775480 prefixEnd_2775480 316701174875756923430179 := by
  unfold tailWord_2775480
  simp only [CollatzResearch.WordTrace]
  refine ⟨50615035992458724545453947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67486714656611632727271929 50615035992458724545453947)
  ·
    refine ⟨75922553988688086818180921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50615035992458724545453947 75922553988688086818180921)
    ·
      refine ⟨56941915491516065113635691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75922553988688086818180921 56941915491516065113635691)
      ·
        refine ⟨85412873237274097670453537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56941915491516065113635691 85412873237274097670453537)
        ·
          refine ⟨64059654927955573252840153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85412873237274097670453537 64059654927955573252840153)
          ·
            refine ⟨48044741195966679939630115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64059654927955573252840153 48044741195966679939630115)
            ·
              refine ⟨72067111793950019909445173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48044741195966679939630115 72067111793950019909445173)
              ·
                refine ⟨6756291730682814366510485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72067111793950019909445173 6756291730682814366510485)
                ·
                  refine ⟨316701174875756923430179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6756291730682814366510485 316701174875756923430179)
                  ·
                    rfl

theorem cell22_2775480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_2775480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775480 prefixEnd_2775480 := by exact prefixLift 2775480
  have htrace : WordTrace (prefixWord ++ tailWord_2775480) baseStart_2775480 baseEnd_2775480 := by
    simpa [prefixWord, tailWord_2775480, baseEnd_2775480] using wordTrace_append hprefix tailTrace_2775480
  have hstable : (prefixWord ++ tailWord_2775480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775480).length < 2 ^ (prefixWord ++ tailWord_2775480).sum := by decide
  have hdescent : baseEnd_2775480 < baseStart_2775480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775512 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_2775512 : Nat := 118140960795 + 2775512 * 2 ^ 59
def prefixEnd_2775512 : Nat := 4983230072969 + 3 ^ 40 * 2775512 * 2
def baseEnd_2775512 : Nat := 950114478881233353490439

theorem tailTrace_2775512 : CollatzResearch.WordTrace tailWord_2775512 prefixEnd_2775512 950114478881233353490439 := by
  unfold tailWord_2775512
  simp only [CollatzResearch.WordTrace]
  refine ⟨50615619560400759278036395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67487492747201012370715193 50615619560400759278036395)
  ·
    refine ⟨75923429340601138917054593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50615619560400759278036395 75923429340601138917054593)
    ·
      refine ⟨56942572005450854187790945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75923429340601138917054593 56942572005450854187790945)
      ·
        refine ⟨42706929004088140640843209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56942572005450854187790945 42706929004088140640843209)
        ·
          refine ⟨32030196753066105480632407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42706929004088140640843209 32030196753066105480632407)
          ·
            refine ⟨48045295129599158220948611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32030196753066105480632407 48045295129599158220948611)
            ·
              refine ⟨72067942694398737331422917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48045295129599158220948611 72067942694398737331422917)
              ·
                refine ⟨13512739255199763249641797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72067942694398737331422917 13512739255199763249641797)
                ·
                  refine ⟨2533638610349955609307837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13512739255199763249641797 2533638610349955609307837)
                  ·
                    refine ⟨950114478881233353490439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533638610349955609307837 950114478881233353490439)
                    ·
                      rfl

theorem cell22_2775512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_2775512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775512 prefixEnd_2775512 := by exact prefixLift 2775512
  have htrace : WordTrace (prefixWord ++ tailWord_2775512) baseStart_2775512 baseEnd_2775512 := by
    simpa [prefixWord, tailWord_2775512, baseEnd_2775512] using wordTrace_append hprefix tailTrace_2775512
  have hstable : (prefixWord ++ tailWord_2775512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775512).length < 2 ^ (prefixWord ++ tailWord_2775512).sum := by decide
  have hdescent : baseEnd_2775512 < baseStart_2775512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775514 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_2775514 : Nat := 118140960795 + 2775514 * 2 ^ 59
def prefixEnd_2775514 : Nat := 4983230072969 + 3 ^ 40 * 2775514 * 2
def baseEnd_2775514 : Nat := 316705054507368671646811

theorem tailTrace_2775514 : CollatzResearch.WordTrace tailWord_2775514 prefixEnd_2775514 316705054507368671646811 := by
  unfold tailWord_2775514
  simp only [CollatzResearch.WordTrace]
  refine ⟨25307828016698568224411399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67487541377862848598430397 25307828016698568224411399)
  ·
    refine ⟨37961742025047852336617099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25307828016698568224411399 37961742025047852336617099)
    ·
      refine ⟨56942613037571778504925649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37961742025047852336617099 56942613037571778504925649)
      ·
        refine ⟨42706959778178833878694237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56942613037571778504925649 42706959778178833878694237)
        ·
          refine ⟨16015109916817062704510339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42706959778178833878694237 16015109916817062704510339)
          ·
            refine ⟨24022664875225594056765509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16015109916817062704510339 24022664875225594056765509)
            ·
              refine ⟨4504249664104798885643533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24022664875225594056765509 4504249664104798885643533)
              ·
                refine ⟨1689093624039299582116325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4504249664104798885643533 1689093624039299582116325)
                ·
                  refine ⟨316705054507368671646811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1689093624039299582116325 316705054507368671646811)
                  ·
                    rfl

theorem cell22_2775514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_2775514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775514 prefixEnd_2775514 := by exact prefixLift 2775514
  have htrace : WordTrace (prefixWord ++ tailWord_2775514) baseStart_2775514 baseEnd_2775514 := by
    simpa [prefixWord, tailWord_2775514, baseEnd_2775514] using wordTrace_append hprefix tailTrace_2775514
  have hstable : (prefixWord ++ tailWord_2775514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775514).length < 2 ^ (prefixWord ++ tailWord_2775514).sum := by decide
  have hdescent : baseEnd_2775514 < baseStart_2775514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775527 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2775527 : Nat := 118140960795 + 2775527 * 2 ^ 59
def prefixEnd_2775527 : Nat := 4983230072969 + 3 ^ 40 * 2775527 * 2
def baseEnd_2775527 : Nat := 950119613687778314365393

theorem tailTrace_2775527 : CollatzResearch.WordTrace tailWord_2775527 prefixEnd_2775527 950119613687778314365393 := by
  unfold tailWord_2775527
  simp only [CollatzResearch.WordTrace]
  refine ⟨101231786215747176117868835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67487857477164784078579223 101231786215747176117868835)
  ·
    refine ⟨151847679323620764176803253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101231786215747176117868835 151847679323620764176803253)
    ·
      refine ⟨14235719936589446641575305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151847679323620764176803253 14235719936589446641575305)
      ·
        refine ⟨10676789952442084981181479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14235719936589446641575305 10676789952442084981181479)
        ·
          refine ⟨16015184928663127471772219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10676789952442084981181479 16015184928663127471772219)
          ·
            refine ⟨24022777392994691207658329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16015184928663127471772219 24022777392994691207658329)
            ·
              refine ⟨18017083044746018405743747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24022777392994691207658329 18017083044746018405743747)
              ·
                refine ⟨27025624567119027608615621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18017083044746018405743747 27025624567119027608615621)
                ·
                  refine ⟨5067304606334817676615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27025624567119027608615621 5067304606334817676615429)
                  ·
                    refine ⟨950119613687778314365393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067304606334817676615429 950119613687778314365393)
                    ·
                      rfl

theorem cell22_2775527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2775527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775527 prefixEnd_2775527 := by exact prefixLift 2775527
  have htrace : WordTrace (prefixWord ++ tailWord_2775527) baseStart_2775527 baseEnd_2775527 := by
    simpa [prefixWord, tailWord_2775527, baseEnd_2775527] using wordTrace_append hprefix tailTrace_2775527
  have hstable : (prefixWord ++ tailWord_2775527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775527).length < 2 ^ (prefixWord ++ tailWord_2775527).sum := by decide
  have hdescent : baseEnd_2775527 < baseStart_2775527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775542 : List Nat := [5, 1, 1, 1, 2, 1, 2, 9]
def baseStart_2775542 : Nat := 118140960795 + 2775542 * 2 ^ 59
def prefixEnd_2775542 : Nat := 4983230072969 + 3 ^ 40 * 2775542 * 2
def baseEnd_2775542 : Nat := 105569416499369252804483

theorem tailTrace_2775542 : CollatzResearch.WordTrace tailWord_2775542 prefixEnd_2775542 105569416499369252804483 := by
  unfold tailWord_2775542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327020831918302104979055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67488222207128555786443253 6327020831918302104979055)
  ·
    refine ⟨9490531247877453157468583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6327020831918302104979055 9490531247877453157468583)
    ·
      refine ⟨14235796871816179736202875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9490531247877453157468583 14235796871816179736202875)
      ·
        refine ⟨21353695307724269604304313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14235796871816179736202875 21353695307724269604304313)
        ·
          refine ⟨16015271480793202203228235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21353695307724269604304313 16015271480793202203228235)
          ·
            refine ⟨24022907221189803304842353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16015271480793202203228235 24022907221189803304842353)
            ·
              refine ⟨18017180415892352478631765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24022907221189803304842353 18017180415892352478631765)
              ·
                refine ⟨105569416499369252804483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18017180415892352478631765 105569416499369252804483)
                ·
                  rfl

theorem cell22_2775542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_2775542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775542 prefixEnd_2775542 := by exact prefixLift 2775542
  have htrace : WordTrace (prefixWord ++ tailWord_2775542) baseStart_2775542 baseEnd_2775542 := by
    simpa [prefixWord, tailWord_2775542, baseEnd_2775542] using wordTrace_append hprefix tailTrace_2775542
  have hstable : (prefixWord ++ tailWord_2775542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775542).length < 2 ^ (prefixWord ++ tailWord_2775542).sum := by decide
  have hdescent : baseEnd_2775542 < baseStart_2775542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775565 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2775565 : Nat := 118140960795 + 2775565 * 2 ^ 59
def prefixEnd_2775565 : Nat := 4983230072969 + 3 ^ 40 * 2775565 * 2
def baseEnd_2775565 : Nat := 316710873954786293971759

theorem tailTrace_2775565 : CollatzResearch.WordTrace tailWord_2775565 prefixEnd_2775565 316710873954786293971759 := by
  unfold tailWord_2775565
  simp only [CollatzResearch.WordTrace]
  refine ⟨101233172189609508607752149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67488781459739672405168099 101233172189609508607752149)
  ·
    refine ⟨2372652473193972857994191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 101233172189609508607752149 2372652473193972857994191)
    ·
      refine ⟨3558978709790959286991287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372652473193972857994191 3558978709790959286991287)
      ·
        refine ⟨5338468064686438930486931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558978709790959286991287 5338468064686438930486931)
        ·
          refine ⟨8007702097029658395730397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5338468064686438930486931 8007702097029658395730397)
          ·
            refine ⟨3002888286386121898398899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8007702097029658395730397 3002888286386121898398899)
            ·
              refine ⟨4504332429579182847598349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002888286386121898398899 4504332429579182847598349)
              ·
                refine ⟨1689124661092193567849381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4504332429579182847598349 1689124661092193567849381)
                ·
                  refine ⟨316710873954786293971759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1689124661092193567849381 316710873954786293971759)
                  ·
                    rfl

theorem cell22_2775565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2775565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775565 prefixEnd_2775565 := by exact prefixLift 2775565
  have htrace : WordTrace (prefixWord ++ tailWord_2775565) baseStart_2775565 baseEnd_2775565 := by
    simpa [prefixWord, tailWord_2775565, baseEnd_2775565] using wordTrace_append hprefix tailTrace_2775565
  have hstable : (prefixWord ++ tailWord_2775565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775565).length < 2 ^ (prefixWord ++ tailWord_2775565).sum := by decide
  have hdescent : baseEnd_2775565 < baseStart_2775565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775587 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 7]
def baseStart_2775587 : Nat := 118140960795 + 2775587 * 2 ^ 59
def prefixEnd_2775587 : Nat := 4983230072969 + 3 ^ 40 * 2775587 * 2
def baseEnd_2775587 : Nat := 316713384304652719288403

theorem tailTrace_2775587 : CollatzResearch.WordTrace tailWord_2775587 prefixEnd_2775587 316713384304652719288403 := by
  unfold tailWord_2775587
  simp only [CollatzResearch.WordTrace]
  refine ⟨101233974595529806365053015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67489316397019870910035343 101233974595529806365053015)
  ·
    refine ⟨151850961893294709547579523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101233974595529806365053015 151850961893294709547579523)
    ·
      refine ⟨227776442839942064321369285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151850961893294709547579523 227776442839942064321369285)
      ·
        refine ⟨42708083032489137060256741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227776442839942064321369285 42708083032489137060256741)
        ·
          refine ⟨8007765568591713198798139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42708083032489137060256741 8007765568591713198798139)
          ·
            refine ⟨12011648352887569798197209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8007765568591713198798139 12011648352887569798197209)
            ·
              refine ⟨9008736264665677348647907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12011648352887569798197209 9008736264665677348647907)
              ·
                refine ⟨13513104396998516022971861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9008736264665677348647907 13513104396998516022971861)
                ·
                  refine ⟨316713384304652719288403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13513104396998516022971861 316713384304652719288403)
                  ·
                    rfl

theorem cell22_2775587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_2775587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775587 prefixEnd_2775587 := by exact prefixLift 2775587
  have htrace : WordTrace (prefixWord ++ tailWord_2775587) baseStart_2775587 baseEnd_2775587 := by
    simpa [prefixWord, tailWord_2775587, baseEnd_2775587] using wordTrace_append hprefix tailTrace_2775587
  have hstable : (prefixWord ++ tailWord_2775587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775587).length < 2 ^ (prefixWord ++ tailWord_2775587).sum := by decide
  have hdescent : baseEnd_2775587 < baseStart_2775587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775602 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2775602 : Nat := 118140960795 + 2775602 * 2 ^ 59
def prefixEnd_2775602 : Nat := 4983230072969 + 3 ^ 40 * 2775602 * 2
def baseEnd_2775602 : Nat := 950145287720503118740163

theorem tailTrace_2775602 : CollatzResearch.WordTrace tailWord_2775602 prefixEnd_2775602 950145287720503118740163 := by
  unfold tailWord_2775602
  simp only [CollatzResearch.WordTrace]
  refine ⟨25308630422618865981712265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67489681126983642617899373 25308630422618865981712265)
  ·
    refine ⟨18981472816964149486284199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25308630422618865981712265 18981472816964149486284199)
    ·
      refine ⟨28472209225446224229426299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18981472816964149486284199 28472209225446224229426299)
      ·
        refine ⟨42708313838169336344139449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28472209225446224229426299 42708313838169336344139449)
        ·
          refine ⟨32031235378627002258104587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42708313838169336344139449 32031235378627002258104587)
          ·
            refine ⟨48046853067940503387156881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32031235378627002258104587 48046853067940503387156881)
            ·
              refine ⟨36035139800955377540367661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48046853067940503387156881 36035139800955377540367661)
              ·
                refine ⟨13513177425358266577637873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36035139800955377540367661 13513177425358266577637873)
                ·
                  refine ⟨10134883069018699933228405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13513177425358266577637873 10134883069018699933228405)
                  ·
                    refine ⟨950145287720503118740163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10134883069018699933228405 950145287720503118740163)
                    ·
                      rfl

theorem cell22_2775602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2775602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775602 prefixEnd_2775602 := by exact prefixLift 2775602
  have htrace : WordTrace (prefixWord ++ tailWord_2775602) baseStart_2775602 baseEnd_2775602 := by
    simpa [prefixWord, tailWord_2775602, baseEnd_2775602] using wordTrace_append hprefix tailTrace_2775602
  have hstable : (prefixWord ++ tailWord_2775602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775602).length < 2 ^ (prefixWord ++ tailWord_2775602).sum := by decide
  have hdescent : baseEnd_2775602 < baseStart_2775602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775698 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2775698 : Nat := 118140960795 + 2775698 * 2 ^ 59
def prefixEnd_2775698 : Nat := 4983230072969 + 3 ^ 40 * 2775698 * 2
def baseEnd_2775698 : Nat := 950178150482390868339869

theorem tailTrace_2775698 : CollatzResearch.WordTrace tailWord_2775698 prefixEnd_2775698 950178150482390868339869 := by
  unfold tailWord_2775698
  simp only [CollatzResearch.WordTrace]
  refine ⟨25309505774531918080585937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67492015398751781548229165 25309505774531918080585937)
  ·
    refine ⟨18982129330898938560439453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25309505774531918080585937 18982129330898938560439453)
    ·
      refine ⟨7118298499087101960164795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18982129330898938560439453 7118298499087101960164795)
      ·
        refine ⟨10677447748630652940247193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7118298499087101960164795 10677447748630652940247193)
        ·
          refine ⟨8008085811472989705185395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10677447748630652940247193 8008085811472989705185395)
          ·
            refine ⟨12012128717209484557778093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008085811472989705185395 12012128717209484557778093)
            ·
              refine ⟨4504548268953556709166785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12012128717209484557778093 4504548268953556709166785)
              ·
                refine ⟨3378411201715167531875089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4504548268953556709166785 3378411201715167531875089)
                ·
                  refine ⟨2533808401286375648906317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3378411201715167531875089 2533808401286375648906317)
                  ·
                    refine ⟨950178150482390868339869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533808401286375648906317 950178150482390868339869)
                    ·
                      rfl

theorem cell22_2775698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2775698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775698 prefixEnd_2775698 := by exact prefixLift 2775698
  have htrace : WordTrace (prefixWord ++ tailWord_2775698) baseStart_2775698 baseEnd_2775698 := by
    simpa [prefixWord, tailWord_2775698, baseEnd_2775698] using wordTrace_append hprefix tailTrace_2775698
  have hstable : (prefixWord ++ tailWord_2775698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775698).length < 2 ^ (prefixWord ++ tailWord_2775698).sum := by decide
  have hdescent : baseEnd_2775698 < baseStart_2775698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775743 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 1, 3]
def baseStart_2775743 : Nat := 118140960795 + 2775743 * 2 ^ 59
def prefixEnd_2775743 : Nat := 4983230072969 + 3 ^ 40 * 2775743 * 2
def baseEnd_2775743 : Nat := 950193554902025750964731

theorem tailTrace_2775743 : CollatzResearch.WordTrace tailWord_2775743 prefixEnd_2775743 950193554902025750964731 := by
  unfold tailWord_2775743
  simp only [CollatzResearch.WordTrace]
  refine ⟨101239664382964645007731883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67493109588643096671821255 101239664382964645007731883)
  ·
    refine ⟨151859496574446967511597825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101239664382964645007731883 151859496574446967511597825)
    ·
      refine ⟨113894622430835225633698369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151859496574446967511597825 113894622430835225633698369)
      ·
        refine ⟨85420966823126419225273777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113894622430835225633698369 85420966823126419225273777)
        ·
          refine ⟨64065725117344814418955333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85420966823126419225273777 64065725117344814418955333)
          ·
            refine ⟨12012323459502152703554125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64065725117344814418955333 12012323459502152703554125)
            ·
              refine ⟨4504621297313307263832797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12012323459502152703554125 4504621297313307263832797)
              ·
                refine ⟨1689232986492490223937299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4504621297313307263832797 1689232986492490223937299)
                ·
                  refine ⟨2533849479738735335905949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689232986492490223937299 2533849479738735335905949)
                  ·
                    refine ⟨950193554902025750964731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533849479738735335905949 950193554902025750964731)
                    ·
                      rfl

theorem cell22_2775743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_2775743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775743 prefixEnd_2775743 := by exact prefixLift 2775743
  have htrace : WordTrace (prefixWord ++ tailWord_2775743) baseStart_2775743 baseEnd_2775743 := by
    simpa [prefixWord, tailWord_2775743, baseEnd_2775743] using wordTrace_append hprefix tailTrace_2775743
  have hstable : (prefixWord ++ tailWord_2775743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775743).length < 2 ^ (prefixWord ++ tailWord_2775743).sum := by decide
  have hdescent : baseEnd_2775743 < baseStart_2775743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775769 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_2775769 : Nat := 118140960795 + 2775769 * 2 ^ 59
def prefixEnd_2775769 : Nat := 4983230072969 + 3 ^ 40 * 2775769 * 2
def baseEnd_2775769 : Nat := 950202455233370349814651

theorem tailTrace_2775769 : CollatzResearch.WordTrace tailWord_2775769 prefixEnd_2775769 950202455233370349814651 := by
  unfold tailWord_2775769
  simp only [CollatzResearch.WordTrace]
  refine ⟨101240612680870451448178361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67493741787246967632118907 101240612680870451448178361)
  ·
    refine ⟨75930459510652838586133771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101240612680870451448178361 75930459510652838586133771)
    ·
      refine ⟨113895689265979257879200657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75930459510652838586133771 113895689265979257879200657)
      ·
        refine ⟨85421766949484443409400493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113895689265979257879200657 85421766949484443409400493)
        ·
          refine ⟨32033162606056666278525185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85421766949484443409400493 32033162606056666278525185)
          ·
            refine ⟨24024871954542499708893889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32033162606056666278525185 24024871954542499708893889)
            ·
              refine ⟨18018653965906874781670417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24024871954542499708893889 18018653965906874781670417)
              ·
                refine ⟨13513990474430156086252813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18018653965906874781670417 13513990474430156086252813)
                ·
                  refine ⟨5067746427911308532344805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13513990474430156086252813 5067746427911308532344805)
                  ·
                    refine ⟨950202455233370349814651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067746427911308532344805 950202455233370349814651)
                    ·
                      rfl

theorem cell22_2775769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_2775769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775769 prefixEnd_2775769 := by exact prefixLift 2775769
  have htrace : WordTrace (prefixWord ++ tailWord_2775769) baseStart_2775769 baseEnd_2775769 := by
    simpa [prefixWord, tailWord_2775769, baseEnd_2775769] using wordTrace_append hprefix tailTrace_2775769
  have hstable : (prefixWord ++ tailWord_2775769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775769).length < 2 ^ (prefixWord ++ tailWord_2775769).sum := by decide
  have hdescent : baseEnd_2775769 < baseStart_2775769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775912 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 1, 3]
def baseStart_2775912 : Nat := 118140960795 + 2775912 * 2 ^ 59
def prefixEnd_2775912 : Nat := 4983230072969 + 3 ^ 40 * 2775912 * 2
def baseEnd_2775912 : Nat := 950251407055765643489213

theorem tailTrace_2775912 : CollatzResearch.WordTrace tailWord_2775912 prefixEnd_2775912 950251407055765643489213 := by
  unfold tailWord_2775912
  simp only [CollatzResearch.WordTrace]
  refine ⟨50622914159676193435316995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67497218879568257913755993 50622914159676193435316995)
  ·
    refine ⟨75934371239514290152975493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50622914159676193435316995 75934371239514290152975493)
    ·
      refine ⟨14237694607408929403682905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75934371239514290152975493 14237694607408929403682905)
      ·
        refine ⟨10678270955556697052762179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14237694607408929403682905 10678270955556697052762179)
        ·
          refine ⟨16017406433335045579143269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10678270955556697052762179 16017406433335045579143269)
          ·
            refine ⟨3003263706250321046089363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16017406433335045579143269 3003263706250321046089363)
            ·
              refine ⟨4504895559375481569134045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003263706250321046089363 4504895559375481569134045)
              ·
                refine ⟨1689335834765805588425267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4504895559375481569134045 1689335834765805588425267)
                ·
                  refine ⟨2534003752148708382637901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689335834765805588425267 2534003752148708382637901)
                  ·
                    refine ⟨950251407055765643489213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534003752148708382637901 950251407055765643489213)
                    ·
                      rfl

theorem cell22_2775912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_2775912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775912 prefixEnd_2775912 := by exact prefixLift 2775912
  have htrace : WordTrace (prefixWord ++ tailWord_2775912) baseStart_2775912 baseEnd_2775912 := by
    simpa [prefixWord, tailWord_2775912, baseEnd_2775912] using wordTrace_append hprefix tailTrace_2775912
  have hstable : (prefixWord ++ tailWord_2775912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775912).length < 2 ^ (prefixWord ++ tailWord_2775912).sum := by decide
  have hdescent : baseEnd_2775912 < baseStart_2775912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775919 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 8]
def baseStart_2775919 : Nat := 118140960795 + 2775919 * 2 ^ 59
def prefixEnd_2775919 : Nat := 4983230072969 + 3 ^ 40 * 2775919 * 2
def baseEnd_2775919 : Nat := 316751267766273319521397

theorem tailTrace_2775919 : CollatzResearch.WordTrace tailWord_2775919 prefixEnd_2775919 316751267766273319521397 := by
  unfold tailWord_2775919
  simp only [CollatzResearch.WordTrace]
  refine ⟨101246083630327027066138811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67497389086884684710759207 101246083630327027066138811)
  ·
    refine ⟨151869125445490540599208217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101246083630327027066138811 151869125445490540599208217)
    ·
      refine ⟨113901844084117905449406163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151869125445490540599208217 113901844084117905449406163)
      ·
        refine ⟨170852766126176858174109245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113901844084117905449406163 170852766126176858174109245)
        ·
          refine ⟨64069787297316321815290967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170852766126176858174109245 64069787297316321815290967)
          ·
            refine ⟨96104680945974482722936451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64069787297316321815290967 96104680945974482722936451)
            ·
              refine ⟨144157021418961724084404677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96104680945974482722936451 144157021418961724084404677)
              ·
                refine ⟨27029441516055323265825877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144157021418961724084404677 27029441516055323265825877)
                ·
                  refine ⟨316751267766273319521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27029441516055323265825877 316751267766273319521397)
                  ·
                    rfl

theorem cell22_2775919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_2775919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775919 prefixEnd_2775919 := by exact prefixLift 2775919
  have htrace : WordTrace (prefixWord ++ tailWord_2775919) baseStart_2775919 baseEnd_2775919 := by
    simpa [prefixWord, tailWord_2775919, baseEnd_2775919] using wordTrace_append hprefix tailTrace_2775919
  have hstable : (prefixWord ++ tailWord_2775919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775919).length < 2 ^ (prefixWord ++ tailWord_2775919).sum := by decide
  have hdescent : baseEnd_2775919 < baseStart_2775919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776060 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 5]
def baseStart_2776060 : Nat := 118140960795 + 2776060 * 2 ^ 59
def prefixEnd_2776060 : Nat := 4983230072969 + 3 ^ 40 * 2776060 * 2
def baseEnd_2776060 : Nat := 316767356826780863596253

theorem tailTrace_2776060 : CollatzResearch.WordTrace tailWord_2776060 prefixEnd_2776060 316767356826780863596253 := by
  unfold tailWord_2776060
  simp only [CollatzResearch.WordTrace]
  refine ⟨50625613161408104073510817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67500817548544138764681089 50625613161408104073510817)
  ·
    refine ⟨37969209871056078055133113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50625613161408104073510817 37969209871056078055133113)
    ·
      refine ⟨28476907403292058541349835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37969209871056078055133113 28476907403292058541349835)
      ·
        refine ⟨42715361104938087812024753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28476907403292058541349835 42715361104938087812024753)
        ·
          refine ⟨32036520828703565859018565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42715361104938087812024753 32036520828703565859018565)
          ·
            refine ⟨6006847655381918598565981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32036520828703565859018565 6006847655381918598565981)
            ·
              refine ⟨2252567870768219474462243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6006847655381918598565981 2252567870768219474462243)
              ·
                refine ⟨3378851806152329211693365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252567870768219474462243 3378851806152329211693365)
                ·
                  refine ⟨316767356826780863596253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3378851806152329211693365 316767356826780863596253)
                  ·
                    rfl

theorem cell22_2776060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_2776060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776060 prefixEnd_2776060 := by exact prefixLift 2776060
  have htrace : WordTrace (prefixWord ++ tailWord_2776060) baseStart_2776060 baseEnd_2776060 := by
    simpa [prefixWord, tailWord_2776060, baseEnd_2776060] using wordTrace_append hprefix tailTrace_2776060
  have hstable : (prefixWord ++ tailWord_2776060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776060).length < 2 ^ (prefixWord ++ tailWord_2776060).sum := by decide
  have hdescent : baseEnd_2776060 < baseStart_2776060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776135 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2776135 : Nat := 118140960795 + 2776135 * 2 ^ 59
def prefixEnd_2776135 : Nat := 4983230072969 + 3 ^ 40 * 2776135 * 2
def baseEnd_2776135 : Nat := 950327744513067395163529

theorem tailTrace_2776135 : CollatzResearch.WordTrace tailWord_2776135 prefixEnd_2776135 950327744513067395163529 := by
  unfold tailWord_2776135
  simp only [CollatzResearch.WordTrace]
  refine ⟨101253961797544495956001859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67502641198362997304001239 101253961797544495956001859)
  ·
    refine ⟨151880942696316743934002789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101253961797544495956001859 151880942696316743934002789)
    ·
      refine ⟨28477676755559389487625523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151880942696316743934002789 28477676755559389487625523)
      ·
        refine ⟨42716515133339084231438285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28477676755559389487625523 42716515133339084231438285)
        ·
          refine ⟨16018693175002156586789357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42716515133339084231438285 16018693175002156586789357)
          ·
            refine ⟨6007009940625808720046009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16018693175002156586789357 6007009940625808720046009)
            ·
              refine ⟨4505257455469356540034507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6007009940625808720046009 4505257455469356540034507)
              ·
                refine ⟨6757886183204034810051761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4505257455469356540034507 6757886183204034810051761)
                ·
                  refine ⟨5068414637403026107538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757886183204034810051761 5068414637403026107538821)
                  ·
                    refine ⟨950327744513067395163529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5068414637403026107538821 950327744513067395163529)
                    ·
                      rfl

theorem cell22_2776135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2776135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776135 prefixEnd_2776135 := by exact prefixLift 2776135
  have htrace : WordTrace (prefixWord ++ tailWord_2776135) baseStart_2776135 baseEnd_2776135 := by
    simpa [prefixWord, tailWord_2776135, baseEnd_2776135] using wordTrace_append hprefix tailTrace_2776135
  have hstable : (prefixWord ++ tailWord_2776135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776135).length < 2 ^ (prefixWord ++ tailWord_2776135).sum := by decide
  have hdescent : baseEnd_2776135 < baseStart_2776135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776150 : List Nat := [5, 2, 2, 1, 12]
def baseStart_2776150 : Nat := 118140960795 + 2776150 * 2 ^ 59
def prefixEnd_2776150 : Nat := 4983230072969 + 3 ^ 40 * 2776150 * 2
def baseEnd_2776150 : Nat := 3910834894319392411681

theorem tailTrace_2776150 : CollatzResearch.WordTrace tailWord_2776150 prefixEnd_2776150 3910834894319392411681 := by
  unfold tailWord_2776150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328406805780634594862369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67503005928326769011865269 6328406805780634594862369)
  ·
    refine ⟨4746305104335475946146777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6328406805780634594862369 4746305104335475946146777)
    ·
      refine ⟨3559728828251606959610083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4746305104335475946146777 3559728828251606959610083)
      ·
        refine ⟨5339593242377410439415125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3559728828251606959610083 5339593242377410439415125)
        ·
          refine ⟨3910834894319392411681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5339593242377410439415125 3910834894319392411681)
          ·
            rfl

theorem cell22_2776150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 12].length) (baseStart_2776150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776150 prefixEnd_2776150 := by exact prefixLift 2776150
  have htrace : WordTrace (prefixWord ++ tailWord_2776150) baseStart_2776150 baseEnd_2776150 := by
    simpa [prefixWord, tailWord_2776150, baseEnd_2776150] using wordTrace_append hprefix tailTrace_2776150
  have hstable : (prefixWord ++ tailWord_2776150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776150).length < 2 ^ (prefixWord ++ tailWord_2776150).sum := by decide
  have hdescent : baseEnd_2776150 < baseStart_2776150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776165 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_2776165 : Nat := 118140960795 + 2776165 * 2 ^ 59
def prefixEnd_2776165 : Nat := 4983230072969 + 3 ^ 40 * 2776165 * 2
def baseEnd_2776165 : Nat := 950338014126157316913437

theorem tailTrace_2776165 : CollatzResearch.WordTrace tailWord_2776165 prefixEnd_2776165 950338014126157316913437 := by
  unfold tailWord_2776165
  simp only [CollatzResearch.WordTrace]
  refine ⟨101255055987435811079593949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67503370658290540719729299 101255055987435811079593949)
  ·
    refine ⟨37970645995288429154847731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101255055987435811079593949 37970645995288429154847731)
    ·
      refine ⟨56955968992932643732271597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37970645995288429154847731 56955968992932643732271597)
      ·
        refine ⟨21358488372349741399601849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56955968992932643732271597 21358488372349741399601849)
        ·
          refine ⟨16018866279262306049701387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21358488372349741399601849 16018866279262306049701387)
          ·
            refine ⟨24028299418893459074552081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16018866279262306049701387 24028299418893459074552081)
            ·
              refine ⟨18021224564170094305914061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24028299418893459074552081 18021224564170094305914061)
              ·
                refine ⟨6757959211563785364717773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18021224564170094305914061 6757959211563785364717773)
                ·
                  refine ⟨2534234704336419511769165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6757959211563785364717773 2534234704336419511769165)
                  ·
                    refine ⟨950338014126157316913437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534234704336419511769165 950338014126157316913437)
                    ·
                      rfl

theorem cell22_2776165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_2776165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776165 prefixEnd_2776165 := by exact prefixLift 2776165
  have htrace : WordTrace (prefixWord ++ tailWord_2776165) baseStart_2776165 baseEnd_2776165 := by
    simpa [prefixWord, tailWord_2776165, baseEnd_2776165] using wordTrace_append hprefix tailTrace_2776165
  have hstable : (prefixWord ++ tailWord_2776165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776165).length < 2 ^ (prefixWord ++ tailWord_2776165).sum := by decide
  have hdescent : baseEnd_2776165 < baseStart_2776165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776182 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_2776182 : Nat := 118140960795 + 2776182 * 2 ^ 59
def prefixEnd_2776182 : Nat := 4983230072969 + 3 ^ 40 * 2776182 * 2
def baseEnd_2776182 : Nat := 950343833573574939238385

theorem tailTrace_2776182 : CollatzResearch.WordTrace tailWord_2776182 prefixEnd_2776182 950343833573574939238385 := by
  unfold tailWord_2776182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328479751773388936435175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67503784018916148655308533 6328479751773388936435175)
  ·
    refine ⟨9492719627660083404652763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6328479751773388936435175 9492719627660083404652763)
    ·
      refine ⟨14239079441490125106979145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492719627660083404652763 14239079441490125106979145)
      ·
        refine ⟨10679309581117593830234359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14239079441490125106979145 10679309581117593830234359)
        ·
          refine ⟨16018964371676390745351539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10679309581117593830234359 16018964371676390745351539)
          ·
            refine ⟨24028446557514586118027309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16018964371676390745351539 24028446557514586118027309)
            ·
              refine ⟨9010667459067969794260241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24028446557514586118027309 9010667459067969794260241)
              ·
                refine ⟨6758000594300977345695181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9010667459067969794260241 6758000594300977345695181)
                ·
                  refine ⟨2534250222862866504635693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6758000594300977345695181 2534250222862866504635693)
                  ·
                    refine ⟨950343833573574939238385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534250222862866504635693 950343833573574939238385)
                    ·
                      rfl

theorem cell22_2776182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_2776182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776182 prefixEnd_2776182 := by exact prefixLift 2776182
  have htrace : WordTrace (prefixWord ++ tailWord_2776182) baseStart_2776182 baseEnd_2776182 := by
    simpa [prefixWord, tailWord_2776182, baseEnd_2776182] using wordTrace_append hprefix tailTrace_2776182
  have hstable : (prefixWord ++ tailWord_2776182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776182).length < 2 ^ (prefixWord ++ tailWord_2776182).sum := by decide
  have hdescent : baseEnd_2776182 < baseStart_2776182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776208 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_2776208 : Nat := 118140960795 + 2776208 * 2 ^ 59
def prefixEnd_2776208 : Nat := 4983230072969 + 3 ^ 40 * 2776208 * 2
def baseEnd_2776208 : Nat := 950352733904919538088305

theorem tailTrace_2776208 : CollatzResearch.WordTrace tailWord_2776208 prefixEnd_2776208 950352733904919538088305 := by
  unfold tailWord_2776208
  simp only [CollatzResearch.WordTrace]
  refine ⟨50628312163140014711704639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67504416217520019615606185 50628312163140014711704639)
  ·
    refine ⟨75942468244710022067556959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50628312163140014711704639 75942468244710022067556959)
    ·
      refine ⟨113913702367065033101335439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75942468244710022067556959 113913702367065033101335439)
      ·
        refine ⟨170870553550597549652003159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113913702367065033101335439 170870553550597549652003159)
        ·
          refine ⟨256305830325896324478004739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170870553550597549652003159 256305830325896324478004739)
          ·
            refine ⟨384458745488844486717007109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256305830325896324478004739 384458745488844486717007109)
            ·
              refine ⟨72086014779158341259438833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 384458745488844486717007109 72086014779158341259438833)
              ·
                refine ⟨54064511084368755944579125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72086014779158341259438833 54064511084368755944579125)
                ·
                  refine ⟨5068547914159570869804293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54064511084368755944579125 5068547914159570869804293)
                  ·
                    refine ⟨950352733904919538088305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5068547914159570869804293 950352733904919538088305)
                    ·
                      rfl

theorem cell22_2776208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_2776208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776208 prefixEnd_2776208 := by exact prefixLift 2776208
  have htrace : WordTrace (prefixWord ++ tailWord_2776208) baseStart_2776208 baseEnd_2776208 := by
    simpa [prefixWord, tailWord_2776208, baseEnd_2776208] using wordTrace_append hprefix tailTrace_2776208
  have hstable : (prefixWord ++ tailWord_2776208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776208).length < 2 ^ (prefixWord ++ tailWord_2776208).sum := by decide
  have hdescent : baseEnd_2776208 < baseStart_2776208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776210 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2776210 : Nat := 118140960795 + 2776210 * 2 ^ 59
def prefixEnd_2776210 : Nat := 4983230072969 + 3 ^ 40 * 2776210 * 2
def baseEnd_2776210 : Nat := 950353418545792199538299

theorem tailTrace_2776210 : CollatzResearch.WordTrace tailWord_2776210 prefixEnd_2776210 950353418545792199538299 := by
  unfold tailWord_2776210
  simp only [CollatzResearch.WordTrace]
  refine ⟨25314174318068195941245521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67504464848181855843321389 25314174318068195941245521)
  ·
    refine ⟨18985630738551146955934141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25314174318068195941245521 18985630738551146955934141)
    ·
      refine ⟨7119611526956680108475303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18985630738551146955934141 7119611526956680108475303)
      ·
        refine ⟨10679417290435020162712955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7119611526956680108475303 10679417290435020162712955)
        ·
          refine ⟨16019125935652530244069433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10679417290435020162712955 16019125935652530244069433)
          ·
            refine ⟨12014344451739397683052075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16019125935652530244069433 12014344451739397683052075)
            ·
              refine ⟨18021516677609096524578113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12014344451739397683052075 18021516677609096524578113)
              ·
                refine ⟨13516137508206822393433585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18021516677609096524578113 13516137508206822393433585)
                ·
                  refine ⟨10137103131155116795075189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13516137508206822393433585 10137103131155116795075189)
                  ·
                    refine ⟨950353418545792199538299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10137103131155116795075189 950353418545792199538299)
                    ·
                      rfl

theorem cell22_2776210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2776210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776210 prefixEnd_2776210 := by exact prefixLift 2776210
  have htrace : WordTrace (prefixWord ++ tailWord_2776210) baseStart_2776210 baseEnd_2776210 := by
    simpa [prefixWord, tailWord_2776210, baseEnd_2776210] using wordTrace_append hprefix tailTrace_2776210
  have hstable : (prefixWord ++ tailWord_2776210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776210).length < 2 ^ (prefixWord ++ tailWord_2776210).sum := by decide
  have hdescent : baseEnd_2776210 < baseStart_2776210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776242 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2776242 : Nat := 118140960795 + 2776242 * 2 ^ 59
def prefixEnd_2776242 : Nat := 4983230072969 + 3 ^ 40 * 2776242 * 2
def baseEnd_2776242 : Nat := 950364372799754782738201

theorem tailTrace_2776242 : CollatzResearch.WordTrace tailWord_2776242 prefixEnd_2776242 950364372799754782738201 := by
  unfold tailWord_2776242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25314466102039213307536745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67505242938771235486764653 25314466102039213307536745)
  ·
    refine ⟨18985849576529409980652559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25314466102039213307536745 18985849576529409980652559)
    ·
      refine ⟨28478774364794114970978839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18985849576529409980652559 28478774364794114970978839)
      ·
        refine ⟨42718161547191172456468259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28478774364794114970978839 42718161547191172456468259)
        ·
          refine ⟨64077242320786758684702389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42718161547191172456468259 64077242320786758684702389)
          ·
            refine ⟨6007241467573758626690849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64077242320786758684702389 6007241467573758626690849)
            ·
              refine ⟨4505431100680318970018137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6007241467573758626690849 4505431100680318970018137)
              ·
                refine ⟨3379073325510239227513603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4505431100680318970018137 3379073325510239227513603)
                ·
                  refine ⟨5068609988265358841270405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379073325510239227513603 5068609988265358841270405)
                  ·
                    refine ⟨950364372799754782738201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5068609988265358841270405 950364372799754782738201)
                    ·
                      rfl

theorem cell22_2776242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2776242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776242 prefixEnd_2776242 := by exact prefixLift 2776242
  have htrace : WordTrace (prefixWord ++ tailWord_2776242) baseStart_2776242 baseEnd_2776242 := by
    simpa [prefixWord, tailWord_2776242, baseEnd_2776242] using wordTrace_append hprefix tailTrace_2776242
  have hstable : (prefixWord ++ tailWord_2776242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776242).length < 2 ^ (prefixWord ++ tailWord_2776242).sum := by decide
  have hdescent : baseEnd_2776242 < baseStart_2776242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776255 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 4, 3]
def baseStart_2776255 : Nat := 118140960795 + 2776255 * 2 ^ 59
def prefixEnd_2776255 : Nat := 4983230072969 + 3 ^ 40 * 2776255 * 2
def baseEnd_2776255 : Nat := 950368822965427082163161

theorem tailTrace_2776255 : CollatzResearch.WordTrace tailWord_2776255 prefixEnd_2776255 950368822965427082163161 := by
  unfold tailWord_2776255
  simp only [CollatzResearch.WordTrace]
  refine ⟨101258338557109756450370219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67505559038073170966913479 101258338557109756450370219)
  ·
    refine ⟨151887507835664634675555329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101258338557109756450370219 151887507835664634675555329)
    ·
      refine ⟨113915630876748476006666497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151887507835664634675555329 113915630876748476006666497)
      ·
        refine ⟨85436723157561357004999873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113915630876748476006666497 85436723157561357004999873)
        ·
          refine ⟨64077542368171017753749905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85436723157561357004999873 64077542368171017753749905)
          ·
            refine ⟨48058156776128263315312429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64077542368171017753749905 48058156776128263315312429)
            ·
              refine ⟨18021808791048098743242161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48058156776128263315312429 18021808791048098743242161)
              ·
                refine ⟨13516356593286074057431621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18021808791048098743242161 13516356593286074057431621)
                ·
                  refine ⟨2534316861241138885768429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13516356593286074057431621 2534316861241138885768429)
                  ·
                    refine ⟨950368822965427082163161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534316861241138885768429 950368822965427082163161)
                    ·
                      rfl

theorem cell22_2776255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_2776255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776255 prefixEnd_2776255 := by exact prefixLift 2776255
  have htrace : WordTrace (prefixWord ++ tailWord_2776255) baseStart_2776255 baseEnd_2776255 := by
    simpa [prefixWord, tailWord_2776255, baseEnd_2776255] using wordTrace_append hprefix tailTrace_2776255
  have hstable : (prefixWord ++ tailWord_2776255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776255).length < 2 ^ (prefixWord ++ tailWord_2776255).sum := by decide
  have hdescent : baseEnd_2776255 < baseStart_2776255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776274 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_2776274 : Nat := 118140960795 + 2776274 * 2 ^ 59
def prefixEnd_2776274 : Nat := 4983230072969 + 3 ^ 40 * 2776274 * 2
def baseEnd_2776274 : Nat := 316791775684572455312701

theorem tailTrace_2776274 : CollatzResearch.WordTrace tailWord_2776274 prefixEnd_2776274 316791775684572455312701 := by
  unfold tailWord_2776274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25314757886010230673827969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67506021029360615130207917 25314757886010230673827969)
  ·
    refine ⟨18986068414507673005370977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25314757886010230673827969 18986068414507673005370977)
    ·
      refine ⟨14239551310880754754028233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18986068414507673005370977 14239551310880754754028233)
      ·
        refine ⟨10679663483160566065521175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14239551310880754754028233 10679663483160566065521175)
        ·
          refine ⟨16019495224740849098281763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10679663483160566065521175 16019495224740849098281763)
          ·
            refine ⟨24029242837111273647422645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16019495224740849098281763 24029242837111273647422645)
            ·
              refine ⟨2252741515979181904445873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24029242837111273647422645 2252741515979181904445873)
              ·
                refine ⟨1689556136984386428334405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252741515979181904445873 1689556136984386428334405)
                ·
                  refine ⟨316791775684572455312701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1689556136984386428334405 316791775684572455312701)
                  ·
                    rfl

theorem cell22_2776274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_2776274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776274 prefixEnd_2776274 := by exact prefixLift 2776274
  have htrace : WordTrace (prefixWord ++ tailWord_2776274) baseStart_2776274 baseEnd_2776274 := by
    simpa [prefixWord, tailWord_2776274, baseEnd_2776274] using wordTrace_append hprefix tailTrace_2776274
  have hstable : (prefixWord ++ tailWord_2776274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776274).length < 2 ^ (prefixWord ++ tailWord_2776274).sum := by decide
  have hdescent : baseEnd_2776274 < baseStart_2776274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776289 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 2, 3]
def baseStart_2776289 : Nat := 118140960795 + 2776289 * 2 ^ 59
def prefixEnd_2776289 : Nat := 4983230072969 + 3 ^ 40 * 2776289 * 2
def baseEnd_2776289 : Nat := 950380461860262326813057

theorem tailTrace_2776289 : CollatzResearch.WordTrace tailWord_2776289 prefixEnd_2776289 950380461860262326813057 := by
  unfold tailWord_2776289
  simp only [CollatzResearch.WordTrace]
  refine ⟨101259578638986580257107921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67506385759324386838071947 101259578638986580257107921)
  ·
    refine ⟨75944683979239935192830941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101259578638986580257107921 75944683979239935192830941)
    ·
      refine ⟨28479256492214975697311603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75944683979239935192830941 28479256492214975697311603)
      ·
        refine ⟨42718884738322463545967405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28479256492214975697311603 42718884738322463545967405)
        ·
          refine ⟨16019581776870923829737777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42718884738322463545967405 16019581776870923829737777)
          ·
            refine ⟨12014686332653192872303333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16019581776870923829737777 12014686332653192872303333)
            ·
              refine ⟨2252753687372473663556875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12014686332653192872303333 2252753687372473663556875)
              ·
                refine ⟨3379130531058710495335313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252753687372473663556875 3379130531058710495335313)
                ·
                  refine ⟨2534347898294032871501485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3379130531058710495335313 2534347898294032871501485)
                  ·
                    refine ⟨950380461860262326813057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534347898294032871501485 950380461860262326813057)
                    ·
                      rfl

theorem cell22_2776289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_2776289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776289 prefixEnd_2776289 := by exact prefixLift 2776289
  have htrace : WordTrace (prefixWord ++ tailWord_2776289) baseStart_2776289 baseEnd_2776289 := by
    simpa [prefixWord, tailWord_2776289, baseEnd_2776289] using wordTrace_append hprefix tailTrace_2776289
  have hstable : (prefixWord ++ tailWord_2776289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776289).length < 2 ^ (prefixWord ++ tailWord_2776289).sum := by decide
  have hdescent : baseEnd_2776289 < baseStart_2776289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776381 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 5]
def baseStart_2776381 : Nat := 118140960795 + 2776381 * 2 ^ 59
def prefixEnd_2776381 : Nat := 4983230072969 + 3 ^ 40 * 2776381 * 2
def baseEnd_2776381 : Nat := 316803985113468251170925

theorem tailTrace_2776381 : CollatzResearch.WordTrace tailWord_2776381 prefixEnd_2776381 316803985113468251170925 := by
  unfold tailWord_2776381
  simp only [CollatzResearch.WordTrace]
  refine ⟨101262934154653279969456997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67508622769768853312971331 101262934154653279969456997)
  ·
    refine ⟨18986800153997489994273187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101262934154653279969456997 18986800153997489994273187)
    ·
      refine ⟨28480200230996234991409781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18986800153997489994273187 28480200230996234991409781)
      ·
        refine ⟨2670018771655897030444667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28480200230996234991409781 2670018771655897030444667)
        ·
          refine ⟨4005028157483845545667001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670018771655897030444667 4005028157483845545667001)
          ·
            refine ⟨3003771118112884159250251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4005028157483845545667001 3003771118112884159250251)
            ·
              refine ⟨4505656677169326238875377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003771118112884159250251 4505656677169326238875377)
              ·
                refine ⟨3379242507876994679156533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4505656677169326238875377 3379242507876994679156533)
                ·
                  refine ⟨316803985113468251170925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3379242507876994679156533 316803985113468251170925)
                  ·
                    rfl

theorem cell22_2776381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_2776381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776381 prefixEnd_2776381 := by exact prefixLift 2776381
  have htrace : WordTrace (prefixWord ++ tailWord_2776381) baseStart_2776381 baseEnd_2776381 := by
    simpa [prefixWord, tailWord_2776381, baseEnd_2776381] using wordTrace_append hprefix tailTrace_2776381
  have hstable : (prefixWord ++ tailWord_2776381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776381).length < 2 ^ (prefixWord ++ tailWord_2776381).sum := by decide
  have hdescent : baseEnd_2776381 < baseStart_2776381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776407 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 1, 5]
def baseStart_2776407 : Nat := 118140960795 + 2776407 * 2 ^ 59
def prefixEnd_2776407 : Nat := 4983230072969 + 3 ^ 40 * 2776407 * 2
def baseEnd_2776407 : Nat := 950420855671749352362695

theorem tailTrace_2776407 : CollatzResearch.WordTrace tailWord_2776407 prefixEnd_2776407 950420855671749352362695 := by
  unfold tailWord_2776407
  simp only [CollatzResearch.WordTrace]
  refine ⟨101263882452559086409903475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67509254968372724273268983 101263882452559086409903475)
  ·
    refine ⟨151895823678838629614855213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101263882452559086409903475 151895823678838629614855213)
    ·
      refine ⟨56960933879564486105570705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151895823678838629614855213 56960933879564486105570705)
      ·
        refine ⟨42720700409673364579178029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56960933879564486105570705 42720700409673364579178029)
        ·
          refine ⟨16020262653627511717191761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42720700409673364579178029 16020262653627511717191761)
          ·
            refine ⟨12015196990220633787893821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16020262653627511717191761 12015196990220633787893821)
            ·
              refine ⟨4505698871332737670460183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12015196990220633787893821 4505698871332737670460183)
              ·
                refine ⟨6758548306999106505690275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4505698871332737670460183 6758548306999106505690275)
                ·
                  refine ⟨10137822460498659758535413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6758548306999106505690275 10137822460498659758535413)
                  ·
                    refine ⟨950420855671749352362695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10137822460498659758535413 950420855671749352362695)
                    ·
                      rfl

theorem cell22_2776407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_2776407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776407 prefixEnd_2776407 := by exact prefixLift 2776407
  have htrace : WordTrace (prefixWord ++ tailWord_2776407) baseStart_2776407 baseEnd_2776407 := by
    simpa [prefixWord, tailWord_2776407, baseEnd_2776407] using wordTrace_append hprefix tailTrace_2776407
  have hstable : (prefixWord ++ tailWord_2776407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776407).length < 2 ^ (prefixWord ++ tailWord_2776407).sum := by decide
  have hdescent : baseEnd_2776407 < baseStart_2776407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776497 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2776497 : Nat := 118140960795 + 2776497 * 2 ^ 59
def prefixEnd_2776497 : Nat := 4983230072969 + 3 ^ 40 * 2776497 * 2
def baseEnd_2776497 : Nat := 950451664511019117612419

theorem tailTrace_2776497 : CollatzResearch.WordTrace tailWord_2776497 prefixEnd_2776497 950451664511019117612419 := by
  unfold tailWord_2776497
  simp only [CollatzResearch.WordTrace]
  refine ⟨101267165022233031780679745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67511443348155354520453163 101267165022233031780679745)
  ·
    refine ⟨75950373766674773835509809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101267165022233031780679745 75950373766674773835509809)
    ·
      refine ⟨56962780325006080376632357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75950373766674773835509809 56962780325006080376632357)
      ·
        refine ⟨10680521310938640070618567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56962780325006080376632357 10680521310938640070618567)
        ·
          refine ⟨16020781966407960105927851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10680521310938640070618567 16020781966407960105927851)
          ·
            refine ⟨24031172949611940158891777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16020781966407960105927851 24031172949611940158891777)
            ·
              refine ⟨18023379712208955119168833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24031172949611940158891777 18023379712208955119168833)
              ·
                refine ⟨13517534784156716339376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18023379712208955119168833 13517534784156716339376625)
                ·
                  refine ⟨10138151088117537254532469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13517534784156716339376625 10138151088117537254532469)
                  ·
                    refine ⟨950451664511019117612419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10138151088117537254532469 950451664511019117612419)
                    ·
                      rfl

theorem cell22_2776497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2776497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776497 prefixEnd_2776497 := by exact prefixLift 2776497
  have htrace : WordTrace (prefixWord ++ tailWord_2776497) baseStart_2776497 baseEnd_2776497 := by
    simpa [prefixWord, tailWord_2776497, baseEnd_2776497] using wordTrace_append hprefix tailTrace_2776497
  have hstable : (prefixWord ++ tailWord_2776497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776497).length < 2 ^ (prefixWord ++ tailWord_2776497).sum := by decide
  have hdescent : baseEnd_2776497 < baseStart_2776497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776512 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_2776512 : Nat := 118140960795 + 2776512 * 2 ^ 59
def prefixEnd_2776512 : Nat := 4983230072969 + 3 ^ 40 * 2776512 * 2
def baseEnd_2776512 : Nat := 950456799317564078487373

theorem tailTrace_2776512 : CollatzResearch.WordTrace tailWord_2776512 prefixEnd_2776512 950456799317564078487373 := by
  unfold tailWord_2776512
  simp only [CollatzResearch.WordTrace]
  refine ⟨50633856058589344671237895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67511808078119126228317193 50633856058589344671237895)
  ·
    refine ⟨75950784087884017006856843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50633856058589344671237895 75950784087884017006856843)
    ·
      refine ⟨113926176131826025510285265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75950784087884017006856843 113926176131826025510285265)
      ·
        refine ⟨85444632098869519132713949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113926176131826025510285265 85444632098869519132713949)
        ·
          refine ⟨32041737037076069674767731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85444632098869519132713949 32041737037076069674767731)
          ·
            refine ⟨48062605555614104512151597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32041737037076069674767731 48062605555614104512151597)
            ·
              refine ⟨18023477083355289192056849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48062605555614104512151597 18023477083355289192056849)
              ·
                refine ⟨13517607812516466894042637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18023477083355289192056849 13517607812516466894042637)
                ·
                  refine ⟨5069102929693675085265989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13517607812516466894042637 5069102929693675085265989)
                  ·
                    refine ⟨950456799317564078487373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5069102929693675085265989 950456799317564078487373)
                    ·
                      rfl

theorem cell22_2776512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_2776512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776512 prefixEnd_2776512 := by exact prefixLift 2776512
  have htrace : WordTrace (prefixWord ++ tailWord_2776512) baseStart_2776512 baseEnd_2776512 := by
    simpa [prefixWord, tailWord_2776512, baseEnd_2776512] using wordTrace_append hprefix tailTrace_2776512
  have hstable : (prefixWord ++ tailWord_2776512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776512).length < 2 ^ (prefixWord ++ tailWord_2776512).sum := by decide
  have hdescent : baseEnd_2776512 < baseStart_2776512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776602 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2776602 : Nat := 118140960795 + 2776602 * 2 ^ 59
def prefixEnd_2776602 : Nat := 4983230072969 + 3 ^ 40 * 2776602 * 2
def baseEnd_2776602 : Nat := 950487608156833843737097

theorem tailTrace_2776602 : CollatzResearch.WordTrace tailWord_2776602 prefixEnd_2776602 950487608156833843737097 := by
  unfold tailWord_2776602
  simp only [CollatzResearch.WordTrace]
  refine ⟨25317748671713158678313015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67513996457901756475501373 25317748671713158678313015)
  ·
    refine ⟨37976623007569738017469523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25317748671713158678313015 37976623007569738017469523)
    ·
      refine ⟨56964934511354607026204285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37976623007569738017469523 56964934511354607026204285)
      ·
        refine ⟨21361850441757977634826607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56964934511354607026204285 21361850441757977634826607)
        ·
          refine ⟨32042775662636966452239911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21361850441757977634826607 32042775662636966452239911)
          ·
            refine ⟨48064163493955449678359867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32042775662636966452239911 48064163493955449678359867)
            ·
              refine ⟨72096245240933174517539801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48064163493955449678359867 72096245240933174517539801)
              ·
                refine ⟨54072183930699880888154851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72096245240933174517539801 54072183930699880888154851)
                ·
                  refine ⟨81108275896049821332232277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54072183930699880888154851 81108275896049821332232277)
                  ·
                    refine ⟨950487608156833843737097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81108275896049821332232277 950487608156833843737097)
                    ·
                      rfl

theorem cell22_2776602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2776602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776602 prefixEnd_2776602 := by exact prefixLift 2776602
  have htrace : WordTrace (prefixWord ++ tailWord_2776602) baseStart_2776602 baseEnd_2776602 := by
    simpa [prefixWord, tailWord_2776602, baseEnd_2776602] using wordTrace_append hprefix tailTrace_2776602
  have hstable : (prefixWord ++ tailWord_2776602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776602).length < 2 ^ (prefixWord ++ tailWord_2776602).sum := by decide
  have hdescent : baseEnd_2776602 < baseStart_2776602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776634 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_2776634 : Nat := 118140960795 + 2776634 * 2 ^ 59
def prefixEnd_2776634 : Nat := 4983230072969 + 3 ^ 40 * 2776634 * 2
def baseEnd_2776634 : Nat := 316832854136932142312333

theorem tailTrace_2776634 : CollatzResearch.WordTrace tailWord_2776634 prefixEnd_2776634 316832854136932142312333 := by
  unfold tailWord_2776634
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318040455684176044604239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67514774548491136118944637 25318040455684176044604239)
  ·
    refine ⟨37977060683526264066906359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25318040455684176044604239 37977060683526264066906359)
    ·
      refine ⟨56965591025289396100359539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37977060683526264066906359 56965591025289396100359539)
      ·
        refine ⟨85448386537934094150539309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56965591025289396100359539 85448386537934094150539309)
        ·
          refine ⟨32043144951725285306452241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85448386537934094150539309 32043144951725285306452241)
          ·
            refine ⟨24032358713793963979839181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32043144951725285306452241 24032358713793963979839181)
            ·
              refine ⟨9012134517672736492439693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24032358713793963979839181 9012134517672736492439693)
              ·
                refine ⟨3379550444127276184664885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9012134517672736492439693 3379550444127276184664885)
                ·
                  refine ⟨316832854136932142312333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3379550444127276184664885 316832854136932142312333)
                  ·
                    rfl

theorem cell22_2776634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_2776634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776634 prefixEnd_2776634 := by exact prefixLift 2776634
  have htrace : WordTrace (prefixWord ++ tailWord_2776634) baseStart_2776634 baseEnd_2776634 := by
    simpa [prefixWord, tailWord_2776634, baseEnd_2776634] using wordTrace_append hprefix tailTrace_2776634
  have hstable : (prefixWord ++ tailWord_2776634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776634).length < 2 ^ (prefixWord ++ tailWord_2776634).sum := by decide
  have hdescent : baseEnd_2776634 < baseStart_2776634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776709 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_2776709 : Nat := 118140960795 + 2776709 * 2 ^ 59
def prefixEnd_2776709 : Nat := 4983230072969 + 3 ^ 40 * 2776709 * 2
def baseEnd_2776709 : Nat := 950524236443521231311769

theorem tailTrace_2776709 : CollatzResearch.WordTrace tailWord_2776709 prefixEnd_2776709 950524236443521231311769 := by
  unfold tailWord_2776709
  simp only [CollatzResearch.WordTrace]
  refine ⟨101274897297464991987397181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67516598198309994658264787 101274897297464991987397181)
  ·
    refine ⟨37978086486549371995273943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101274897297464991987397181 37978086486549371995273943)
    ·
      refine ⟨56967129729824057992910915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37978086486549371995273943 56967129729824057992910915)
      ·
        refine ⟨85450694594736086989366373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56967129729824057992910915 85450694594736086989366373)
        ·
          refine ⟨16022005236513016310506195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85450694594736086989366373 16022005236513016310506195)
          ·
            refine ⟨24033007854769524465759293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16022005236513016310506195 24033007854769524465759293)
            ·
              refine ⟨9012377945538571674659735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24033007854769524465759293 9012377945538571674659735)
              ·
                refine ⟨13518566918307857511989603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012377945538571674659735 13518566918307857511989603)
                ·
                  refine ⟨20277850377461786267984405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13518566918307857511989603 20277850377461786267984405)
                  ·
                    refine ⟨950524236443521231311769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20277850377461786267984405 950524236443521231311769)
                    ·
                      rfl

theorem cell22_2776709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_2776709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776709 prefixEnd_2776709 := by exact prefixLift 2776709
  have htrace : WordTrace (prefixWord ++ tailWord_2776709) baseStart_2776709 baseEnd_2776709 := by
    simpa [prefixWord, tailWord_2776709, baseEnd_2776709] using wordTrace_append hprefix tailTrace_2776709
  have hstable : (prefixWord ++ tailWord_2776709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776709).length < 2 ^ (prefixWord ++ tailWord_2776709).sum := by decide
  have hdescent : baseEnd_2776709 < baseStart_2776709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776728 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 2, 3]
def baseStart_2776728 : Nat := 118140960795 + 2776728 * 2 ^ 59
def prefixEnd_2776728 : Nat := 4983230072969 + 3 ^ 40 * 2776728 * 2
def baseEnd_2776728 : Nat := 950530740531811515086711

theorem tailTrace_2776728 : CollatzResearch.WordTrace tailWord_2776728 prefixEnd_2776728 950530740531811515086711 := by
  unfold tailWord_2776728
  simp only [CollatzResearch.WordTrace]
  refine ⟨50637795142198079116169419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67517060189597438821559225 50637795142198079116169419)
  ·
    refine ⟨75956692713297118674254129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50637795142198079116169419 75956692713297118674254129)
    ·
      refine ⟨56967519534972839005690597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75956692713297118674254129 56967519534972839005690597)
      ·
        refine ⟨10681409912807407313566987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56967519534972839005690597 10681409912807407313566987)
        ·
          refine ⟨16022114869211110970350481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10681409912807407313566987 16022114869211110970350481)
          ·
            refine ⟨12016586151908333227762861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16022114869211110970350481 12016586151908333227762861)
            ·
              refine ⟨4506219806965624960411073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12016586151908333227762861 4506219806965624960411073)
              ·
                refine ⟨3379664855224218720308305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4506219806965624960411073 3379664855224218720308305)
                ·
                  refine ⟨2534748641418164040231229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3379664855224218720308305 2534748641418164040231229)
                  ·
                    refine ⟨950530740531811515086711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534748641418164040231229 950530740531811515086711)
                    ·
                      rfl

theorem cell22_2776728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_2776728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776728 prefixEnd_2776728 := by exact prefixLift 2776728
  have htrace : WordTrace (prefixWord ++ tailWord_2776728) baseStart_2776728 baseEnd_2776728 := by
    simpa [prefixWord, tailWord_2776728, baseEnd_2776728] using wordTrace_append hprefix tailTrace_2776728
  have hstable : (prefixWord ++ tailWord_2776728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776728).length < 2 ^ (prefixWord ++ tailWord_2776728).sum := by decide
  have hdescent : baseEnd_2776728 < baseStart_2776728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776754 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2776754 : Nat := 118140960795 + 2776754 * 2 ^ 59
def prefixEnd_2776754 : Nat := 4983230072969 + 3 ^ 40 * 2776754 * 2
def baseEnd_2776754 : Nat := 950539640863156113936631

theorem tailTrace_2776754 : CollatzResearch.WordTrace tailWord_2776754 prefixEnd_2776754 950539640863156113936631 := by
  unfold tailWord_2776754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25319134645575491168196329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67517692388201309781856877 25319134645575491168196329)
  ·
    refine ⟨18989350984181618376147247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25319134645575491168196329 18989350984181618376147247)
    ·
      refine ⟨28484026476272427564220871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18989350984181618376147247 28484026476272427564220871)
      ·
        refine ⟨42726039714408641346331307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28484026476272427564220871 42726039714408641346331307)
        ·
          refine ⟨64089059571612962019496961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42726039714408641346331307 64089059571612962019496961)
          ·
            refine ⟨48066794678709721514622721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64089059571612962019496961 48066794678709721514622721)
            ·
              refine ⟨36050096009032291135967041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48066794678709721514622721 36050096009032291135967041)
              ·
                refine ⟨27037572006774218351975281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36050096009032291135967041 27037572006774218351975281)
                ·
                  refine ⟨20278179005080663763981461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27037572006774218351975281 20278179005080663763981461)
                  ·
                    refine ⟨950539640863156113936631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20278179005080663763981461 950539640863156113936631)
                    ·
                      rfl

theorem cell22_2776754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2776754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776754 prefixEnd_2776754 := by exact prefixLift 2776754
  have htrace : WordTrace (prefixWord ++ tailWord_2776754) baseStart_2776754 baseEnd_2776754 := by
    simpa [prefixWord, tailWord_2776754, baseEnd_2776754] using wordTrace_append hprefix tailTrace_2776754
  have hstable : (prefixWord ++ tailWord_2776754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776754).length < 2 ^ (prefixWord ++ tailWord_2776754).sum := by decide
  have hdescent : baseEnd_2776754 < baseStart_2776754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776758 : List Nat := [5, 1, 3, 1, 1, 2, 1, 8]
def baseStart_2776758 : Nat := 118140960795 + 2776758 * 2 ^ 59
def prefixEnd_2776758 : Nat := 4983230072969 + 3 ^ 40 * 2776758 * 2
def baseEnd_2776758 : Nat := 105615667793877937426291

theorem tailTrace_2776758 : CollatzResearch.WordTrace tailWord_2776758 prefixEnd_2776758 105615667793877937426291 := by
  unfold tailWord_2776758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329792779642967084745683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67517789649524982237287285 6329792779642967084745683)
  ·
    refine ⟨9494689169464450627118525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6329792779642967084745683 9494689169464450627118525)
    ·
      refine ⟨3560508438549168985169447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9494689169464450627118525 3560508438549168985169447)
      ·
        refine ⟨5340762657823753477754171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560508438549168985169447 5340762657823753477754171)
        ·
          refine ⟨8011143986735630216631257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340762657823753477754171 8011143986735630216631257)
          ·
            refine ⟨6008357990051722662473443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8011143986735630216631257 6008357990051722662473443)
            ·
              refine ⟨9012536985077583993710165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6008357990051722662473443 9012536985077583993710165)
              ·
                refine ⟨105615667793877937426291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9012536985077583993710165 105615667793877937426291)
                ·
                  rfl

theorem cell22_2776758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_2776758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776758 prefixEnd_2776758 := by exact prefixLift 2776758
  have htrace : WordTrace (prefixWord ++ tailWord_2776758) baseStart_2776758 baseEnd_2776758 := by
    simpa [prefixWord, tailWord_2776758, baseEnd_2776758] using wordTrace_append hprefix tailTrace_2776758
  have hstable : (prefixWord ++ tailWord_2776758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776758).length < 2 ^ (prefixWord ++ tailWord_2776758).sum := by decide
  have hdescent : baseEnd_2776758 < baseStart_2776758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776784 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_2776784 : Nat := 118140960795 + 2776784 * 2 ^ 59
def prefixEnd_2776784 : Nat := 4983230072969 + 3 ^ 40 * 2776784 * 2
def baseEnd_2776784 : Nat := 950549910476246035686539

theorem tailTrace_2776784 : CollatzResearch.WordTrace tailWord_2776784 prefixEnd_2776784 950549910476246035686539 := by
  unfold tailWord_2776784
  simp only [CollatzResearch.WordTrace]
  refine ⟨50638816386096639898188703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67518421848128853197584937 50638816386096639898188703)
  ·
    refine ⟨75958224579144959847283055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50638816386096639898188703 75958224579144959847283055)
    ·
      refine ⟨113937336868717439770924583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75958224579144959847283055 113937336868717439770924583)
      ·
        refine ⟨170906005303076159656386875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113937336868717439770924583 170906005303076159656386875)
        ·
          refine ⟨256359007954614239484580313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170906005303076159656386875 256359007954614239484580313)
          ·
            refine ⟨192269255965960679613435235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256359007954614239484580313 192269255965960679613435235)
            ·
              refine ⟨288403883948941019420152853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192269255965960679613435235 288403883948941019420152853)
              ·
                refine ⟨13518932060106610285319665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 288403883948941019420152853 13518932060106610285319665)
                ·
                  refine ⟨10139199045079957713989749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13518932060106610285319665 10139199045079957713989749)
                  ·
                    refine ⟨950549910476246035686539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10139199045079957713989749 950549910476246035686539)
                    ·
                      rfl

theorem cell22_2776784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_2776784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776784 prefixEnd_2776784 := by exact prefixLift 2776784
  have htrace : WordTrace (prefixWord ++ tailWord_2776784) baseStart_2776784 baseEnd_2776784 := by
    simpa [prefixWord, tailWord_2776784, baseEnd_2776784] using wordTrace_append hprefix tailTrace_2776784
  have hstable : (prefixWord ++ tailWord_2776784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776784).length < 2 ^ (prefixWord ++ tailWord_2776784).sum := by decide
  have hdescent : baseEnd_2776784 < baseStart_2776784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776786 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_2776786 : Nat := 118140960795 + 2776786 * 2 ^ 59
def prefixEnd_2776786 : Nat := 4983230072969 + 3 ^ 40 * 2776786 * 2
def baseEnd_2776786 : Nat := 316850198372372899045511

theorem tailTrace_2776786 : CollatzResearch.WordTrace tailWord_2776786 prefixEnd_2776786 316850198372372899045511 := by
  unfold tailWord_2776786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25319426429546508534487553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67518470478790689425300141 25319426429546508534487553)
  ·
    refine ⟨18989569822159881400865665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25319426429546508534487553 18989569822159881400865665)
    ·
      refine ⟨14242177366619911050649249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18989569822159881400865665 14242177366619911050649249)
      ·
        refine ⟨10681633024964933287986937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14242177366619911050649249 10681633024964933287986937)
        ·
          refine ⟨8011224768723699965990203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10681633024964933287986937 8011224768723699965990203)
          ·
            refine ⟨12016837153085549948985305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8011224768723699965990203 12016837153085549948985305)
            ·
              refine ⟨9012627864814162461738979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12016837153085549948985305 9012627864814162461738979)
              ·
                refine ⟨13518941797221243692608469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012627864814162461738979 13518941797221243692608469)
                ·
                  refine ⟨316850198372372899045511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13518941797221243692608469 316850198372372899045511)
                  ·
                    rfl

theorem cell22_2776786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_2776786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776786 prefixEnd_2776786 := by exact prefixLift 2776786
  have htrace : WordTrace (prefixWord ++ tailWord_2776786) baseStart_2776786 baseEnd_2776786 := by
    simpa [prefixWord, tailWord_2776786, baseEnd_2776786] using wordTrace_append hprefix tailTrace_2776786
  have hstable : (prefixWord ++ tailWord_2776786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776786).length < 2 ^ (prefixWord ++ tailWord_2776786).sum := by decide
  have hdescent : baseEnd_2776786 < baseStart_2776786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776803 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 5]
def baseStart_2776803 : Nat := 118140960795 + 2776803 * 2 ^ 59
def prefixEnd_2776803 : Nat := 4983230072969 + 3 ^ 40 * 2776803 * 2
def baseEnd_2776803 : Nat := 316852138188178773153827

theorem tailTrace_2776803 : CollatzResearch.WordTrace tailWord_2776803 prefixEnd_2776803 316852138188178773153827 := by
  unfold tailWord_2776803
  simp only [CollatzResearch.WordTrace]
  refine ⟨101278325759124446041319063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67518883839416297360879375 101278325759124446041319063)
  ·
    refine ⟨151917488638686669061978595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101278325759124446041319063 151917488638686669061978595)
    ·
      refine ⟨227876232958030003592967893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151917488638686669061978595 227876232958030003592967893)
      ·
        refine ⟨5340849209953828209210185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 227876232958030003592967893 5340849209953828209210185)
        ·
          refine ⟨4005636907465371156907639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5340849209953828209210185 4005636907465371156907639)
          ·
            refine ⟨6008455361198056735361459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005636907465371156907639 6008455361198056735361459)
            ·
              refine ⟨9012683041797085103042189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6008455361198056735361459 9012683041797085103042189)
              ·
                refine ⟨3379756140673906913640821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9012683041797085103042189 3379756140673906913640821)
                ·
                  refine ⟨316852138188178773153827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3379756140673906913640821 316852138188178773153827)
                  ·
                    rfl

theorem cell22_2776803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 5].length) (baseStart_2776803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776803 prefixEnd_2776803 := by exact prefixLift 2776803
  have htrace : WordTrace (prefixWord ++ tailWord_2776803) baseStart_2776803 baseEnd_2776803 := by
    simpa [prefixWord, tailWord_2776803, baseEnd_2776803] using wordTrace_append hprefix tailTrace_2776803
  have hstable : (prefixWord ++ tailWord_2776803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776803).length < 2 ^ (prefixWord ++ tailWord_2776803).sum := by decide
  have hdescent : baseEnd_2776803 < baseStart_2776803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776816 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_2776816 : Nat := 118140960795 + 2776816 * 2 ^ 59
def prefixEnd_2776816 : Nat := 4983230072969 + 3 ^ 40 * 2776816 * 2
def baseEnd_2776816 : Nat := 950560864730208618886441

theorem tailTrace_2776816 : CollatzResearch.WordTrace tailWord_2776816 prefixEnd_2776816 950560864730208618886441 := by
  unfold tailWord_2776816
  simp only [CollatzResearch.WordTrace]
  refine ⟨50639399954038674630771151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67519199938718232841028201 50639399954038674630771151)
  ·
    refine ⟨75959099931058011946156727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50639399954038674630771151 75959099931058011946156727)
    ·
      refine ⟨113938649896587017919235091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75959099931058011946156727 113938649896587017919235091)
      ·
        refine ⟨170907974844880526878852637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113938649896587017919235091 170907974844880526878852637)
        ·
          refine ⟨64090490566830197579569739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170907974844880526878852637 64090490566830197579569739)
          ·
            refine ⟨96135735850245296369354609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64090490566830197579569739 96135735850245296369354609)
            ·
              refine ⟨72101801887683972277015957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96135735850245296369354609 72101801887683972277015957)
              ·
                refine ⟨3379771963485186200485123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72101801887683972277015957 3379771963485186200485123)
                ·
                  refine ⟨5069657945227779300727685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379771963485186200485123 5069657945227779300727685)
                  ·
                    refine ⟨950560864730208618886441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5069657945227779300727685 950560864730208618886441)
                    ·
                      rfl

theorem cell22_2776816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_2776816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776816 prefixEnd_2776816 := by exact prefixLift 2776816
  have htrace : WordTrace (prefixWord ++ tailWord_2776816) baseStart_2776816 baseEnd_2776816 := by
    simpa [prefixWord, tailWord_2776816, baseEnd_2776816] using wordTrace_append hprefix tailTrace_2776816
  have hstable : (prefixWord ++ tailWord_2776816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776816).length < 2 ^ (prefixWord ++ tailWord_2776816).sum := by decide
  have hdescent : baseEnd_2776816 < baseStart_2776816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776852 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2776852 : Nat := 118140960795 + 2776852 * 2 ^ 59
def prefixEnd_2776852 : Nat := 4983230072969 + 3 ^ 40 * 2776852 * 2
def baseEnd_2776852 : Nat := 950573188265916524986331

theorem tailTrace_2776852 : CollatzResearch.WordTrace tailWord_2776852 prefixEnd_2776852 950573188265916524986331 := by
  unfold tailWord_2776852
  simp only [CollatzResearch.WordTrace]
  refine ⟨50640056467973463704926405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67520075290631284939901873 50640056467973463704926405)
  ·
    refine ⟨9495010587745024444673701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50640056467973463704926405 9495010587745024444673701)
    ·
      refine ⟨1780314485202192083376319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9495010587745024444673701 1780314485202192083376319)
      ·
        refine ⟨2670471727803288125064479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780314485202192083376319 2670471727803288125064479)
        ·
          refine ⟨4005707591704932187596719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670471727803288125064479 4005707591704932187596719)
          ·
            refine ⟨6008561387557398281395079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005707591704932187596719 6008561387557398281395079)
            ·
              refine ⟨9012842081336097422092619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6008561387557398281395079 9012842081336097422092619)
              ·
                refine ⟨13519263122004146133138929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012842081336097422092619 13519263122004146133138929)
                ·
                  refine ⟨10139447341503109599854197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13519263122004146133138929 10139447341503109599854197)
                  ·
                    refine ⟨950573188265916524986331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10139447341503109599854197 950573188265916524986331)
                    ·
                      rfl

theorem cell22_2776852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2776852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776852 prefixEnd_2776852 := by exact prefixLift 2776852
  have htrace : WordTrace (prefixWord ++ tailWord_2776852) baseStart_2776852 baseEnd_2776852 := by
    simpa [prefixWord, tailWord_2776852, baseEnd_2776852] using wordTrace_append hprefix tailTrace_2776852
  have hstable : (prefixWord ++ tailWord_2776852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776852).length < 2 ^ (prefixWord ++ tailWord_2776852).sum := by decide
  have hdescent : baseEnd_2776852 < baseStart_2776852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776863 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 2, 3]
def baseStart_2776863 : Nat := 118140960795 + 2776863 * 2 ^ 59
def prefixEnd_2776863 : Nat := 4983230072969 + 3 ^ 40 * 2776863 * 2
def baseEnd_2776863 : Nat := 950576953790716162961297

theorem tailTrace_2776863 : CollatzResearch.WordTrace tailWord_2776863 prefixEnd_2776863 950576953790716162961297 := by
  unfold tailWord_2776863
  simp only [CollatzResearch.WordTrace]
  refine ⟨101280514138907076288503243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67520342759271384192335495 101280514138907076288503243)
  ·
    refine ⟨151920771208360614432754865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101280514138907076288503243 151920771208360614432754865)
    ·
      refine ⟨113940578406270460824566149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151920771208360614432754865 113940578406270460824566149)
      ·
        refine ⟨21363858451175711404606153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113940578406270460824566149 21363858451175711404606153)
        ·
          refine ⟨16022893838381783553454615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21363858451175711404606153 16022893838381783553454615)
          ·
            refine ⟨24034340757572675330181923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16022893838381783553454615 24034340757572675330181923)
            ·
              refine ⟨36051511136359012995272885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24034340757572675330181923 36051511136359012995272885)
              ·
                refine ⟨3379829169033657468306833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36051511136359012995272885 3379829169033657468306833)
                ·
                  refine ⟨2534871876775243101230125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3379829169033657468306833 2534871876775243101230125)
                  ·
                    refine ⟨950576953790716162961297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534871876775243101230125 950576953790716162961297)
                    ·
                      rfl

theorem cell22_2776863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_2776863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776863 prefixEnd_2776863 := by exact prefixLift 2776863
  have htrace : WordTrace (prefixWord ++ tailWord_2776863) baseStart_2776863 baseEnd_2776863 := by
    simpa [prefixWord, tailWord_2776863, baseEnd_2776863] using wordTrace_append hprefix tailTrace_2776863
  have hstable : (prefixWord ++ tailWord_2776863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776863).length < 2 ^ (prefixWord ++ tailWord_2776863).sum := by decide
  have hdescent : baseEnd_2776863 < baseStart_2776863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776951 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 7, 4]
def baseStart_2776951 : Nat := 118140960795 + 2776951 * 2 ^ 59
def prefixEnd_2776951 : Nat := 4983230072969 + 3 ^ 40 * 2776951 * 2
def baseEnd_2776951 : Nat := 950607077989113266761027

theorem tailTrace_2776951 : CollatzResearch.WordTrace tailWord_2776951 prefixEnd_2776951 950607077989113266761027 := by
  unfold tailWord_2776951
  simp only [CollatzResearch.WordTrace]
  refine ⟨101283723762588267317706707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67522482508392178211804471 101283723762588267317706707)
  ·
    refine ⟨151925585643882400976560061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101283723762588267317706707 151925585643882400976560061)
    ·
      refine ⟨56972094616455900366210023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151925585643882400976560061 56972094616455900366210023)
      ·
        refine ⟨85458141924683850549315035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56972094616455900366210023 85458141924683850549315035)
        ·
          refine ⟨128187212887025775823972553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85458141924683850549315035 128187212887025775823972553)
          ·
            refine ⟨96140409665269331867979415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128187212887025775823972553 96140409665269331867979415)
            ·
              refine ⟨144210614497903997801969123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96140409665269331867979415 144210614497903997801969123)
              ·
                refine ⟨216315921746855996702953685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144210614497903997801969123 216315921746855996702953685)
                ·
                  refine ⟨5069904415941937422725477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 216315921746855996702953685 5069904415941937422725477)
                  ·
                    refine ⟨950607077989113266761027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5069904415941937422725477 950607077989113266761027)
                    ·
                      rfl

theorem cell22_2776951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_2776951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2776951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2776951 prefixEnd_2776951 := by exact prefixLift 2776951
  have htrace : WordTrace (prefixWord ++ tailWord_2776951) baseStart_2776951 baseEnd_2776951 := by
    simpa [prefixWord, tailWord_2776951, baseEnd_2776951] using wordTrace_append hprefix tailTrace_2776951
  have hstable : (prefixWord ++ tailWord_2776951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776951).length < 2 ^ (prefixWord ++ tailWord_2776951).sum := by decide
  have hdescent : baseEnd_2776951 < baseStart_2776951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777045 : List Nat := [1, 3, 2, 3, 2, 2, 3, 6]
def baseStart_2777045 : Nat := 118140960795 + 2777045 * 2 ^ 59
def prefixEnd_2777045 : Nat := 4983230072969 + 3 ^ 40 * 2777045 * 2
def baseEnd_2777045 : Nat := 105626584012236483878971

theorem tailTrace_2777045 : CollatzResearch.WordTrace tailWord_2777045 prefixEnd_2777045 105626584012236483878971 := by
  unfold tailWord_2777045
  simp only [CollatzResearch.WordTrace]
  refine ⟨101287152224247721371628589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67524768149498480914419059 101287152224247721371628589)
  ·
    refine ⟨37982682084092895514360721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101287152224247721371628589 37982682084092895514360721)
    ·
      refine ⟨28487011563069671635770541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37982682084092895514360721 28487011563069671635770541)
      ·
        refine ⟨10682629336151126863413953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28487011563069671635770541 10682629336151126863413953)
        ·
          refine ⟨8011972002113345147560465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10682629336151126863413953 8011972002113345147560465)
          ·
            refine ⟨6008979001585008860670349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8011972002113345147560465 6008979001585008860670349)
            ·
              refine ⟨2253367125594378322751381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6008979001585008860670349 2253367125594378322751381)
              ·
                refine ⟨105626584012236483878971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2253367125594378322751381 105626584012236483878971)
                ·
                  rfl

theorem cell22_2777045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 6].length) (baseStart_2777045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777045 prefixEnd_2777045 := by exact prefixLift 2777045
  have htrace : WordTrace (prefixWord ++ tailWord_2777045) baseStart_2777045 baseEnd_2777045 := by
    simpa [prefixWord, tailWord_2777045, baseEnd_2777045] using wordTrace_append hprefix tailTrace_2777045
  have hstable : (prefixWord ++ tailWord_2777045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777045).length < 2 ^ (prefixWord ++ tailWord_2777045).sum := by decide
  have hdescent : baseEnd_2777045 < baseStart_2777045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777111 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 1, 3]
def baseStart_2777111 : Nat := 118140960795 + 2777111 * 2 ^ 59
def prefixEnd_2777111 : Nat := 4983230072969 + 3 ^ 40 * 2777111 * 2
def baseEnd_2777111 : Nat := 950661849258926182760537

theorem tailTrace_2777111 : CollatzResearch.WordTrace tailWord_2777111 prefixEnd_2777111 950661849258926182760537 := by
  unfold tailWord_2777111
  simp only [CollatzResearch.WordTrace]
  refine ⟨101289559442008614643531187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67526372961339076429020791 101289559442008614643531187)
  ·
    refine ⟨151934339163012921965296781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101289559442008614643531187 151934339163012921965296781)
    ·
      refine ⟨56975377186129845736986293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151934339163012921965296781 56975377186129845736986293)
      ·
        refine ⟨5341441611199673037842465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56975377186129845736986293 5341441611199673037842465)
        ·
          refine ⟨4006081208399754778381849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341441611199673037842465 4006081208399754778381849)
          ·
            refine ⟨3004560906299816083786387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4006081208399754778381849 3004560906299816083786387)
            ·
              refine ⟨4506841359449724125679581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3004560906299816083786387 4506841359449724125679581)
              ·
                refine ⟨1690065509793646547129843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4506841359449724125679581 1690065509793646547129843)
                ·
                  refine ⟨2535098264690469820694765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690065509793646547129843 2535098264690469820694765)
                  ·
                    refine ⟨950661849258926182760537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535098264690469820694765 950661849258926182760537)
                    ·
                      rfl

theorem cell22_2777111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_2777111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777111 prefixEnd_2777111 := by exact prefixLift 2777111
  have htrace : WordTrace (prefixWord ++ tailWord_2777111) baseStart_2777111 baseEnd_2777111 := by
    simpa [prefixWord, tailWord_2777111, baseEnd_2777111] using wordTrace_append hprefix tailTrace_2777111
  have hstable : (prefixWord ++ tailWord_2777111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777111).length < 2 ^ (prefixWord ++ tailWord_2777111).sum := by decide
  have hdescent : baseEnd_2777111 < baseStart_2777111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777128 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2777128 : Nat := 118140960795 + 2777128 * 2 ^ 59
def prefixEnd_2777128 : Nat := 4983230072969 + 3 ^ 40 * 2777128 * 2
def baseEnd_2777128 : Nat := 950667668706343805085485

theorem tailTrace_2777128 : CollatzResearch.WordTrace tailWord_2777128 prefixEnd_2777128 950667668706343805085485 := by
  unfold tailWord_2777128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50645089741473513273450019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67526786321964684364600025 50645089741473513273450019)
  ·
    refine ⟨75967634612210269910175029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50645089741473513273450019 75967634612210269910175029)
    ·
      refine ⟨7121965744894712804078909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75967634612210269910175029 7121965744894712804078909)
      ·
        refine ⟨2670737154335517301529591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7121965744894712804078909 2670737154335517301529591)
        ·
          refine ⟨4006105731503275952294387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670737154335517301529591 4006105731503275952294387)
          ·
            refine ⟨6009158597254913928441581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006105731503275952294387 6009158597254913928441581)
            ·
              refine ⟨2253434473970592723165593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6009158597254913928441581 2253434473970592723165593)
              ·
                refine ⟨1690075855477944542374195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253434473970592723165593 1690075855477944542374195)
                ·
                  refine ⟨2535113783216916813561293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690075855477944542374195 2535113783216916813561293)
                  ·
                    refine ⟨950667668706343805085485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535113783216916813561293 950667668706343805085485)
                    ·
                      rfl

theorem cell22_2777128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2777128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777128 prefixEnd_2777128 := by exact prefixLift 2777128
  have htrace : WordTrace (prefixWord ++ tailWord_2777128) baseStart_2777128 baseEnd_2777128 := by
    simpa [prefixWord, tailWord_2777128, baseEnd_2777128] using wordTrace_append hprefix tailTrace_2777128
  have hstable : (prefixWord ++ tailWord_2777128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777128).length < 2 ^ (prefixWord ++ tailWord_2777128).sum := by decide
  have hdescent : baseEnd_2777128 < baseStart_2777128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777193 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_2777193 : Nat := 118140960795 + 2777193 * 2 ^ 59
def prefixEnd_2777193 : Nat := 4983230072969 + 3 ^ 40 * 2777193 * 2
def baseEnd_2777193 : Nat := 950689919534705302210285

theorem tailTrace_2777193 : CollatzResearch.WordTrace tailWord_2777193 prefixEnd_2777193 950689919534705302210285 := by
  unfold tailWord_2777193
  simp only [CollatzResearch.WordTrace]
  refine ⟨101292550227711542648016233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67528366818474361765344155 101292550227711542648016233)
  ·
    refine ⟨75969412670783656986012175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101292550227711542648016233 75969412670783656986012175)
    ·
      refine ⟨113954119006175485479018263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75969412670783656986012175 113954119006175485479018263)
      ·
        refine ⟨170931178509263228218527395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113954119006175485479018263 170931178509263228218527395)
        ·
          refine ⟨256396767763894842327791093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170931178509263228218527395 256396767763894842327791093)
          ·
            refine ⟨24037196977865141468230415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256396767763894842327791093 24037196977865141468230415)
            ·
              refine ⟨36055795466797712202345623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24037196977865141468230415 36055795466797712202345623)
              ·
                refine ⟨54083693200196568303518435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36055795466797712202345623 54083693200196568303518435)
                ·
                  refine ⟨81125539800294852455277653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54083693200196568303518435 81125539800294852455277653)
                  ·
                    refine ⟨950689919534705302210285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81125539800294852455277653 950689919534705302210285)
                    ·
                      rfl

theorem cell22_2777193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_2777193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777193 prefixEnd_2777193 := by exact prefixLift 2777193
  have htrace : WordTrace (prefixWord ++ tailWord_2777193) baseStart_2777193 baseEnd_2777193 := by
    simpa [prefixWord, tailWord_2777193, baseEnd_2777193] using wordTrace_append hprefix tailTrace_2777193
  have hstable : (prefixWord ++ tailWord_2777193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777193).length < 2 ^ (prefixWord ++ tailWord_2777193).sum := by decide
  have hdescent : baseEnd_2777193 < baseStart_2777193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777208 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_2777208 : Nat := 118140960795 + 2777208 * 2 ^ 59
def prefixEnd_2777208 : Nat := 4983230072969 + 3 ^ 40 * 2777208 * 2
def baseEnd_2777208 : Nat := 316898351447083421028413

theorem tailTrace_2777208 : CollatzResearch.WordTrace tailWord_2777208 prefixEnd_2777208 316898351447083421028413 := by
  unfold tailWord_2777208
  simp only [CollatzResearch.WordTrace]
  refine ⟨50646548661328600104906139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67528731548438133473208185 50646548661328600104906139)
  ·
    refine ⟨75969822991992900157359209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50646548661328600104906139 75969822991992900157359209)
    ·
      refine ⟨56977367243994675118019407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75969822991992900157359209 56977367243994675118019407)
      ·
        refine ⟨85466050865992012677029111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56977367243994675118019407 85466050865992012677029111)
        ·
          refine ⟨128199076298988019015543667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85466050865992012677029111 128199076298988019015543667)
          ·
            refine ⟨192298614448482028523315501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128199076298988019015543667 192298614448482028523315501)
            ·
              refine ⟨72111980418180760696243313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192298614448482028523315501 72111980418180760696243313)
              ·
                refine ⟨54083985313635570522182485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72111980418180760696243313 54083985313635570522182485)
                ·
                  refine ⟨316898351447083421028413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54083985313635570522182485 316898351447083421028413)
                  ·
                    rfl

theorem cell22_2777208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_2777208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777208 prefixEnd_2777208 := by exact prefixLift 2777208
  have htrace : WordTrace (prefixWord ++ tailWord_2777208) baseStart_2777208 baseEnd_2777208 := by
    simpa [prefixWord, tailWord_2777208, baseEnd_2777208] using wordTrace_append hprefix tailTrace_2777208
  have hstable : (prefixWord ++ tailWord_2777208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777208).length < 2 ^ (prefixWord ++ tailWord_2777208).sum := by decide
  have hdescent : baseEnd_2777208 < baseStart_2777208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777212 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_2777212 : Nat := 118140960795 + 2777212 * 2 ^ 59
def prefixEnd_2777212 : Nat := 4983230072969 + 3 ^ 40 * 2777212 * 2
def baseEnd_2777212 : Nat := 950696423622995585985227

theorem tailTrace_2777212 : CollatzResearch.WordTrace tailWord_2777212 prefixEnd_2777212 950696423622995585985227 := by
  unfold tailWord_2777212
  simp only [CollatzResearch.WordTrace]
  refine ⟨50646621607321354446478945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67528828809761805928638593 50646621607321354446478945)
  ·
    refine ⟨37984966205491015834859209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50646621607321354446478945 37984966205491015834859209)
    ·
      refine ⟨28488724654118261876144407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37984966205491015834859209 28488724654118261876144407)
      ·
        refine ⟨42733086981177392814216611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28488724654118261876144407 42733086981177392814216611)
        ·
          refine ⟨64099630471766089221324917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42733086981177392814216611 64099630471766089221324917)
          ·
            refine ⟨6009340356728070864499211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64099630471766089221324917 6009340356728070864499211)
            ·
              refine ⟨9014010535092106296748817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009340356728070864499211 9014010535092106296748817)
              ·
                refine ⟨6760507901319079722561613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9014010535092106296748817 6760507901319079722561613)
                ·
                  refine ⟨2535190462994654895960605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6760507901319079722561613 2535190462994654895960605)
                  ·
                    refine ⟨950696423622995585985227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535190462994654895960605 950696423622995585985227)
                    ·
                      rfl

theorem cell22_2777212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_2777212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777212 prefixEnd_2777212 := by exact prefixLift 2777212
  have htrace : WordTrace (prefixWord ++ tailWord_2777212) baseStart_2777212 baseEnd_2777212 := by
    simpa [prefixWord, tailWord_2777212, baseEnd_2777212] using wordTrace_append hprefix tailTrace_2777212
  have hstable : (prefixWord ++ tailWord_2777212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777212).length < 2 ^ (prefixWord ++ tailWord_2777212).sum := by decide
  have hdescent : baseEnd_2777212 < baseStart_2777212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777242 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_2777242 : Nat := 118140960795 + 2777242 * 2 ^ 59
def prefixEnd_2777242 : Nat := 4983230072969 + 3 ^ 40 * 2777242 * 2
def baseEnd_2777242 : Nat := 316902231078695169245045

theorem tailTrace_2777242 : CollatzResearch.WordTrace tailWord_2777242 prefixEnd_2777242 316902231078695169245045 := by
  unfold tailWord_2777242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25323584351133506004137495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67529558269689349344366653 25323584351133506004137495)
  ·
    refine ⟨37985376526700259006206243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25323584351133506004137495 37985376526700259006206243)
    ·
      refine ⟨56978064790050388509309365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37985376526700259006206243 56978064790050388509309365)
      ·
        refine ⟨5341693574067223922747753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56978064790050388509309365 5341693574067223922747753)
        ·
          refine ⟨4006270180550417942060815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341693574067223922747753 4006270180550417942060815)
          ·
            refine ⟨6009405270825626913091223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006270180550417942060815 6009405270825626913091223)
            ·
              refine ⟨9014107906238440369636835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009405270825626913091223 9014107906238440369636835)
              ·
                refine ⟨13521161859357660554455253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014107906238440369636835 13521161859357660554455253)
                ·
                  refine ⟨316902231078695169245045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13521161859357660554455253 316902231078695169245045)
                  ·
                    rfl

theorem cell22_2777242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_2777242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777242 prefixEnd_2777242 := by exact prefixLift 2777242
  have htrace : WordTrace (prefixWord ++ tailWord_2777242) baseStart_2777242 baseEnd_2777242 := by
    simpa [prefixWord, tailWord_2777242, baseEnd_2777242] using wordTrace_append hprefix tailTrace_2777242
  have hstable : (prefixWord ++ tailWord_2777242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777242).length < 2 ^ (prefixWord ++ tailWord_2777242).sum := by decide
  have hdescent : baseEnd_2777242 < baseStart_2777242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777246 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2777246 : Nat := 118140960795 + 2777246 * 2 ^ 59
def prefixEnd_2777246 : Nat := 4983230072969 + 3 ^ 40 * 2777246 * 2
def baseEnd_2777246 : Nat := 950708062517830830635123

theorem tailTrace_2777246 : CollatzResearch.WordTrace tailWord_2777246 prefixEnd_2777246 950708062517830830635123 := by
  unfold tailWord_2777246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12661810412064941587461949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67529655531013021799797061 12661810412064941587461949)
  ·
    refine ⟨4748178904524353095298231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12661810412064941587461949 4748178904524353095298231)
    ·
      refine ⟨7122268356786529642947347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748178904524353095298231 7122268356786529642947347)
      ·
        refine ⟨10683402535179794464421021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7122268356786529642947347 10683402535179794464421021)
        ·
          refine ⟨4006275950692422924157883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10683402535179794464421021 4006275950692422924157883)
          ·
            refine ⟨6009413926038634386236825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006275950692422924157883 6009413926038634386236825)
            ·
              refine ⟨4507060444528975789677619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6009413926038634386236825 4507060444528975789677619)
              ·
                refine ⟨6760590666793463684516429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4507060444528975789677619 6760590666793463684516429)
                ·
                  refine ⟨2535221500047548881693661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6760590666793463684516429 2535221500047548881693661)
                  ·
                    refine ⟨950708062517830830635123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535221500047548881693661 950708062517830830635123)
                    ·
                      rfl

theorem cell22_2777246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2777246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777246 prefixEnd_2777246 := by exact prefixLift 2777246
  have htrace : WordTrace (prefixWord ++ tailWord_2777246) baseStart_2777246 baseEnd_2777246 := by
    simpa [prefixWord, tailWord_2777246, baseEnd_2777246] using wordTrace_append hprefix tailTrace_2777246
  have hstable : (prefixWord ++ tailWord_2777246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777246).length < 2 ^ (prefixWord ++ tailWord_2777246).sum := by decide
  have hdescent : baseEnd_2777246 < baseStart_2777246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777272 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_2777272 : Nat := 118140960795 + 2777272 * 2 ^ 59
def prefixEnd_2777272 : Nat := 4983230072969 + 3 ^ 40 * 2777272 * 2
def baseEnd_2777272 : Nat := 950716962849175429485043

theorem tailTrace_2777272 : CollatzResearch.WordTrace tailWord_2777272 prefixEnd_2777272 950716962849175429485043 := by
  unfold tailWord_2777272
  simp only [CollatzResearch.WordTrace]
  refine ⟨50647715797212669570071035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67530287729616892760094713 50647715797212669570071035)
  ·
    refine ⟨75971573695819004355106553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50647715797212669570071035 75971573695819004355106553)
    ·
      refine ⟨56978680271864253266329915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75971573695819004355106553 56978680271864253266329915)
      ·
        refine ⟨85468020407796379899494873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56978680271864253266329915 85468020407796379899494873)
        ·
          refine ⟨64101015305847284924621155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85468020407796379899494873 64101015305847284924621155)
          ·
            refine ⟨96151522958770927386931733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64101015305847284924621155 96151522958770927386931733)
            ·
              refine ⟨4507102638692387221262425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96151522958770927386931733 4507102638692387221262425)
              ·
                refine ⟨3380326979019290415946819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507102638692387221262425 3380326979019290415946819)
                ·
                  refine ⟨5070490468528935623920229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380326979019290415946819 5070490468528935623920229)
                  ·
                    refine ⟨950716962849175429485043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5070490468528935623920229 950716962849175429485043)
                    ·
                      rfl

theorem cell22_2777272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_2777272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777272 prefixEnd_2777272 := by exact prefixLift 2777272
  have htrace : WordTrace (prefixWord ++ tailWord_2777272) baseStart_2777272 baseEnd_2777272 := by
    simpa [prefixWord, tailWord_2777272, baseEnd_2777272] using wordTrace_append hprefix tailTrace_2777272
  have hstable : (prefixWord ++ tailWord_2777272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777272).length < 2 ^ (prefixWord ++ tailWord_2777272).sum := by decide
  have hdescent : baseEnd_2777272 < baseStart_2777272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777285 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_2777285 : Nat := 118140960795 + 2777285 * 2 ^ 59
def prefixEnd_2777285 : Nat := 4983230072969 + 3 ^ 40 * 2777285 * 2
def baseEnd_2777285 : Nat := 950721413014847728910003

theorem tailTrace_2777285 : CollatzResearch.WordTrace tailWord_2777285 prefixEnd_2777285 950721413014847728910003 := by
  unfold tailWord_2777285
  simp only [CollatzResearch.WordTrace]
  refine ⟨101295905743378242360365309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67530603828918828240243539 101295905743378242360365309)
  ·
    refine ⟨37985964653766840885136991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101295905743378242360365309 37985964653766840885136991)
    ·
      refine ⟨56978946980650261327705487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37985964653766840885136991 56978946980650261327705487)
      ·
        refine ⟨85468420470975391991558231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56978946980650261327705487 85468420470975391991558231)
        ·
          refine ⟨128202630706463087987337347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85468420470975391991558231 128202630706463087987337347)
          ·
            refine ⟨192303946059694631981006021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128202630706463087987337347 192303946059694631981006021)
            ·
              refine ⟨36056989886192743496438629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192303946059694631981006021 36056989886192743496438629)
              ·
                refine ⟨6760685603661139405582243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36056989886192743496438629 6760685603661139405582243)
                ·
                  refine ⟨10141028405491709108373365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760685603661139405582243 10141028405491709108373365)
                  ·
                    refine ⟨950721413014847728910003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10141028405491709108373365 950721413014847728910003)
                    ·
                      rfl

theorem cell22_2777285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_2777285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777285 prefixEnd_2777285 := by exact prefixLift 2777285
  have htrace : WordTrace (prefixWord ++ tailWord_2777285) baseStart_2777285 baseEnd_2777285 := by
    simpa [prefixWord, tailWord_2777285, baseEnd_2777285] using wordTrace_append hprefix tailTrace_2777285
  have hstable : (prefixWord ++ tailWord_2777285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777285).length < 2 ^ (prefixWord ++ tailWord_2777285).sum := by decide
  have hdescent : baseEnd_2777285 < baseStart_2777285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777377 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 5]
def baseStart_2777377 : Nat := 118140960795 + 2777377 * 2 ^ 59
def prefixEnd_2777377 : Nat := 4983230072969 + 3 ^ 40 * 2777377 * 2
def baseEnd_2777377 : Nat := 316917635498330051869907

theorem tailTrace_2777377 : CollatzResearch.WordTrace tailWord_2777377 prefixEnd_2777377 316917635498330051869907 := by
  unfold tailWord_2777377
  simp only [CollatzResearch.WordTrace]
  refine ⟨101299261259044942072714385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67532840839363294715142923 101299261259044942072714385)
  ·
    refine ⟨75974445944283706554535789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101299261259044942072714385 75974445944283706554535789)
    ·
      refine ⟨28490417229106389957950921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75974445944283706554535789 28490417229106389957950921)
      ·
        refine ⟨21367812921829792468463191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28490417229106389957950921 21367812921829792468463191)
        ·
          refine ⟨32051719382744688702694787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21367812921829792468463191 32051719382744688702694787)
          ·
            refine ⟨48077579074117033054042181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32051719382744688702694787 48077579074117033054042181)
            ·
              refine ⟨9014546076396943697632909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48077579074117033054042181 9014546076396943697632909)
              ·
                refine ⟨3380454778648853886612341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9014546076396943697632909 3380454778648853886612341)
                ·
                  refine ⟨316917635498330051869907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3380454778648853886612341 316917635498330051869907)
                  ·
                    rfl

theorem cell22_2777377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_2777377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777377 prefixEnd_2777377 := by exact prefixLift 2777377
  have htrace : WordTrace (prefixWord ++ tailWord_2777377) baseStart_2777377 baseEnd_2777377 := by
    simpa [prefixWord, tailWord_2777377, baseEnd_2777377] using wordTrace_append hprefix tailTrace_2777377
  have hstable : (prefixWord ++ tailWord_2777377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777377).length < 2 ^ (prefixWord ++ tailWord_2777377).sum := by decide
  have hdescent : baseEnd_2777377 < baseStart_2777377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777383 : List Nat := [1, 1, 8, 1, 1, 1, 3, 6]
def baseStart_2777383 : Nat := 118140960795 + 2777383 * 2 ^ 59
def prefixEnd_2777383 : Nat := 4983230072969 + 3 ^ 40 * 2777383 * 2
def baseEnd_2777383 : Nat := 105639440046400904439967

theorem tailTrace_2777383 : CollatzResearch.WordTrace tailWord_2777383 prefixEnd_2777383 105639440046400904439967 := by
  unfold tailWord_2777383
  simp only [CollatzResearch.WordTrace]
  refine ⟨101299480097023205097432803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67532986731348803398288535 101299480097023205097432803)
  ·
    refine ⟨151949220145534807646149205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101299480097023205097432803 151949220145534807646149205)
    ·
      refine ⟨1780654923580486027103311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 151949220145534807646149205 1780654923580486027103311)
      ·
        refine ⟨2670982385370729040654967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780654923580486027103311 2670982385370729040654967)
        ·
          refine ⟨4006473578056093560982451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670982385370729040654967 4006473578056093560982451)
          ·
            refine ⟨6009710367084140341473677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006473578056093560982451 6009710367084140341473677)
            ·
              refine ⟨2253641387656552628052629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6009710367084140341473677 2253641387656552628052629)
              ·
                refine ⟨105639440046400904439967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2253641387656552628052629 105639440046400904439967)
                ·
                  rfl

theorem cell22_2777383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 6].length) (baseStart_2777383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777383 prefixEnd_2777383 := by exact prefixLift 2777383
  have htrace : WordTrace (prefixWord ++ tailWord_2777383) baseStart_2777383 baseEnd_2777383 := by
    simpa [prefixWord, tailWord_2777383, baseEnd_2777383] using wordTrace_append hprefix tailTrace_2777383
  have hstable : (prefixWord ++ tailWord_2777383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777383).length < 2 ^ (prefixWord ++ tailWord_2777383).sum := by decide
  have hdescent : baseEnd_2777383 < baseStart_2777383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777456 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 4]
def baseStart_2777456 : Nat := 118140960795 + 2777456 * 2 ^ 59
def prefixEnd_2777456 : Nat := 4983230072969 + 3 ^ 40 * 2777456 * 2
def baseEnd_2777456 : Nat := 316926649936486760961493

theorem tailTrace_2777456 : CollatzResearch.WordTrace tailWord_2777456 prefixEnd_2777456 316926649936486760961493 := by
  unfold tailWord_2777456
  simp only [CollatzResearch.WordTrace]
  refine ⟨50651071312879369282420111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67534761750505825709893481 50651071312879369282420111)
  ·
    refine ⟨75976606969319053923630167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50651071312879369282420111 75976606969319053923630167)
    ·
      refine ⟨113964910453978580885445251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75976606969319053923630167 113964910453978580885445251)
      ·
        refine ⟨170947365680967871328167877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113964910453978580885445251 170947365680967871328167877)
        ·
          refine ⟨32052631065181475874031477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170947365680967871328167877 32052631065181475874031477)
          ·
            refine ⟨3004934162360763363190451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32052631065181475874031477 3004934162360763363190451)
            ·
              refine ⟨4507401243541145044785677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3004934162360763363190451 4507401243541145044785677)
              ·
                refine ⟨1690275466327929391794629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4507401243541145044785677 1690275466327929391794629)
                ·
                  refine ⟨316926649936486760961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690275466327929391794629 316926649936486760961493)
                  ·
                    rfl

theorem cell22_2777456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_2777456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777456 prefixEnd_2777456 := by exact prefixLift 2777456
  have htrace : WordTrace (prefixWord ++ tailWord_2777456) baseStart_2777456 baseEnd_2777456 := by
    simpa [prefixWord, tailWord_2777456, baseEnd_2777456] using wordTrace_append hprefix tailTrace_2777456
  have hstable : (prefixWord ++ tailWord_2777456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777456).length < 2 ^ (prefixWord ++ tailWord_2777456).sum := by decide
  have hdescent : baseEnd_2777456 < baseStart_2777456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777467 : List Nat := [1, 1, 1, 1, 1, 9, 8]
def baseStart_2777467 : Nat := 118140960795 + 2777467 * 2 ^ 59
def prefixEnd_2777467 : Nat := 4983230072969 + 3 ^ 40 * 2777467 * 2
def baseEnd_2777467 : Nat := 35214211679046663735535

theorem tailTrace_2777467 : CollatzResearch.WordTrace tailWord_2777467 prefixEnd_2777467 35214211679046663735535 := by
  unfold tailWord_2777467
  simp only [CollatzResearch.WordTrace]
  refine ⟨101302543828718887443490655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67535029219145924962327103 101302543828718887443490655)
  ·
    refine ⟨151953815743078331165235983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101302543828718887443490655 151953815743078331165235983)
    ·
      refine ⟨227930723614617496747853975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151953815743078331165235983 227930723614617496747853975)
      ·
        refine ⟨341896085421926245121780963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227930723614617496747853975 341896085421926245121780963)
        ·
          refine ⟨512844128132889367682671445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341896085421926245121780963 512844128132889367682671445)
          ·
            refine ⟨3004946063278648638765653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 512844128132889367682671445 3004946063278648638765653)
            ·
              refine ⟨35214211679046663735535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3004946063278648638765653 35214211679046663735535)
              ·
                rfl

theorem cell22_2777467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 8].length) (baseStart_2777467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777467 prefixEnd_2777467 := by exact prefixLift 2777467
  have htrace : WordTrace (prefixWord ++ tailWord_2777467) baseStart_2777467 baseEnd_2777467 := by
    simpa [prefixWord, tailWord_2777467, baseEnd_2777467] using wordTrace_append hprefix tailTrace_2777467
  have hstable : (prefixWord ++ tailWord_2777467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777467).length < 2 ^ (prefixWord ++ tailWord_2777467).sum := by decide
  have hdescent : baseEnd_2777467 < baseStart_2777467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777469 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2777469 : Nat := 118140960795 + 2777469 * 2 ^ 59
def prefixEnd_2777469 : Nat := 4983230072969 + 3 ^ 40 * 2777469 * 2
def baseEnd_2777469 : Nat := 950784399975132582309439

theorem tailTrace_2777469 : CollatzResearch.WordTrace tailWord_2777469 prefixEnd_2777469 950784399975132582309439 := by
  unfold tailWord_2777469
  simp only [CollatzResearch.WordTrace]
  refine ⟨101302616774711641785063461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67535077849807761190042307 101302616774711641785063461)
  ·
    refine ⟨18994240645258432834699399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101302616774711641785063461 18994240645258432834699399)
    ·
      refine ⟨28491360967887649252049099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18994240645258432834699399 28491360967887649252049099)
      ·
        refine ⟨42737041451831473878073649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28491360967887649252049099 42737041451831473878073649)
        ·
          refine ⟨32052781088873605408555237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42737041451831473878073649 32052781088873605408555237)
          ·
            refine ⟨6009896454163801014104107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32052781088873605408555237 6009896454163801014104107)
            ·
              refine ⟨9014844681245701521156161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009896454163801014104107 9014844681245701521156161)
              ·
                refine ⟨6761133510934276140867121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9014844681245701521156161 6761133510934276140867121)
                ·
                  refine ⟨5070850133200707105650341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6761133510934276140867121 5070850133200707105650341)
                  ·
                    refine ⟨950784399975132582309439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5070850133200707105650341 950784399975132582309439)
                    ·
                      rfl

theorem cell22_2777469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2777469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777469 prefixEnd_2777469 := by exact prefixLift 2777469
  have htrace : WordTrace (prefixWord ++ tailWord_2777469) baseStart_2777469 baseEnd_2777469 := by
    simpa [prefixWord, tailWord_2777469, baseEnd_2777469] using wordTrace_append hprefix tailTrace_2777469
  have hstable : (prefixWord ++ tailWord_2777469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777469).length < 2 ^ (prefixWord ++ tailWord_2777469).sum := by decide
  have hdescent : baseEnd_2777469 < baseStart_2777469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777473 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 4]
def baseStart_2777473 : Nat := 118140960795 + 2777473 * 2 ^ 59
def prefixEnd_2777473 : Nat := 4983230072969 + 3 ^ 40 * 2777473 * 2
def baseEnd_2777473 : Nat := 316928589752292635069809

theorem tailTrace_2777473 : CollatzResearch.WordTrace tailWord_2777473 prefixEnd_2777473 316928589752292635069809 := by
  unfold tailWord_2777473
  simp only [CollatzResearch.WordTrace]
  refine ⟨101302762666697150468209073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67535175111131433645472715 101302762666697150468209073)
  ·
    refine ⟨75977072000022862851156805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101302762666697150468209073 75977072000022862851156805)
    ·
      refine ⟨14245701000004286784591901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75977072000022862851156805 14245701000004286784591901)
      ·
        refine ⟨5342137875001607544221963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14245701000004286784591901 5342137875001607544221963)
        ·
          refine ⟨8013206812502411316332945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342137875001607544221963 8013206812502411316332945)
          ·
            refine ⟨6009905109376808487249709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8013206812502411316332945 6009905109376808487249709)
            ·
              refine ⟨2253714416016303182718641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6009905109376808487249709 2253714416016303182718641)
              ·
                refine ⟨1690285812012227387038981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253714416016303182718641 1690285812012227387038981)
                ·
                  refine ⟨316928589752292635069809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690285812012227387038981 316928589752292635069809)
                  ·
                    rfl

theorem cell22_2777473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_2777473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777473 prefixEnd_2777473 := by exact prefixLift 2777473
  have htrace : WordTrace (prefixWord ++ tailWord_2777473) baseStart_2777473 baseEnd_2777473 := by
    simpa [prefixWord, tailWord_2777473, baseEnd_2777473] using wordTrace_append hprefix tailTrace_2777473
  have hstable : (prefixWord ++ tailWord_2777473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777473).length < 2 ^ (prefixWord ++ tailWord_2777473).sum := by decide
  have hdescent : baseEnd_2777473 < baseStart_2777473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777516 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_2777516 : Nat := 118140960795 + 2777516 * 2 ^ 59
def prefixEnd_2777516 : Nat := 4983230072969 + 3 ^ 40 * 2777516 * 2
def baseEnd_2777516 : Nat := 950800489035640126384295

theorem tailTrace_2777516 : CollatzResearch.WordTrace tailWord_2777516 prefixEnd_2777516 950800489035640126384295 := by
  unfold tailWord_2777516
  simp only [CollatzResearch.WordTrace]
  refine ⟨50652165502770684406012201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67536220670360912541349601 50652165502770684406012201)
  ·
    refine ⟨37989124127078013304509151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50652165502770684406012201 37989124127078013304509151)
    ·
      refine ⟨56983686190617019956763727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37989124127078013304509151 56983686190617019956763727)
      ·
        refine ⟨85475529285925529935145591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56983686190617019956763727 85475529285925529935145591)
        ·
          refine ⟨128213293928888294902718387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85475529285925529935145591 128213293928888294902718387)
          ·
            refine ⟨192319940893332442354077581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128213293928888294902718387 192319940893332442354077581)
            ·
              refine ⟨72119977834999665882779093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192319940893332442354077581 72119977834999665882779093)
              ·
                refine ⟨1690311980507804669127635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72119977834999665882779093 1690311980507804669127635)
                ·
                  refine ⟨2535467970761707003691453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690311980507804669127635 2535467970761707003691453)
                  ·
                    refine ⟨950800489035640126384295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535467970761707003691453 950800489035640126384295)
                    ·
                      rfl

theorem cell22_2777516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_2777516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777516 prefixEnd_2777516 := by exact prefixLift 2777516
  have htrace : WordTrace (prefixWord ++ tailWord_2777516) baseStart_2777516 baseEnd_2777516 := by
    simpa [prefixWord, tailWord_2777516, baseEnd_2777516] using wordTrace_append hprefix tailTrace_2777516
  have hstable : (prefixWord ++ tailWord_2777516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777516).length < 2 ^ (prefixWord ++ tailWord_2777516).sum := by decide
  have hdescent : baseEnd_2777516 < baseStart_2777516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777524 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2777524 : Nat := 118140960795 + 2777524 * 2 ^ 59
def prefixEnd_2777524 : Nat := 4983230072969 + 3 ^ 40 * 2777524 * 2
def baseEnd_2777524 : Nat := 316934409199710257394757

theorem tailTrace_2777524 : CollatzResearch.WordTrace tailWord_2777524 prefixEnd_2777524 316934409199710257394757 := by
  unfold tailWord_2777524
  simp only [CollatzResearch.WordTrace]
  refine ⟨50652311394756193089157813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67536415193008257452210417 50652311394756193089157813)
  ·
    refine ⟨4748654193258393102108545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50652311394756193089157813 4748654193258393102108545)
    ·
      refine ⟨3561490644943794826581409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4748654193258393102108545 3561490644943794826581409)
      ·
        refine ⟨2671117983707846119936057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3561490644943794826581409 2671117983707846119936057)
        ·
          refine ⟨2003338487780884589952043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2671117983707846119936057 2003338487780884589952043)
          ·
            refine ⟨3005007731671326884928065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003338487780884589952043 3005007731671326884928065)
            ·
              refine ⟨2253755798753495163696049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005007731671326884928065 2253755798753495163696049)
              ·
                refine ⟨1690316849065121372772037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253755798753495163696049 1690316849065121372772037)
                ·
                  refine ⟨316934409199710257394757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690316849065121372772037 316934409199710257394757)
                  ·
                    rfl

theorem cell22_2777524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2777524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777524 prefixEnd_2777524 := by exact prefixLift 2777524
  have htrace : WordTrace (prefixWord ++ tailWord_2777524) baseStart_2777524 baseEnd_2777524 := by
    simpa [prefixWord, tailWord_2777524, baseEnd_2777524] using wordTrace_append hprefix tailTrace_2777524
  have hstable : (prefixWord ++ tailWord_2777524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777524).length < 2 ^ (prefixWord ++ tailWord_2777524).sum := by decide
  have hdescent : baseEnd_2777524 < baseStart_2777524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777529 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 5]
def baseStart_2777529 : Nat := 118140960795 + 2777529 * 2 ^ 59
def prefixEnd_2777529 : Nat := 4983230072969 + 3 ^ 40 * 2777529 * 2
def baseEnd_2777529 : Nat := 316934979733770808603085

theorem tailTrace_2777529 : CollatzResearch.WordTrace tailWord_2777529 prefixEnd_2777529 316934979733770808603085 := by
  unfold tailWord_2777529
  simp only [CollatzResearch.WordTrace]
  refine ⟨101304805154494272032247641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67536536769662848021498427 101304805154494272032247641)
  ·
    refine ⟨75978603865870704024185731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101304805154494272032247641 75978603865870704024185731)
    ·
      refine ⟨113967905798806056036278597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75978603865870704024185731 113967905798806056036278597)
      ·
        refine ⟨21368982337276135506802237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113967905798806056036278597 21368982337276135506802237)
        ·
          refine ⟨8013368376478550815050839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21368982337276135506802237 8013368376478550815050839)
          ·
            refine ⟨12020052564717826222576259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8013368376478550815050839 12020052564717826222576259)
            ·
              refine ⟨18030078847076739333864389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12020052564717826222576259 18030078847076739333864389)
              ·
                refine ⟨3380639783826888625099573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18030078847076739333864389 3380639783826888625099573)
                ·
                  refine ⟨316934979733770808603085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3380639783826888625099573 316934979733770808603085)
                  ·
                    rfl

theorem cell22_2777529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_2777529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777529 prefixEnd_2777529 := by exact prefixLift 2777529
  have htrace : WordTrace (prefixWord ++ tailWord_2777529) baseStart_2777529 baseEnd_2777529 := by
    simpa [prefixWord, tailWord_2777529, baseEnd_2777529] using wordTrace_append hprefix tailTrace_2777529
  have hstable : (prefixWord ++ tailWord_2777529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777529).length < 2 ^ (prefixWord ++ tailWord_2777529).sum := by decide
  have hdescent : baseEnd_2777529 < baseStart_2777529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777533 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_2777533 : Nat := 118140960795 + 2777533 * 2 ^ 59
def prefixEnd_2777533 : Nat := 4983230072969 + 3 ^ 40 * 2777533 * 2
def baseEnd_2777533 : Nat := 950806308483057748709243

theorem tailTrace_2777533 : CollatzResearch.WordTrace tailWord_2777533 prefixEnd_2777533 950806308483057748709243 := by
  unfold tailWord_2777533
  simp only [CollatzResearch.WordTrace]
  refine ⟨101304951046479780715393253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67536634030986520476928835 101304951046479780715393253)
  ·
    refine ⟨18994678321214958884136235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101304951046479780715393253 18994678321214958884136235)
    ·
      refine ⟨28492017481822438326204353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18994678321214958884136235 28492017481822438326204353)
      ·
        refine ⟨21369013111366828744653265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28492017481822438326204353 21369013111366828744653265)
        ·
          refine ⟨16026759833525121558489949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21369013111366828744653265 16026759833525121558489949)
          ·
            refine ⟨6010034937571920584433731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16026759833525121558489949 6010034937571920584433731)
            ·
              refine ⟨9015052406357880876650597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6010034937571920584433731 9015052406357880876650597)
              ·
                refine ⟨1690322326192102664371987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9015052406357880876650597 1690322326192102664371987)
                ·
                  refine ⟨2535483489288153996557981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690322326192102664371987 2535483489288153996557981)
                  ·
                    refine ⟨950806308483057748709243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535483489288153996557981 950806308483057748709243)
                    ·
                      rfl

theorem cell22_2777533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_2777533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777533 prefixEnd_2777533 := by exact prefixLift 2777533
  have htrace : WordTrace (prefixWord ++ tailWord_2777533) baseStart_2777533 baseEnd_2777533 := by
    simpa [prefixWord, tailWord_2777533, baseEnd_2777533] using wordTrace_append hprefix tailTrace_2777533
  have hstable : (prefixWord ++ tailWord_2777533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777533).length < 2 ^ (prefixWord ++ tailWord_2777533).sum := by decide
  have hdescent : baseEnd_2777533 < baseStart_2777533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777544 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_2777544 : Nat := 118140960795 + 2777544 * 2 ^ 59
def prefixEnd_2777544 : Nat := 4983230072969 + 3 ^ 40 * 2777544 * 2
def baseEnd_2777544 : Nat := 950810074007857386684209

theorem tailTrace_2777544 : CollatzResearch.WordTrace tailWord_2777544 prefixEnd_2777544 950810074007857386684209 := by
  unfold tailWord_2777544
  simp only [CollatzResearch.WordTrace]
  refine ⟨50652676124719964797021843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67536901499626619729362457 50652676124719964797021843)
  ·
    refine ⟨75979014187079947195532765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50652676124719964797021843 75979014187079947195532765)
    ·
      refine ⟨28492130320154980198324787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75979014187079947195532765 28492130320154980198324787)
      ·
        refine ⟨42738195480232470297487181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28492130320154980198324787 42738195480232470297487181)
        ·
          refine ⟨16026823305087176361557693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42738195480232470297487181 16026823305087176361557693)
          ·
            refine ⟨6010058739407691135584135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16026823305087176361557693 6010058739407691135584135)
            ·
              refine ⟨9015088109111536703376203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6010058739407691135584135 9015088109111536703376203)
              ·
                refine ⟨13522632163667305055064305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9015088109111536703376203 13522632163667305055064305)
                ·
                  refine ⟨10141974122750478791298229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13522632163667305055064305 10141974122750478791298229)
                  ·
                    refine ⟨950810074007857386684209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10141974122750478791298229 950810074007857386684209)
                    ·
                      rfl

theorem cell22_2777544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_2777544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777544 prefixEnd_2777544 := by exact prefixLift 2777544
  have htrace : WordTrace (prefixWord ++ tailWord_2777544) baseStart_2777544 baseEnd_2777544 := by
    simpa [prefixWord, tailWord_2777544, baseEnd_2777544] using wordTrace_append hprefix tailTrace_2777544
  have hstable : (prefixWord ++ tailWord_2777544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777544).length < 2 ^ (prefixWord ++ tailWord_2777544).sum := by decide
  have hdescent : baseEnd_2777544 < baseStart_2777544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777576 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2777576 : Nat := 118140960795 + 2777576 * 2 ^ 59
def prefixEnd_2777576 : Nat := 4983230072969 + 3 ^ 40 * 2777576 * 2
def baseEnd_2777576 : Nat := 950821028261819969884111

theorem tailTrace_2777576 : CollatzResearch.WordTrace tailWord_2777576 prefixEnd_2777576 950821028261819969884111 := by
  unfold tailWord_2777576
  simp only [CollatzResearch.WordTrace]
  refine ⟨50653259692661999529604291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67537679590215999372805721 50653259692661999529604291)
  ·
    refine ⟨75979889538992999294406437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50653259692661999529604291 75979889538992999294406437)
    ·
      refine ⟨14246229288561187367701207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75979889538992999294406437 14246229288561187367701207)
      ·
        refine ⟨21369343932841781051551811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14246229288561187367701207 21369343932841781051551811)
        ·
          refine ⟨32054015899262671577327717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21369343932841781051551811 32054015899262671577327717)
          ·
            refine ⟨6010127981111750920748947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32054015899262671577327717 6010127981111750920748947)
            ·
              refine ⟨9015191971667626381123421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6010127981111750920748947 9015191971667626381123421)
              ·
                refine ⟨3380696989375359892921283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9015191971667626381123421 3380696989375359892921283)
                ·
                  refine ⟨5071045484063039839381925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380696989375359892921283 5071045484063039839381925)
                  ·
                    refine ⟨950821028261819969884111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071045484063039839381925 950821028261819969884111)
                    ·
                      rfl

theorem cell22_2777576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2777576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777576 prefixEnd_2777576 := by exact prefixLift 2777576
  have htrace : WordTrace (prefixWord ++ tailWord_2777576) baseStart_2777576 baseEnd_2777576 := by
    simpa [prefixWord, tailWord_2777576, baseEnd_2777576] using wordTrace_append hprefix tailTrace_2777576
  have hstable : (prefixWord ++ tailWord_2777576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777576).length < 2 ^ (prefixWord ++ tailWord_2777576).sum := by decide
  have hdescent : baseEnd_2777576 < baseStart_2777576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777769 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_2777769 : Nat := 118140960795 + 2777769 * 2 ^ 59
def prefixEnd_2777769 : Nat := 4983230072969 + 3 ^ 40 * 2777769 * 2
def baseEnd_2777769 : Nat := 950887096106031799808519

theorem tailTrace_2777769 : CollatzResearch.WordTrace tailWord_2777769 prefixEnd_2777769 950887096106031799808519 := by
  unfold tailWord_2777769
  simp only [CollatzResearch.WordTrace]
  refine ⟨101313558673624793020984361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67542372449083195347322907 101313558673624793020984361)
  ·
    refine ⟨75985169005218594765738271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101313558673624793020984361 75985169005218594765738271)
    ·
      refine ⟨113977753507827892148607407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75985169005218594765738271 113977753507827892148607407)
      ·
        refine ⟨170966630261741838222911111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113977753507827892148607407 170966630261741838222911111)
        ·
          refine ⟨256449945392612757334366667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170966630261741838222911111 256449945392612757334366667)
          ·
            refine ⟨384674918088919136001550001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256449945392612757334366667 384674918088919136001550001)
            ·
              refine ⟨288506188566689352001162501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384674918088919136001550001 288506188566689352001162501)
              ·
                refine ⟨54094910356254253500217969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288506188566689352001162501 54094910356254253500217969)
                ·
                  refine ⟨40571182767190690125163477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54094910356254253500217969 40571182767190690125163477)
                  ·
                    refine ⟨950887096106031799808519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40571182767190690125163477 950887096106031799808519)
                    ·
                      rfl

theorem cell22_2777769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_2777769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777769 prefixEnd_2777769 := by exact prefixLift 2777769
  have htrace : WordTrace (prefixWord ++ tailWord_2777769) baseStart_2777769 baseEnd_2777769 := by
    simpa [prefixWord, tailWord_2777769, baseEnd_2777769] using wordTrace_append hprefix tailTrace_2777769
  have hstable : (prefixWord ++ tailWord_2777769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777769).length < 2 ^ (prefixWord ++ tailWord_2777769).sum := by decide
  have hdescent : baseEnd_2777769 < baseStart_2777769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777775 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 2, 3]
def baseStart_2777775 : Nat := 118140960795 + 2777775 * 2 ^ 59
def prefixEnd_2777775 : Nat := 4983230072969 + 3 ^ 40 * 2777775 * 2
def baseEnd_2777775 : Nat := 950889150028649784158501

theorem tailTrace_2777775 : CollatzResearch.WordTrace tailWord_2777775 prefixEnd_2777775 950889150028649784158501 := by
  unfold tailWord_2777775
  simp only [CollatzResearch.WordTrace]
  refine ⟨101313777511603056045702779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67542518341068704030468519 101313777511603056045702779)
  ·
    refine ⟨151970666267404584068554169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101313777511603056045702779 151970666267404584068554169)
    ·
      refine ⟨113977999700553438051415627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151970666267404584068554169 113977999700553438051415627)
      ·
        refine ⟨170966999550830157077123441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113977999700553438051415627 170966999550830157077123441)
        ·
          refine ⟨128225249663122617807842581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170966999550830157077123441 128225249663122617807842581)
          ·
            refine ⟨6010558577958872709742621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128225249663122617807842581 6010558577958872709742621)
            ·
              refine ⟨2253959466734577266153483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6010558577958872709742621 2253959466734577266153483)
              ·
                refine ⟨3380939200101865899230225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253959466734577266153483 3380939200101865899230225)
                ·
                  refine ⟨2535704400076399424422669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380939200101865899230225 2535704400076399424422669)
                  ·
                    refine ⟨950889150028649784158501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535704400076399424422669 950889150028649784158501)
                    ·
                      rfl

theorem cell22_2777775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_2777775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777775 prefixEnd_2777775 := by exact prefixLift 2777775
  have htrace : WordTrace (prefixWord ++ tailWord_2777775) baseStart_2777775 baseEnd_2777775 := by
    simpa [prefixWord, tailWord_2777775, baseEnd_2777775] using wordTrace_append hprefix tailTrace_2777775
  have hstable : (prefixWord ++ tailWord_2777775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777775).length < 2 ^ (prefixWord ++ tailWord_2777775).sum := by decide
  have hdescent : baseEnd_2777775 < baseStart_2777775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777805 : List Nat := [1, 6, 2, 1, 2, 2, 8]
def baseStart_2777805 : Nat := 118140960795 + 2777805 * 2 ^ 59
def prefixEnd_2777805 : Nat := 4983230072969 + 3 ^ 40 * 2777805 * 2
def baseEnd_2777805 : Nat := 35218497023768137255867

theorem tailTrace_2777805 : CollatzResearch.WordTrace tailWord_2777805 prefixEnd_2777805 35218497023768137255867 := by
  unfold tailWord_2777805
  simp only [CollatzResearch.WordTrace]
  refine ⟨101314871701494371169294869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67543247800996247446196579 101314871701494371169294869)
  ·
    refine ⟨4749134611007548648560697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101314871701494371169294869 4749134611007548648560697)
    ·
      refine ⟨3561850958255661486420523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4749134611007548648560697 3561850958255661486420523)
      ·
        refine ⟨5342776437383492229630785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561850958255661486420523 5342776437383492229630785)
        ·
          refine ⟨4007082328037619172223089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5342776437383492229630785 4007082328037619172223089)
          ·
            refine ⟨3005311746028214379167317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007082328037619172223089 3005311746028214379167317)
            ·
              refine ⟨35218497023768137255867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3005311746028214379167317 35218497023768137255867)
              ·
                rfl

theorem cell22_2777805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 8].length) (baseStart_2777805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777805 prefixEnd_2777805 := by exact prefixLift 2777805
  have htrace : WordTrace (prefixWord ++ tailWord_2777805) baseStart_2777805 baseEnd_2777805 := by
    simpa [prefixWord, tailWord_2777805, baseEnd_2777805] using wordTrace_append hprefix tailTrace_2777805
  have hstable : (prefixWord ++ tailWord_2777805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777805).length < 2 ^ (prefixWord ++ tailWord_2777805).sum := by decide
  have hdescent : baseEnd_2777805 < baseStart_2777805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777816 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_2777816 : Nat := 118140960795 + 2777816 * 2 ^ 59
def prefixEnd_2777816 : Nat := 4983230072969 + 3 ^ 40 * 2777816 * 2
def baseEnd_2777816 : Nat := 316967728388846447961125

theorem tailTrace_2777816 : CollatzResearch.WordTrace tailWord_2777816 prefixEnd_2777816 316967728388846447961125 := by
  unfold tailWord_2777816
  simp only [CollatzResearch.WordTrace]
  refine ⟨50657636452227260023972651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67543515269636346698630201 50657636452227260023972651)
  ·
    refine ⟨75986454678340890035958977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50657636452227260023972651 75986454678340890035958977)
    ·
      refine ⟨56989841008755667526969233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75986454678340890035958977 56989841008755667526969233)
      ·
        refine ⟨42742380756566750645226925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56989841008755667526969233 42742380756566750645226925)
        ·
          refine ⟨16028392783712531491960097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42742380756566750645226925 16028392783712531491960097)
          ·
            refine ⟨12021294587784398618970073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16028392783712531491960097 12021294587784398618970073)
            ·
              refine ⟨9015970940838298964227555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12021294587784398618970073 9015970940838298964227555)
              ·
                refine ⟨13523956411257448446341333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9015970940838298964227555 13523956411257448446341333)
                ·
                  refine ⟨316967728388846447961125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13523956411257448446341333 316967728388846447961125)
                  ·
                    rfl

theorem cell22_2777816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_2777816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777816 prefixEnd_2777816 := by exact prefixLift 2777816
  have htrace : WordTrace (prefixWord ++ tailWord_2777816) baseStart_2777816 baseEnd_2777816 := by
    simpa [prefixWord, tailWord_2777816, baseEnd_2777816] using wordTrace_append hprefix tailTrace_2777816
  have hstable : (prefixWord ++ tailWord_2777816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777816).length < 2 ^ (prefixWord ++ tailWord_2777816).sum := by decide
  have hdescent : baseEnd_2777816 < baseStart_2777816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777833 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 5]
def baseStart_2777833 : Nat := 118140960795 + 2777833 * 2 ^ 59
def prefixEnd_2777833 : Nat := 4983230072969 + 3 ^ 40 * 2777833 * 2
def baseEnd_2777833 : Nat := 316969668204652322069441

theorem tailTrace_2777833 : CollatzResearch.WordTrace tailWord_2777833 prefixEnd_2777833 316969668204652322069441 := by
  unfold tailWord_2777833
  simp only [CollatzResearch.WordTrace]
  refine ⟨101315892945392931951314153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67543928630261954634209435 101315892945392931951314153)
  ·
    refine ⟨75986919709044698963485615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101315892945392931951314153 75986919709044698963485615)
    ·
      refine ⟨113980379563567048445228423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75986919709044698963485615 113980379563567048445228423)
      ·
        refine ⟨170970569345350572667842635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113980379563567048445228423 170970569345350572667842635)
        ·
          refine ⟨256455854018025859001763953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170970569345350572667842635 256455854018025859001763953)
          ·
            refine ⟨192341890513519394251322965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256455854018025859001763953 192341890513519394251322965)
            ·
              refine ⟨2254006529455305401382691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 192341890513519394251322965 2254006529455305401382691)
              ·
                refine ⟨3381009794182958102074037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254006529455305401382691 3381009794182958102074037)
                ·
                  refine ⟨316969668204652322069441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3381009794182958102074037 316969668204652322069441)
                  ·
                    rfl

theorem cell22_2777833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_2777833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777833 prefixEnd_2777833 := by exact prefixLift 2777833
  have htrace : WordTrace (prefixWord ++ tailWord_2777833) baseStart_2777833 baseEnd_2777833 := by
    simpa [prefixWord, tailWord_2777833, baseEnd_2777833] using wordTrace_append hprefix tailTrace_2777833
  have hstable : (prefixWord ++ tailWord_2777833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777833).length < 2 ^ (prefixWord ++ tailWord_2777833).sum := by decide
  have hdescent : baseEnd_2777833 < baseStart_2777833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777891 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_2777891 : Nat := 118140960795 + 2777891 * 2 ^ 59
def prefixEnd_2777891 : Nat := 4983230072969 + 3 ^ 40 * 2777891 * 2
def baseEnd_2777891 : Nat := 950928859199264148258145

theorem tailTrace_2777891 : CollatzResearch.WordTrace tailWord_2777891 prefixEnd_2777891 950928859199264148258145 := by
  unfold tailWord_2777891
  simp only [CollatzResearch.WordTrace]
  refine ⟨101318008379182807856925527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67545338919455205237950351 101318008379182807856925527)
  ·
    refine ⟨151977012568774211785388291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101318008379182807856925527 151977012568774211785388291)
    ·
      refine ⟨227965518853161317678082437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151977012568774211785388291 227965518853161317678082437)
      ·
        refine ⟨42743534784967747064640457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227965518853161317678082437 42743534784967747064640457)
        ·
          refine ⟨32057651088725810298480343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42743534784967747064640457 32057651088725810298480343)
          ·
            refine ⟨48086476633088715447720515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32057651088725810298480343 48086476633088715447720515)
            ·
              refine ⟨72129714949633073171580773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48086476633088715447720515 72129714949633073171580773)
              ·
                refine ⟨13524321553056201219671395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72129714949633073171580773 13524321553056201219671395)
                ·
                  refine ⟨20286482329584301829507093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13524321553056201219671395 20286482329584301829507093)
                  ·
                    refine ⟨950928859199264148258145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20286482329584301829507093 950928859199264148258145)
                    ·
                      rfl

theorem cell22_2777891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_2777891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777891 prefixEnd_2777891 := by exact prefixLift 2777891
  have htrace : WordTrace (prefixWord ++ tailWord_2777891) baseStart_2777891 baseEnd_2777891 := by
    simpa [prefixWord, tailWord_2777891, baseEnd_2777891] using wordTrace_append hprefix tailTrace_2777891
  have hstable : (prefixWord ++ tailWord_2777891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777891).length < 2 ^ (prefixWord ++ tailWord_2777891).sum := by decide
  have hdescent : baseEnd_2777891 < baseStart_2777891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777893 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2777893 : Nat := 118140960795 + 2777893 * 2 ^ 59
def prefixEnd_2777893 : Nat := 4983230072969 + 3 ^ 40 * 2777893 * 2
def baseEnd_2777893 : Nat := 950929543840136809708139

theorem tailTrace_2777893 : CollatzResearch.WordTrace tailWord_2777893 prefixEnd_2777893 950929543840136809708139 := by
  unfold tailWord_2777893
  simp only [CollatzResearch.WordTrace]
  refine ⟨101318081325175562198498333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67545387550117041465665555 101318081325175562198498333)
  ·
    refine ⟨37994280496940835824436875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101318081325175562198498333 37994280496940835824436875)
    ·
      refine ⟨56991420745411253736655313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37994280496940835824436875 56991420745411253736655313)
      ·
        refine ⟨42743565559058440302491485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56991420745411253736655313 42743565559058440302491485)
        ·
          refine ⟨16028837084646915113434307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42743565559058440302491485 16028837084646915113434307)
          ·
            refine ⟨24043255626970372670151461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16028837084646915113434307 24043255626970372670151461)
            ·
              refine ⟨4508110430056944875653399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24043255626970372670151461 4508110430056944875653399)
              ·
                refine ⟨6762165645085417313480099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508110430056944875653399 6762165645085417313480099)
                ·
                  refine ⟨10143248467628125970220149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762165645085417313480099 10143248467628125970220149)
                  ·
                    refine ⟨950929543840136809708139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10143248467628125970220149 950929543840136809708139)
                    ·
                      rfl

theorem cell22_2777893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2777893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777893 prefixEnd_2777893 := by exact prefixLift 2777893
  have htrace : WordTrace (prefixWord ++ tailWord_2777893) baseStart_2777893 baseEnd_2777893 := by
    simpa [prefixWord, tailWord_2777893, baseEnd_2777893] using wordTrace_append hprefix tailTrace_2777893
  have hstable : (prefixWord ++ tailWord_2777893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777893).length < 2 ^ (prefixWord ++ tailWord_2777893).sum := by decide
  have hdescent : baseEnd_2777893 < baseStart_2777893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777914 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_2777914 : Nat := 118140960795 + 2777914 * 2 ^ 59
def prefixEnd_2777914 : Nat := 4983230072969 + 3 ^ 40 * 2777914 * 2
def baseEnd_2777914 : Nat := 950936732569299754933075

theorem tailTrace_2777914 : CollatzResearch.WordTrace tailWord_2777914 prefixEnd_2777914 950936732569299754933075 := by
  unfold tailWord_2777914
  simp only [CollatzResearch.WordTrace]
  refine ⟨25329711814524870696253199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67545898172066321856675197 25329711814524870696253199)
  ·
    refine ⟨37994567721787306044379799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25329711814524870696253199 37994567721787306044379799)
    ·
      refine ⟨56991851582680959066569699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37994567721787306044379799 56991851582680959066569699)
      ·
        refine ⟨85487777374021438599854549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56991851582680959066569699 85487777374021438599854549)
        ·
          refine ⟨2003619782203627467184091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85487777374021438599854549 2003619782203627467184091)
          ·
            refine ⟨3005429673305441200776137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003619782203627467184091 3005429673305441200776137)
            ·
              refine ⟨2254072254979080900582103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005429673305441200776137 2254072254979080900582103)
              ·
                refine ⟨3381108382468621350873155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254072254979080900582103 3381108382468621350873155)
                ·
                  refine ⟨5071662573702932026309733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381108382468621350873155 5071662573702932026309733)
                  ·
                    refine ⟨950936732569299754933075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071662573702932026309733 950936732569299754933075)
                    ·
                      rfl

theorem cell22_2777914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_2777914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777914 prefixEnd_2777914 := by exact prefixLift 2777914
  have htrace : WordTrace (prefixWord ++ tailWord_2777914) baseStart_2777914 baseEnd_2777914 := by
    simpa [prefixWord, tailWord_2777914, baseEnd_2777914] using wordTrace_append hprefix tailTrace_2777914
  have hstable : (prefixWord ++ tailWord_2777914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777914).length < 2 ^ (prefixWord ++ tailWord_2777914).sum := by decide
  have hdescent : baseEnd_2777914 < baseStart_2777914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777936 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_2777936 : Nat := 118140960795 + 2777936 * 2 ^ 59
def prefixEnd_2777936 : Nat := 4983230072969 + 3 ^ 40 * 2777936 * 2
def baseEnd_2777936 : Nat := 950944263618899030883007

theorem tailTrace_2777936 : CollatzResearch.WordTrace tailWord_2777936 prefixEnd_2777936 950944263618899030883007 := by
  unfold tailWord_2777936
  simp only [CollatzResearch.WordTrace]
  refine ⟨50659824832009890271156831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67546433109346520361542441 50659824832009890271156831)
  ·
    refine ⟨75989737248014835406735247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50659824832009890271156831 75989737248014835406735247)
    ·
      refine ⟨113984605872022253110102871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75989737248014835406735247 113984605872022253110102871)
      ·
        refine ⟨170976908808033379665154307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113984605872022253110102871 170976908808033379665154307)
        ·
          refine ⟨256465363212050069497731461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170976908808033379665154307 256465363212050069497731461)
          ·
            refine ⟨48087255602259388030824649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256465363212050069497731461 48087255602259388030824649)
            ·
              refine ⟨36065441701694541023118487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48087255602259388030824649 36065441701694541023118487)
              ·
                refine ⟨54098162552541811534677731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36065441701694541023118487 54098162552541811534677731)
                ·
                  refine ⟨81147243828812717302016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54098162552541811534677731 81147243828812717302016597)
                  ·
                    refine ⟨950944263618899030883007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81147243828812717302016597 950944263618899030883007)
                    ·
                      rfl

theorem cell22_2777936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_2777936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777936 prefixEnd_2777936 := by exact prefixLift 2777936
  have htrace : WordTrace (prefixWord ++ tailWord_2777936) baseStart_2777936 baseEnd_2777936 := by
    simpa [prefixWord, tailWord_2777936, baseEnd_2777936] using wordTrace_append hprefix tailTrace_2777936
  have hstable : (prefixWord ++ tailWord_2777936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777936).length < 2 ^ (prefixWord ++ tailWord_2777936).sum := by decide
  have hdescent : baseEnd_2777936 < baseStart_2777936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777955 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 3, 3]
def baseStart_2777955 : Nat := 118140960795 + 2777955 * 2 ^ 59
def prefixEnd_2777955 : Nat := 4983230072969 + 3 ^ 40 * 2777955 * 2
def baseEnd_2777955 : Nat := 950950767707189314657949

theorem tailTrace_2777955 : CollatzResearch.WordTrace tailWord_2777955 prefixEnd_2777955 950950767707189314657949 := by
  unfold tailWord_2777955
  simp only [CollatzResearch.WordTrace]
  refine ⟨101320342650950946787255319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67546895100633964524836879 101320342650950946787255319)
  ·
    refine ⟨151980513976426420180882979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101320342650950946787255319 151980513976426420180882979)
    ·
      refine ⟨227970770964639630271324469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151980513976426420180882979 227970770964639630271324469)
      ·
        refine ⟨21372259777934965337936669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227970770964639630271324469 21372259777934965337936669)
        ·
          refine ⟨8014597416725612001726251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21372259777934965337936669 8014597416725612001726251)
          ·
            refine ⟨12021896125088418002589377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014597416725612001726251 12021896125088418002589377)
            ·
              refine ⟨9016422093816313501942033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12021896125088418002589377 9016422093816313501942033)
              ·
                refine ⟨6762316570362235126456525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9016422093816313501942033 6762316570362235126456525)
                ·
                  refine ⟨2535868713885838172421197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6762316570362235126456525 2535868713885838172421197)
                  ·
                    refine ⟨950950767707189314657949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535868713885838172421197 950950767707189314657949)
                    ·
                      rfl

theorem cell22_2777955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 3].length) (baseStart_2777955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777955 prefixEnd_2777955 := by exact prefixLift 2777955
  have htrace : WordTrace (prefixWord ++ tailWord_2777955) baseStart_2777955 baseEnd_2777955 := by
    simpa [prefixWord, tailWord_2777955, baseEnd_2777955] using wordTrace_append hprefix tailTrace_2777955
  have hstable : (prefixWord ++ tailWord_2777955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777955).length < 2 ^ (prefixWord ++ tailWord_2777955).sum := by decide
  have hdescent : baseEnd_2777955 < baseStart_2777955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777989 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_2777989 : Nat := 118140960795 + 2777989 * 2 ^ 59
def prefixEnd_2777989 : Nat := 4983230072969 + 3 ^ 40 * 2777989 * 2
def baseEnd_2777989 : Nat := 950962406602024559307845

theorem tailTrace_2777989 : CollatzResearch.WordTrace tailWord_2777989 prefixEnd_2777989 950962406602024559307845 := by
  unfold tailWord_2777989
  simp only [CollatzResearch.WordTrace]
  refine ⟨101321582732827770593993021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67547721821885180395995347 101321582732827770593993021)
  ·
    refine ⟨37995593524810413972747383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101321582732827770593993021 37995593524810413972747383)
    ·
      refine ⟨56993390287215620959121075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37995593524810413972747383 56993390287215620959121075)
      ·
        refine ⟨85490085430823431438681613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56993390287215620959121075 85490085430823431438681613)
        ·
          refine ⟨32058782036558786789505605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85490085430823431438681613 32058782036558786789505605)
          ·
            refine ⟨6011021631854772523032301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32058782036558786789505605 6011021631854772523032301)
            ·
              refine ⟨2254133111945539696137113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6011021631854772523032301 2254133111945539696137113)
              ·
                refine ⟨1690599833959154772102835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254133111945539696137113 1690599833959154772102835)
                ·
                  refine ⟨2535899750938732158154253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690599833959154772102835 2535899750938732158154253)
                  ·
                    refine ⟨950962406602024559307845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535899750938732158154253 950962406602024559307845)
                    ·
                      rfl

theorem cell22_2777989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_2777989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2777989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2777989 prefixEnd_2777989 := by exact prefixLift 2777989
  have htrace : WordTrace (prefixWord ++ tailWord_2777989) baseStart_2777989 baseEnd_2777989 := by
    simpa [prefixWord, tailWord_2777989, baseEnd_2777989] using wordTrace_append hprefix tailTrace_2777989
  have hstable : (prefixWord ++ tailWord_2777989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777989).length < 2 ^ (prefixWord ++ tailWord_2777989).sum := by decide
  have hdescent : baseEnd_2777989 < baseStart_2777989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778002 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_2778002 : Nat := 118140960795 + 2778002 * 2 ^ 59
def prefixEnd_2778002 : Nat := 4983230072969 + 3 ^ 40 * 2778002 * 2
def baseEnd_2778002 : Nat := 316988952255898952910935

theorem tailTrace_2778002 : CollatzResearch.WordTrace tailWord_2778002 prefixEnd_2778002 316988952255898952910935 := by
  unfold tailWord_2778002
  simp only [CollatzResearch.WordTrace]
  refine ⟨25330514220445168453554065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67548037921187115876144173 25330514220445168453554065)
  ·
    refine ⟨18997885665333876340165549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25330514220445168453554065 18997885665333876340165549)
    ·
      refine ⟨7124207124500203627562081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18997885665333876340165549 7124207124500203627562081)
      ·
        refine ⟨5343155343375152720671561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7124207124500203627562081 5343155343375152720671561)
        ·
          refine ⟨4007366507531364540503671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5343155343375152720671561 4007366507531364540503671)
          ·
            refine ⟨6011049761297046810755507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007366507531364540503671 6011049761297046810755507)
            ·
              refine ⟨9016574641945570216133261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011049761297046810755507 9016574641945570216133261)
              ·
                refine ⟨3381215490729588831049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9016574641945570216133261 3381215490729588831049973)
                ·
                  refine ⟨316988952255898952910935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3381215490729588831049973 316988952255898952910935)
                  ·
                    rfl

theorem cell22_2778002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_2778002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778002 prefixEnd_2778002 := by exact prefixLift 2778002
  have htrace : WordTrace (prefixWord ++ tailWord_2778002) baseStart_2778002 baseEnd_2778002 := by
    simpa [prefixWord, tailWord_2778002, baseEnd_2778002] using wordTrace_append hprefix tailTrace_2778002
  have hstable : (prefixWord ++ tailWord_2778002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778002).length < 2 ^ (prefixWord ++ tailWord_2778002).sum := by decide
  have hdescent : baseEnd_2778002 < baseStart_2778002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778013 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 8]
def baseStart_2778013 : Nat := 118140960795 + 2778013 * 2 ^ 59
def prefixEnd_2778013 : Nat := 4983230072969 + 3 ^ 40 * 2778013 * 2
def baseEnd_2778013 : Nat := 316990207430832165569257

theorem tailTrace_2778013 : CollatzResearch.WordTrace tailWord_2778013 prefixEnd_2778013 316990207430832165569257 := by
  unfold tailWord_2778013
  simp only [CollatzResearch.WordTrace]
  refine ⟨101322458084740822692866693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67548305389827215128577795 101322458084740822692866693)
  ·
    refine ⟨18997960890888904254912505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101322458084740822692866693 18997960890888904254912505)
    ·
      refine ⟨14248470668166678191184379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18997960890888904254912505 14248470668166678191184379)
      ·
        refine ⟨21372706002250017286776569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14248470668166678191184379 21372706002250017286776569)
        ·
          refine ⟨16029529501687512965082427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21372706002250017286776569 16029529501687512965082427)
          ·
            refine ⟨24044294252531269447623641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16029529501687512965082427 24044294252531269447623641)
            ·
              refine ⟨18033220689398452085717731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24044294252531269447623641 18033220689398452085717731)
              ·
                refine ⟨27049831034097678128576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18033220689398452085717731 27049831034097678128576597)
                ·
                  refine ⟨316990207430832165569257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27049831034097678128576597 316990207430832165569257)
                  ·
                    rfl

theorem cell22_2778013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_2778013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778013 prefixEnd_2778013 := by exact prefixLift 2778013
  have htrace : WordTrace (prefixWord ++ tailWord_2778013) baseStart_2778013 baseEnd_2778013 := by
    simpa [prefixWord, tailWord_2778013, baseEnd_2778013] using wordTrace_append hprefix tailTrace_2778013
  have hstable : (prefixWord ++ tailWord_2778013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778013).length < 2 ^ (prefixWord ++ tailWord_2778013).sum := by decide
  have hdescent : baseEnd_2778013 < baseStart_2778013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778015 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 3, 4]
def baseStart_2778015 : Nat := 118140960795 + 2778015 * 2 ^ 59
def prefixEnd_2778015 : Nat := 4983230072969 + 3 ^ 40 * 2778015 * 2
def baseEnd_2778015 : Nat := 950971306933369158157765

theorem tailTrace_2778015 : CollatzResearch.WordTrace tailWord_2778015 prefixEnd_2778015 950971306933369158157765 := by
  unfold tailWord_2778015
  simp only [CollatzResearch.WordTrace]
  refine ⟨101322531030733577034439499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67548354020489051356292999 101322531030733577034439499)
  ·
    refine ⟨151983796546100365551659249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101322531030733577034439499 151983796546100365551659249)
    ·
      refine ⟨113987847409575274163744437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151983796546100365551659249 113987847409575274163744437)
      ·
        refine ⟨10686360694647681952851041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113987847409575274163744437 10686360694647681952851041)
        ·
          refine ⟨8014770520985761464638281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10686360694647681952851041 8014770520985761464638281)
          ·
            refine ⟨6011077890739321098478711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8014770520985761464638281 6011077890739321098478711)
            ·
              refine ⟨9016616836108981647718067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011077890739321098478711 9016616836108981647718067)
              ·
                refine ⟨13524925254163472471577101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9016616836108981647718067 13524925254163472471577101)
                ·
                  refine ⟨5071846970311302176841413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13524925254163472471577101 5071846970311302176841413)
                  ·
                    refine ⟨950971306933369158157765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071846970311302176841413 950971306933369158157765)
                    ·
                      rfl

theorem cell22_2778015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_2778015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778015 prefixEnd_2778015 := by exact prefixLift 2778015
  have htrace : WordTrace (prefixWord ++ tailWord_2778015) baseStart_2778015 baseEnd_2778015 := by
    simpa [prefixWord, tailWord_2778015, baseEnd_2778015] using wordTrace_append hprefix tailTrace_2778015
  have hstable : (prefixWord ++ tailWord_2778015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778015).length < 2 ^ (prefixWord ++ tailWord_2778015).sum := by decide
  have hdescent : baseEnd_2778015 < baseStart_2778015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778028 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_2778028 : Nat := 118140960795 + 2778028 * 2 ^ 59
def prefixEnd_2778028 : Nat := 4983230072969 + 3 ^ 40 * 2778028 * 2
def baseEnd_2778028 : Nat := 950975757099041457582725

theorem tailTrace_2778028 : CollatzResearch.WordTrace tailWord_2778028 prefixEnd_2778028 950975757099041457582725 := by
  unfold tailWord_2778028
  simp only [CollatzResearch.WordTrace]
  refine ⟨50661502589843240127331369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67548670119790986836441825 50661502589843240127331369)
  ·
    refine ⟨37996126942382430095498527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50661502589843240127331369 37996126942382430095498527)
    ·
      refine ⟨56994190413573645143247791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37996126942382430095498527 56994190413573645143247791)
      ·
        refine ⟨85491285620360467714871687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56994190413573645143247791 85491285620360467714871687)
        ·
          refine ⟨128236928430540701572307531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85491285620360467714871687 128236928430540701572307531)
          ·
            refine ⟨192355392645811052358461297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128236928430540701572307531 192355392645811052358461297)
            ·
              refine ⟨144266544484358289268845973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192355392645811052358461297 144266544484358289268845973)
              ·
                refine ⟨6762494272704294809477155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144266544484358289268845973 6762494272704294809477155)
                ·
                  refine ⟨10143741409056442214215733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762494272704294809477155 10143741409056442214215733)
                  ·
                    refine ⟨950975757099041457582725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10143741409056442214215733 950975757099041457582725)
                    ·
                      rfl

theorem cell22_2778028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_2778028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778028 prefixEnd_2778028 := by exact prefixLift 2778028
  have htrace : WordTrace (prefixWord ++ tailWord_2778028) baseStart_2778028 baseEnd_2778028 := by
    simpa [prefixWord, tailWord_2778028, baseEnd_2778028] using wordTrace_append hprefix tailTrace_2778028
  have hstable : (prefixWord ++ tailWord_2778028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778028).length < 2 ^ (prefixWord ++ tailWord_2778028).sum := by decide
  have hdescent : baseEnd_2778028 < baseStart_2778028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778062 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_2778062 : Nat := 118140960795 + 2778062 * 2 ^ 59
def prefixEnd_2778062 : Nat := 4983230072969 + 3 ^ 40 * 2778062 * 2
def baseEnd_2778062 : Nat := 950987395993876702232621

theorem tailTrace_2778062 : CollatzResearch.WordTrace tailWord_2778062 prefixEnd_2778062 950987395993876702232621 := by
  unfold tailWord_2778062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665530657695413007675055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67549496841042202707600293 12665530657695413007675055)
  ·
    refine ⟨18998295986543119511512583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12665530657695413007675055 18998295986543119511512583)
    ·
      refine ⟨28497443979814679267268875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18998295986543119511512583 28497443979814679267268875)
      ·
        refine ⟨42746165969722018900903313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28497443979814679267268875 42746165969722018900903313)
        ·
          refine ⟨32059624477291514175677485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42746165969722018900903313 32059624477291514175677485)
          ·
            refine ⟨12022359178984317815879057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32059624477291514175677485 12022359178984317815879057)
            ·
              refine ⟨9016769384238238361909293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12022359178984317815879057 9016769384238238361909293)
              ·
                refine ⟨3381288519089339385715985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9016769384238238361909293 3381288519089339385715985)
                ·
                  refine ⟨2535966389317004539286989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3381288519089339385715985 2535966389317004539286989)
                  ·
                    refine ⟨950987395993876702232621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535966389317004539286989 950987395993876702232621)
                    ·
                      rfl

theorem cell22_2778062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_2778062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778062 prefixEnd_2778062 := by exact prefixLift 2778062
  have htrace : WordTrace (prefixWord ++ tailWord_2778062) baseStart_2778062 baseEnd_2778062 := by
    simpa [prefixWord, tailWord_2778062, baseEnd_2778062] using wordTrace_append hprefix tailTrace_2778062
  have hstable : (prefixWord ++ tailWord_2778062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778062).length < 2 ^ (prefixWord ++ tailWord_2778062).sum := by decide
  have hdescent : baseEnd_2778062 < baseStart_2778062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778077 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2778077 : Nat := 118140960795 + 2778077 * 2 ^ 59
def prefixEnd_2778077 : Nat := 4983230072969 + 3 ^ 40 * 2778077 * 2
def baseEnd_2778077 : Nat := 950992530800421663107575

theorem tailTrace_2778077 : CollatzResearch.WordTrace tailWord_2778077 prefixEnd_2778077 950992530800421663107575 := by
  unfold tailWord_2778077
  simp only [CollatzResearch.WordTrace]
  refine ⟨101324792356508961623196485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67549861571005974415464323 101324792356508961623196485)
  ·
    refine ⟨18998398566845430304349341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101324792356508961623196485 18998398566845430304349341)
    ·
      refine ⟨7124399462567036364131003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18998398566845430304349341 7124399462567036364131003)
      ·
        refine ⟨10686599193850554546196505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7124399462567036364131003 10686599193850554546196505)
        ·
          refine ⟨8014949395387915909647379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10686599193850554546196505 8014949395387915909647379)
          ·
            refine ⟨12022424093081873864471069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014949395387915909647379 12022424093081873864471069)
            ·
              refine ⟨4508409034905702699176651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12022424093081873864471069 4508409034905702699176651)
              ·
                refine ⟨6762613552358554048764977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508409034905702699176651 6762613552358554048764977)
                ·
                  refine ⟨5071960164268915536573733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762613552358554048764977 5071960164268915536573733)
                  ·
                    refine ⟨950992530800421663107575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071960164268915536573733 950992530800421663107575)
                    ·
                      rfl

theorem cell22_2778077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2778077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778077 prefixEnd_2778077 := by exact prefixLift 2778077
  have htrace : WordTrace (prefixWord ++ tailWord_2778077) baseStart_2778077 baseEnd_2778077 := by
    simpa [prefixWord, tailWord_2778077, baseEnd_2778077] using wordTrace_append hprefix tailTrace_2778077
  have hstable : (prefixWord ++ tailWord_2778077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778077).length < 2 ^ (prefixWord ++ tailWord_2778077).sum := by decide
  have hdescent : baseEnd_2778077 < baseStart_2778077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778195 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 2, 4]
def baseStart_2778195 : Nat := 118140960795 + 2778195 * 2 ^ 59
def prefixEnd_2778195 : Nat := 4983230072969 + 3 ^ 40 * 2778195 * 2
def baseEnd_2778195 : Nat := 951032924611908688657213

theorem tailTrace_2778195 : CollatzResearch.WordTrace tailWord_2778195 prefixEnd_2778195 951032924611908688657213 := by
  unfold tailWord_2778195
  simp only [CollatzResearch.WordTrace]
  refine ⟨101329096170081467775992039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67552730780054311850661359 101329096170081467775992039)
  ·
    refine ⟨151993644255122201663988059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101329096170081467775992039 151993644255122201663988059)
    ·
      refine ⟨227990466382683302495982089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151993644255122201663988059 227990466382683302495982089)
      ·
        refine ⟨170992849787012476871986567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227990466382683302495982089 170992849787012476871986567)
        ·
          refine ⟨256489274680518715307979851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170992849787012476871986567 256489274680518715307979851)
          ·
            refine ⟨384733912020778072961969777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256489274680518715307979851 384733912020778072961969777)
            ·
              refine ⟨288550434015583554721477333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384733912020778072961969777 288550434015583554721477333)
              ·
                refine ⟨6762900797240239563784625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 288550434015583554721477333 6762900797240239563784625)
                ·
                  refine ⟨5072175597930179672838469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762900797240239563784625 5072175597930179672838469)
                  ·
                    refine ⟨951032924611908688657213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5072175597930179672838469 951032924611908688657213)
                    ·
                      rfl

theorem cell22_2778195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_2778195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778195 prefixEnd_2778195 := by exact prefixLift 2778195
  have htrace : WordTrace (prefixWord ++ tailWord_2778195) baseStart_2778195 baseEnd_2778195 := by
    simpa [prefixWord, tailWord_2778195, baseEnd_2778195] using wordTrace_append hprefix tailTrace_2778195
  have hstable : (prefixWord ++ tailWord_2778195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778195).length < 2 ^ (prefixWord ++ tailWord_2778195).sum := by decide
  have hdescent : baseEnd_2778195 < baseStart_2778195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778216 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 4]
def baseStart_2778216 : Nat := 118140960795 + 2778216 * 2 ^ 59
def prefixEnd_2778216 : Nat := 4983230072969 + 3 ^ 40 * 2778216 * 2
def baseEnd_2778216 : Nat := 317013371113690544627383

theorem tailTrace_2778216 : CollatzResearch.WordTrace tailWord_2778216 prefixEnd_2778216 317013371113690544627383 := by
  unfold tailWord_2778216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50664931051502694181253251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67553241402003592241671001 50664931051502694181253251)
  ·
    refine ⟨75997396577254041271879877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50664931051502694181253251 75997396577254041271879877)
    ·
      refine ⟨14249511858235132738477477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75997396577254041271879877 14249511858235132738477477)
      ·
        refine ⟨2671783473419087388464527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14249511858235132738477477 2671783473419087388464527)
        ·
          refine ⟨4007675210128631082696791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671783473419087388464527 4007675210128631082696791)
          ·
            refine ⟨6011512815192946624045187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007675210128631082696791 6011512815192946624045187)
            ·
              refine ⟨9017269222789419936067781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011512815192946624045187 9017269222789419936067781)
              ·
                refine ⟨1690737979273016238012709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9017269222789419936067781 1690737979273016238012709)
                ·
                  refine ⟨317013371113690544627383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690737979273016238012709 317013371113690544627383)
                  ·
                    rfl

theorem cell22_2778216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_2778216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778216 prefixEnd_2778216 := by exact prefixLift 2778216
  have htrace : WordTrace (prefixWord ++ tailWord_2778216) baseStart_2778216 baseEnd_2778216 := by
    simpa [prefixWord, tailWord_2778216, baseEnd_2778216] using wordTrace_append hprefix tailTrace_2778216
  have hstable : (prefixWord ++ tailWord_2778216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778216).length < 2 ^ (prefixWord ++ tailWord_2778216).sum := by decide
  have hdescent : baseEnd_2778216 < baseStart_2778216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778259 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 1, 3]
def baseStart_2778259 : Nat := 118140960795 + 2778259 * 2 ^ 59
def prefixEnd_2778259 : Nat := 4983230072969 + 3 ^ 40 * 2778259 * 2
def baseEnd_2778259 : Nat := 951054833119833855057017

theorem tailTrace_2778259 : CollatzResearch.WordTrace tailWord_2778259 prefixEnd_2778259 951054833119833855057017 := by
  unfold tailWord_2778259
  simp only [CollatzResearch.WordTrace]
  refine ⟨101331430441849606706321831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67554286961233071137547887 101331430441849606706321831)
  ·
    refine ⟨151997145662774410059482747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101331430441849606706321831 151997145662774410059482747)
    ·
      refine ⟨227995718494161615089224121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151997145662774410059482747 227995718494161615089224121)
      ·
        refine ⟨170996788870621211316918091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227995718494161615089224121 170996788870621211316918091)
        ·
          refine ⟨256495183305931816975377137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170996788870621211316918091 256495183305931816975377137)
          ·
            refine ⟨192371387479448862731532853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256495183305931816975377137 192371387479448862731532853)
            ·
              refine ⟨18034817576198330881081205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192371387479448862731532853 18034817576198330881081205)
              ·
                refine ⟨1690764147768593520101363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18034817576198330881081205 1690764147768593520101363)
                ·
                  refine ⟨2536146221652890280152045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690764147768593520101363 2536146221652890280152045)
                  ·
                    refine ⟨951054833119833855057017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536146221652890280152045 951054833119833855057017)
                    ·
                      rfl

theorem cell22_2778259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 3].length) (baseStart_2778259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778259 prefixEnd_2778259 := by exact prefixLift 2778259
  have htrace : WordTrace (prefixWord ++ tailWord_2778259) baseStart_2778259 baseEnd_2778259 := by
    simpa [prefixWord, tailWord_2778259, baseEnd_2778259] using wordTrace_append hprefix tailTrace_2778259
  have hstable : (prefixWord ++ tailWord_2778259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778259).length < 2 ^ (prefixWord ++ tailWord_2778259).sum := by decide
  have hdescent : baseEnd_2778259 < baseStart_2778259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778276 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_2778276 : Nat := 118140960795 + 2778276 * 2 ^ 59
def prefixEnd_2778276 : Nat := 4983230072969 + 3 ^ 40 * 2778276 * 2
def baseEnd_2778276 : Nat := 951060652567251477381965

theorem tailTrace_2778276 : CollatzResearch.WordTrace tailWord_2778276 prefixEnd_2778276 951060652567251477381965 := by
  unfold tailWord_2778276
  simp only [CollatzResearch.WordTrace]
  refine ⟨50666025241394009304845341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67554700321858679073127121 50666025241394009304845341)
  ·
    refine ⟨18999759465522753489317003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50666025241394009304845341 18999759465522753489317003)
    ·
      refine ⟨28499639198284130233975505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18999759465522753489317003 28499639198284130233975505)
      ·
        refine ⟨21374729398713097675481629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28499639198284130233975505 21374729398713097675481629)
        ·
          refine ⟨8015523524517411628305611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21374729398713097675481629 8015523524517411628305611)
          ·
            refine ⟨12023285286776117442458417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8015523524517411628305611 12023285286776117442458417)
            ·
              refine ⟨9017463965082088081843813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12023285286776117442458417 9017463965082088081843813)
              ·
                refine ⟨1690774493452891515345715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9017463965082088081843813 1690774493452891515345715)
                ·
                  refine ⟨2536161740179337273018573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690774493452891515345715 2536161740179337273018573)
                  ·
                    refine ⟨951060652567251477381965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536161740179337273018573 951060652567251477381965)
                    ·
                      rfl

theorem cell22_2778276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_2778276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778276 prefixEnd_2778276 := by exact prefixLift 2778276
  have htrace : WordTrace (prefixWord ++ tailWord_2778276) baseStart_2778276 baseEnd_2778276 := by
    simpa [prefixWord, tailWord_2778276, baseEnd_2778276] using wordTrace_append hprefix tailTrace_2778276
  have hstable : (prefixWord ++ tailWord_2778276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778276).length < 2 ^ (prefixWord ++ tailWord_2778276).sum := by decide
  have hdescent : baseEnd_2778276 < baseStart_2778276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778392 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_2778392 : Nat := 118140960795 + 2778392 * 2 ^ 59
def prefixEnd_2778392 : Nat := 4983230072969 + 3 ^ 40 * 2778392 * 2
def baseEnd_2778392 : Nat := 951100361737865841481609

theorem tailTrace_2778392 : CollatzResearch.WordTrace tailWord_2778392 prefixEnd_2778392 951100361737865841481609 := by
  unfold tailWord_2778392
  simp only [CollatzResearch.WordTrace]
  refine ⟨50668140675183885210456715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67557520900245180280608953 50668140675183885210456715)
  ·
    refine ⟨76002211012775827815685073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50668140675183885210456715 76002211012775827815685073)
    ·
      refine ⟨57001658259581870861763805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76002211012775827815685073 57001658259581870861763805)
      ·
        refine ⟨21375621847343201573161427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57001658259581870861763805 21375621847343201573161427)
        ·
          refine ⟨32063432771014802359742141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21375621847343201573161427 32063432771014802359742141)
          ·
            refine ⟨12023787289130550884903303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32063432771014802359742141 12023787289130550884903303)
            ·
              refine ⟨18035680933695826327354955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12023787289130550884903303 18035680933695826327354955)
              ·
                refine ⟨27053521400543739491032433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18035680933695826327354955 27053521400543739491032433)
                ·
                  refine ⟨20290141050407804618274325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27053521400543739491032433 20290141050407804618274325)
                  ·
                    refine ⟨951100361737865841481609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20290141050407804618274325 951100361737865841481609)
                    ·
                      rfl

theorem cell22_2778392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_2778392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778392 prefixEnd_2778392 := by exact prefixLift 2778392
  have htrace : WordTrace (prefixWord ++ tailWord_2778392) baseStart_2778392 baseEnd_2778392 := by
    simpa [prefixWord, tailWord_2778392, baseEnd_2778392] using wordTrace_append hprefix tailTrace_2778392
  have hstable : (prefixWord ++ tailWord_2778392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778392).length < 2 ^ (prefixWord ++ tailWord_2778392).sum := by decide
  have hdescent : baseEnd_2778392 < baseStart_2778392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778428 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_2778428 : Nat := 118140960795 + 2778428 * 2 ^ 59
def prefixEnd_2778428 : Nat := 4983230072969 + 3 ^ 40 * 2778428 * 2
def baseEnd_2778428 : Nat := 951112685273573747581499

theorem tailTrace_2778428 : CollatzResearch.WordTrace tailWord_2778428 prefixEnd_2778428 951112685273573747581499 := by
  unfold tailWord_2778428
  simp only [CollatzResearch.WordTrace]
  refine ⟨50668797189118674284611969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67558396252158232379482625 50668797189118674284611969)
  ·
    refine ⟨38001597891839005713458977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50668797189118674284611969 38001597891839005713458977)
    ·
      refine ⟨28501198418879254285094233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38001597891839005713458977 28501198418879254285094233)
      ·
        refine ⟨21375898814159440713820675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28501198418879254285094233 21375898814159440713820675)
        ·
          refine ⟨32063848221239161070731013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21375898814159440713820675 32063848221239161070731013)
          ·
            refine ⟨6011971541482342700762065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32063848221239161070731013 6011971541482342700762065)
            ·
              refine ⟨4508978656111757025571549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011971541482342700762065 4508978656111757025571549)
              ·
                refine ⟨1690866996041908884589331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4508978656111757025571549 1690866996041908884589331)
                ·
                  refine ⟨2536300494062863326883997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690866996041908884589331 2536300494062863326883997)
                  ·
                    refine ⟨951112685273573747581499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536300494062863326883997 951112685273573747581499)
                    ·
                      rfl

theorem cell22_2778428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_2778428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778428 prefixEnd_2778428 := by exact prefixLift 2778428
  have htrace : WordTrace (prefixWord ++ tailWord_2778428) baseStart_2778428 baseEnd_2778428 := by
    simpa [prefixWord, tailWord_2778428, baseEnd_2778428] using wordTrace_append hprefix tailTrace_2778428
  have hstable : (prefixWord ++ tailWord_2778428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778428).length < 2 ^ (prefixWord ++ tailWord_2778428).sum := by decide
  have hdescent : baseEnd_2778428 < baseStart_2778428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778445 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2778445 : Nat := 118140960795 + 2778445 * 2 ^ 59
def prefixEnd_2778445 : Nat := 4983230072969 + 3 ^ 40 * 2778445 * 2
def baseEnd_2778445 : Nat := 951118504720991369906447

theorem tailTrace_2778445 : CollatzResearch.WordTrace tailWord_2778445 prefixEnd_2778445 951118504720991369906447 := by
  unfold tailWord_2778445
  simp only [CollatzResearch.WordTrace]
  refine ⟨101338214419175760472592789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67558809612783840315061859 101338214419175760472592789)
  ·
    refine ⟨4750228800898863772152787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101338214419175760472592789 4750228800898863772152787)
    ·
      refine ⟨7125343201348295658229181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750228800898863772152787 7125343201348295658229181)
      ·
        refine ⟨2672003700505610871835943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7125343201348295658229181 2672003700505610871835943)
        ·
          refine ⟨4008005550758416307753915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672003700505610871835943 4008005550758416307753915)
          ·
            refine ⟨6012008326137624461630873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008005550758416307753915 6012008326137624461630873)
            ·
              refine ⟨4509006244603218346223155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6012008326137624461630873 4509006244603218346223155)
              ·
                refine ⟨6763509366904827519334733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509006244603218346223155 6763509366904827519334733)
                ·
                  refine ⟨2536316012589310319750525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6763509366904827519334733 2536316012589310319750525)
                  ·
                    refine ⟨951118504720991369906447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536316012589310319750525 951118504720991369906447)
                    ·
                      rfl

theorem cell22_2778445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2778445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778445 prefixEnd_2778445 := by exact prefixLift 2778445
  have htrace : WordTrace (prefixWord ++ tailWord_2778445) baseStart_2778445 baseEnd_2778445 := by
    simpa [prefixWord, tailWord_2778445, baseEnd_2778445] using wordTrace_append hprefix tailTrace_2778445
  have hstable : (prefixWord ++ tailWord_2778445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778445).length < 2 ^ (prefixWord ++ tailWord_2778445).sum := by decide
  have hdescent : baseEnd_2778445 < baseStart_2778445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778499 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 4, 4]
def baseStart_2778499 : Nat := 118140960795 + 2778499 * 2 ^ 59
def prefixEnd_2778499 : Nat := 4983230072969 + 3 ^ 40 * 2778499 * 2
def baseEnd_2778499 : Nat := 951136990024553229056281

theorem tailTrace_2778499 : CollatzResearch.WordTrace tailWord_2778499 prefixEnd_2778499 951136990024553229056281 := by
  unfold tailWord_2778499
  simp only [CollatzResearch.WordTrace]
  refine ⟨101340183960980127695058551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67560122640653418463372367 101340183960980127695058551)
  ·
    refine ⟨152010275941470191542587827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101340183960980127695058551 152010275941470191542587827)
    ·
      refine ⟨228015413912205287313881741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152010275941470191542587827 228015413912205287313881741)
      ·
        refine ⟨85505780217076982742705653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228015413912205287313881741 85505780217076982742705653)
        ·
          refine ⟨8016166895350967132128655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85505780217076982742705653 8016166895350967132128655)
          ·
            refine ⟨12024250343026450698192983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016166895350967132128655 12024250343026450698192983)
            ·
              refine ⟨18036375514539676047289475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12024250343026450698192983 18036375514539676047289475)
              ·
                refine ⟨27054563271809514070934213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18036375514539676047289475 27054563271809514070934213)
                ·
                  refine ⟨5072730613464283888300165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27054563271809514070934213 5072730613464283888300165)
                  ·
                    refine ⟨951136990024553229056281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5072730613464283888300165 951136990024553229056281)
                    ·
                      rfl

theorem cell22_2778499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_2778499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778499 prefixEnd_2778499 := by exact prefixLift 2778499
  have htrace : WordTrace (prefixWord ++ tailWord_2778499) baseStart_2778499 baseEnd_2778499 := by
    simpa [prefixWord, tailWord_2778499, baseEnd_2778499] using wordTrace_append hprefix tailTrace_2778499
  have hstable : (prefixWord ++ tailWord_2778499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778499).length < 2 ^ (prefixWord ++ tailWord_2778499).sum := by decide
  have hdescent : baseEnd_2778499 < baseStart_2778499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778503 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 4]
def baseStart_2778503 : Nat := 118140960795 + 2778503 * 2 ^ 59
def prefixEnd_2778503 : Nat := 4983230072969 + 3 ^ 40 * 2778503 * 2
def baseEnd_2778503 : Nat := 317046119768766183985423

theorem tailTrace_2778503 : CollatzResearch.WordTrace tailWord_2778503 prefixEnd_2778503 317046119768766183985423 := by
  unfold tailWord_2778503
  simp only [CollatzResearch.WordTrace]
  refine ⟨101340329852965636378204163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67560219901977090918802775 101340329852965636378204163)
  ·
    refine ⟨152010494779448454567306245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101340329852965636378204163 152010494779448454567306245)
    ·
      refine ⟨28501967771146585231369921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152010494779448454567306245 28501967771146585231369921)
      ·
        refine ⟨21376475828359938923527441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28501967771146585231369921 21376475828359938923527441)
        ·
          refine ⟨16032356871269954192645581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21376475828359938923527441 16032356871269954192645581)
          ·
            refine ⟨6012133826726232822242093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16032356871269954192645581 6012133826726232822242093)
            ·
              refine ⟨2254550185022337308340785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6012133826726232822242093 2254550185022337308340785)
              ·
                refine ⟨1690912638766752981255589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254550185022337308340785 1690912638766752981255589)
                ·
                  refine ⟨317046119768766183985423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690912638766752981255589 317046119768766183985423)
                  ·
                    rfl

theorem cell22_2778503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 4].length) (baseStart_2778503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778503 prefixEnd_2778503 := by exact prefixLift 2778503
  have htrace : WordTrace (prefixWord ++ tailWord_2778503) baseStart_2778503 baseEnd_2778503 := by
    simpa [prefixWord, tailWord_2778503, baseEnd_2778503] using wordTrace_append hprefix tailTrace_2778503
  have hstable : (prefixWord ++ tailWord_2778503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778503).length < 2 ^ (prefixWord ++ tailWord_2778503).sum := by decide
  have hdescent : baseEnd_2778503 < baseStart_2778503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778574 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2778574 : Nat := 118140960795 + 2778574 * 2 ^ 59
def prefixEnd_2778574 : Nat := 4983230072969 + 3 ^ 40 * 2778574 * 2
def baseEnd_2778574 : Nat := 951162664057278033431051

theorem tailTrace_2778574 : CollatzResearch.WordTrace tailWord_2778574 prefixEnd_2778574 951162664057278033431051 := by
  unfold tailWord_2778574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12667864929463551938004847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67561946290472277002692517 12667864929463551938004847)
  ·
    refine ⟨19001797394195327907007271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12667864929463551938004847 19001797394195327907007271)
    ·
      refine ⟨28502696091292991860510907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19001797394195327907007271 28502696091292991860510907)
      ·
        refine ⟨42754044136939487790766361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28502696091292991860510907 42754044136939487790766361)
        ·
          refine ⟨32065533102704615843074771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42754044136939487790766361 32065533102704615843074771)
          ·
            refine ⟨48098299654056923764612157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32065533102704615843074771 48098299654056923764612157)
            ·
              refine ⟨18036862370271346411729559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48098299654056923764612157 18036862370271346411729559)
              ·
                refine ⟨27055293555407019617594339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18036862370271346411729559 27055293555407019617594339)
                ·
                  refine ⟨40582940333110529426391509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27055293555407019617594339 40582940333110529426391509)
                  ·
                    refine ⟨951162664057278033431051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40582940333110529426391509 951162664057278033431051)
                    ·
                      rfl

theorem cell22_2778574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2778574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778574 prefixEnd_2778574 := by exact prefixLift 2778574
  have htrace : WordTrace (prefixWord ++ tailWord_2778574) baseStart_2778574 baseEnd_2778574 := by
    simpa [prefixWord, tailWord_2778574, baseEnd_2778574] using wordTrace_append hprefix tailTrace_2778574
  have hstable : (prefixWord ++ tailWord_2778574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778574).length < 2 ^ (prefixWord ++ tailWord_2778574).sum := by decide
  have hdescent : baseEnd_2778574 < baseStart_2778574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778621 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 6]
def baseStart_2778621 : Nat := 118140960795 + 2778621 * 2 ^ 59
def prefixEnd_2778621 : Nat := 4983230072969 + 3 ^ 40 * 2778621 * 2
def baseEnd_2778621 : Nat := 317059584372595192501969

theorem tailTrace_2778621 : CollatzResearch.WordTrace tailWord_2778621 prefixEnd_2778621 317059584372595192501969 := by
  unfold tailWord_2778621
  simp only [CollatzResearch.WordTrace]
  refine ⟨101344633666538142530999717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67563089111025428353999811 101344633666538142530999717)
  ·
    refine ⟨19002118812475901724562447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101344633666538142530999717 19002118812475901724562447)
    ·
      refine ⟨28503178218713852586843671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19002118812475901724562447 28503178218713852586843671)
      ·
        refine ⟨42754767328070778880265507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28503178218713852586843671 42754767328070778880265507)
        ·
          refine ⟨64132150992106168320398261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42754767328070778880265507 64132150992106168320398261)
          ·
            refine ⟨6012389155509953280037337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64132150992106168320398261 6012389155509953280037337)
            ·
              refine ⟨4509291866632464960028003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6012389155509953280037337 4509291866632464960028003)
              ·
                refine ⟨6763937799948697440042005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509291866632464960028003 6763937799948697440042005)
                ·
                  refine ⟨317059584372595192501969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6763937799948697440042005 317059584372595192501969)
                  ·
                    rfl

theorem cell22_2778621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_2778621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778621 prefixEnd_2778621 := by exact prefixLift 2778621
  have htrace : WordTrace (prefixWord ++ tailWord_2778621) baseStart_2778621 baseEnd_2778621 := by
    simpa [prefixWord, tailWord_2778621, baseEnd_2778621] using wordTrace_append hprefix tailTrace_2778621
  have hstable : (prefixWord ++ tailWord_2778621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778621).length < 2 ^ (prefixWord ++ tailWord_2778621).sum := by decide
  have hdescent : baseEnd_2778621 < baseStart_2778621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778728 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_2778728 : Nat := 118140960795 + 2778728 * 2 ^ 59
def prefixEnd_2778728 : Nat := 4983230072969 + 3 ^ 40 * 2778728 * 2
def baseEnd_2778728 : Nat := 317071793801490988360193

theorem tailTrace_2778728 : CollatzResearch.WordTrace tailWord_2778728 prefixEnd_2778728 317071793801490988360193 := by
  unfold tailWord_2778728
  simp only [CollatzResearch.WordTrace]
  refine ⟨50674268138575249902572419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67565690851433666536763225 50674268138575249902572419)
  ·
    refine ⟨76011402207862874853858629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50674268138575249902572419 76011402207862874853858629)
    ·
      refine ⟨14252137913974289035098493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76011402207862874853858629 14252137913974289035098493)
      ·
        refine ⟨5344551717740358388161935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14252137913974289035098493 5344551717740358388161935)
        ·
          refine ⟨8016827576610537582242903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344551717740358388161935 8016827576610537582242903)
          ·
            refine ⟨12025241364915806373364355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016827576610537582242903 12025241364915806373364355)
            ·
              refine ⟨18037862047373709560046533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12025241364915806373364355 18037862047373709560046533)
              ·
                refine ⟨3382099133882570542508725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18037862047373709560046533 3382099133882570542508725)
                ·
                  refine ⟨317071793801490988360193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3382099133882570542508725 317071793801490988360193)
                  ·
                    rfl

theorem cell22_2778728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_2778728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778728 prefixEnd_2778728 := by exact prefixLift 2778728
  have htrace : WordTrace (prefixWord ++ tailWord_2778728) baseStart_2778728 baseEnd_2778728 := by
    simpa [prefixWord, tailWord_2778728, baseEnd_2778728] using wordTrace_append hprefix tailTrace_2778728
  have hstable : (prefixWord ++ tailWord_2778728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778728).length < 2 ^ (prefixWord ++ tailWord_2778728).sum := by decide
  have hdescent : baseEnd_2778728 < baseStart_2778728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778775 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 1, 4]
def baseStart_2778775 : Nat := 118140960795 + 2778775 * 2 ^ 59
def prefixEnd_2778775 : Nat := 4983230072969 + 3 ^ 40 * 2778775 * 2
def baseEnd_2778775 : Nat := 951231470464980509155435

theorem tailTrace_2778775 : CollatzResearch.WordTrace tailWord_2778775 prefixEnd_2778775 951231470464980509155435 := by
  unfold tailWord_2778775
  simp only [CollatzResearch.WordTrace]
  refine ⟨101350250507980226832105779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67566833671986817888070519 101350250507980226832105779)
  ·
    refine ⟨152025375761970340248158669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101350250507980226832105779 152025375761970340248158669)
    ·
      refine ⟨57009515910738877593059501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152025375761970340248158669 57009515910738877593059501)
      ·
        refine ⟨21378568466527079097397313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57009515910738877593059501 21378568466527079097397313)
        ·
          refine ⟨16033926349895309323047985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21378568466527079097397313 16033926349895309323047985)
          ·
            refine ⟨12025444762421481992285989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16033926349895309323047985 12025444762421481992285989)
            ·
              refine ⟨2254770892954027873553623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12025444762421481992285989 2254770892954027873553623)
              ·
                refine ⟨3382156339431041810330435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254770892954027873553623 3382156339431041810330435)
                ·
                  refine ⟨5073234509146562715495653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382156339431041810330435 5073234509146562715495653)
                  ·
                    refine ⟨951231470464980509155435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5073234509146562715495653 951231470464980509155435)
                    ·
                      rfl

theorem cell22_2778775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_2778775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778775 prefixEnd_2778775 := by exact prefixLift 2778775
  have htrace : WordTrace (prefixWord ++ tailWord_2778775) baseStart_2778775 baseEnd_2778775 := by
    simpa [prefixWord, tailWord_2778775, baseEnd_2778775] using wordTrace_append hprefix tailTrace_2778775
  have hstable : (prefixWord ++ tailWord_2778775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778775).length < 2 ^ (prefixWord ++ tailWord_2778775).sum := by decide
  have hdescent : baseEnd_2778775 < baseStart_2778775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778816 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_2778816 : Nat := 118140960795 + 2778816 * 2 ^ 59
def prefixEnd_2778816 : Nat := 4983230072969 + 3 ^ 40 * 2778816 * 2
def baseEnd_2778816 : Nat := 951245505602870068880309

theorem tailTrace_2778816 : CollatzResearch.WordTrace tailWord_2778816 prefixEnd_2778816 951245505602870068880309 := by
  unfold tailWord_2778816
  simp only [CollatzResearch.WordTrace]
  refine ⟨50675872950415845417174151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67567830600554460556232201 50675872950415845417174151)
  ·
    refine ⟨76013809425623768125761227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50675872950415845417174151 76013809425623768125761227)
    ·
      refine ⟨114020714138435652188641841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76013809425623768125761227 114020714138435652188641841)
      ·
        refine ⟨85515535603826739141481381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114020714138435652188641841 85515535603826739141481381)
        ·
          refine ⟨16034162925717513589027759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85515535603826739141481381 16034162925717513589027759)
          ·
            refine ⟨24051244388576270383541639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16034162925717513589027759 24051244388576270383541639)
            ·
              refine ⟨36076866582864405575312459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24051244388576270383541639 36076866582864405575312459)
              ·
                refine ⟨54115299874296608362968689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36076866582864405575312459 54115299874296608362968689)
                ·
                  refine ⟨40586474905722456272226517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54115299874296608362968689 40586474905722456272226517)
                  ·
                    refine ⟨951245505602870068880309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40586474905722456272226517 951245505602870068880309)
                    ·
                      rfl

theorem cell22_2778816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_2778816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778816 prefixEnd_2778816 := by exact prefixLift 2778816
  have htrace : WordTrace (prefixWord ++ tailWord_2778816) baseStart_2778816 baseEnd_2778816 := by
    simpa [prefixWord, tailWord_2778816, baseEnd_2778816] using wordTrace_append hprefix tailTrace_2778816
  have hstable : (prefixWord ++ tailWord_2778816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778816).length < 2 ^ (prefixWord ++ tailWord_2778816).sum := by decide
  have hdescent : baseEnd_2778816 < baseStart_2778816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778863 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 5]
def baseStart_2778863 : Nat := 118140960795 + 2778863 * 2 ^ 59
def prefixEnd_2778863 : Nat := 4983230072969 + 3 ^ 40 * 2778863 * 2
def baseEnd_2778863 : Nat := 317087198221125870985055

theorem tailTrace_2778863 : CollatzResearch.WordTrace tailWord_2778863 prefixEnd_2778863 317087198221125870985055 := by
  unfold tailWord_2778863
  simp only [CollatzResearch.WordTrace]
  refine ⟨101353460131661417861309243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67568973421107611907539495 101353460131661417861309243)
  ·
    refine ⟨152030190197492126791963865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101353460131661417861309243 152030190197492126791963865)
    ·
      refine ⟨114022642648119095093972899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152030190197492126791963865 114022642648119095093972899)
      ·
        refine ⟨171033963972178642640959349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114022642648119095093972899 171033963972178642640959349)
        ·
          refine ⟨16034434122391747747589939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171033963972178642640959349 16034434122391747747589939)
          ·
            refine ⟨24051651183587621621384909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16034434122391747747589939 24051651183587621621384909)
            ·
              refine ⟨9019369193845358108019341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24051651183587621621384909 9019369193845358108019341)
              ·
                refine ⟨3382263447692009290507253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9019369193845358108019341 3382263447692009290507253)
                ·
                  refine ⟨317087198221125870985055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3382263447692009290507253 317087198221125870985055)
                  ·
                    rfl

theorem cell22_2778863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 5].length) (baseStart_2778863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778863 prefixEnd_2778863 := by exact prefixLift 2778863
  have htrace : WordTrace (prefixWord ++ tailWord_2778863) baseStart_2778863 baseEnd_2778863 := by
    simpa [prefixWord, tailWord_2778863, baseEnd_2778863] using wordTrace_append hprefix tailTrace_2778863
  have hstable : (prefixWord ++ tailWord_2778863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778863).length < 2 ^ (prefixWord ++ tailWord_2778863).sum := by decide
  have hdescent : baseEnd_2778863 < baseStart_2778863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778886 : List Nat := [6, 2, 2, 1, 2, 9]
def baseStart_2778886 : Nat := 118140960795 + 2778886 * 2 ^ 59
def prefixEnd_2778886 : Nat := 4983230072969 + 3 ^ 40 * 2778886 * 2
def baseEnd_2778886 : Nat := 11744067506585348390495

theorem tailTrace_2778886 : CollatzResearch.WordTrace tailWord_2778886 prefixEnd_2778886 11744067506585348390495 := by
  unfold tailWord_2778886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167321844080565399668641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67569532673718728526264341 3167321844080565399668641)
  ·
    refine ⟨2375491383060424049751481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3167321844080565399668641 2375491383060424049751481)
    ·
      refine ⟨1781618537295318037313611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375491383060424049751481 1781618537295318037313611)
      ·
        refine ⟨2672427805942977055970417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781618537295318037313611 2672427805942977055970417)
        ·
          refine ⟨2004320854457232791977813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2672427805942977055970417 2004320854457232791977813)
          ·
            refine ⟨11744067506585348390495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2004320854457232791977813 11744067506585348390495)
            ·
              rfl

theorem cell22_2778886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 9].length) (baseStart_2778886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778886 prefixEnd_2778886 := by exact prefixLift 2778886
  have htrace : WordTrace (prefixWord ++ tailWord_2778886) baseStart_2778886 baseEnd_2778886 := by
    simpa [prefixWord, tailWord_2778886, baseEnd_2778886] using wordTrace_append hprefix tailTrace_2778886
  have hstable : (prefixWord ++ tailWord_2778886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778886).length < 2 ^ (prefixWord ++ tailWord_2778886).sum := by decide
  have hdescent : baseEnd_2778886 < baseStart_2778886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778908 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_2778908 : Nat := 118140960795 + 2778908 * 2 ^ 59
def prefixEnd_2778908 : Nat := 4983230072969 + 3 ^ 40 * 2778908 * 2
def baseEnd_2778908 : Nat := 317092333027670831860009

theorem tailTrace_2778908 : CollatzResearch.WordTrace tailWord_2778908 prefixEnd_2778908 317092333027670831860009 := by
  unfold tailWord_2778908
  simp only [CollatzResearch.WordTrace]
  refine ⟨50677550708249195273348689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67570067610998927031131585 50677550708249195273348689)
  ·
    refine ⟨38008163031186896455011517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50677550708249195273348689 38008163031186896455011517)
    ·
      refine ⟨14253061136695086170629319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38008163031186896455011517 14253061136695086170629319)
      ·
        refine ⟨21379591705042629255943979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14253061136695086170629319 21379591705042629255943979)
        ·
          refine ⟨32069387557563943883915969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21379591705042629255943979 32069387557563943883915969)
          ·
            refine ⟨24052040668172957912936977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32069387557563943883915969 24052040668172957912936977)
            ·
              refine ⟨18039030501129718434702733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24052040668172957912936977 18039030501129718434702733)
              ·
                refine ⟨6764636437923644413013525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18039030501129718434702733 6764636437923644413013525)
                ·
                  refine ⟨317092333027670831860009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6764636437923644413013525 317092333027670831860009)
                  ·
                    rfl

theorem cell22_2778908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_2778908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778908 prefixEnd_2778908 := by exact prefixLift 2778908
  have htrace : WordTrace (prefixWord ++ tailWord_2778908) baseStart_2778908 baseEnd_2778908 := by
    simpa [prefixWord, tailWord_2778908, baseEnd_2778908] using wordTrace_append hprefix tailTrace_2778908
  have hstable : (prefixWord ++ tailWord_2778908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778908).length < 2 ^ (prefixWord ++ tailWord_2778908).sum := by decide
  have hdescent : baseEnd_2778908 < baseStart_2778908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778942 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_2778942 : Nat := 118140960795 + 2778942 * 2 ^ 59
def prefixEnd_2778942 : Nat := 4983230072969 + 3 ^ 40 * 2778942 * 2
def baseEnd_2778942 : Nat := 317096212659282580076641

theorem tailTrace_2778942 : CollatzResearch.WordTrace tailWord_2778942 prefixEnd_2778942 317096212659282580076641 := by
  unfold tailWord_2778942
  simp only [CollatzResearch.WordTrace]
  refine ⟨12669542687296901794179385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67570894332250142902290053 12669542687296901794179385)
  ·
    refine ⟨9502157015472676345634539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12669542687296901794179385 9502157015472676345634539)
    ·
      refine ⟨14253235523209014518451809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9502157015472676345634539 14253235523209014518451809)
      ·
        refine ⟨10689926642406760888838857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14253235523209014518451809 10689926642406760888838857)
        ·
          refine ⟨8017444981805070666629143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10689926642406760888838857 8017444981805070666629143)
          ·
            refine ⟨12026167472707605999943715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8017444981805070666629143 12026167472707605999943715)
            ·
              refine ⟨18039251209061408999915573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12026167472707605999943715 18039251209061408999915573)
              ·
                refine ⟨1691179800849507093742085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18039251209061408999915573 1691179800849507093742085)
                ·
                  refine ⟨317096212659282580076641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691179800849507093742085 317096212659282580076641)
                  ·
                    rfl

theorem cell22_2778942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2778942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2778942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2778942 prefixEnd_2778942 := by exact prefixLift 2778942
  have htrace : WordTrace (prefixWord ++ tailWord_2778942) baseStart_2778942 baseEnd_2778942 := by
    simpa [prefixWord, tailWord_2778942, baseEnd_2778942] using wordTrace_append hprefix tailTrace_2778942
  have hstable : (prefixWord ++ tailWord_2778942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778942).length < 2 ^ (prefixWord ++ tailWord_2778942).sum := by decide
  have hdescent : baseEnd_2778942 < baseStart_2778942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779043 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 8]
def baseStart_2779043 : Nat := 118140960795 + 2779043 * 2 ^ 59
def prefixEnd_2779043 : Nat := 4983230072969 + 3 ^ 40 * 2779043 * 2
def baseEnd_2779043 : Nat := 317107737447305714484871

theorem tailTrace_2779043 : CollatzResearch.WordTrace tailWord_2779043 prefixEnd_2779043 317107737447305714484871 := by
  unfold tailWord_2779043
  simp only [CollatzResearch.WordTrace]
  refine ⟨101360025271009308602861783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67573350180672872401907855 101360025271009308602861783)
  ·
    refine ⟨152040037906513962904292675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101360025271009308602861783 152040037906513962904292675)
    ·
      refine ⟨228060056859770944356439013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152040037906513962904292675 228060056859770944356439013)
      ·
        refine ⟨42761260661207052066832315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228060056859770944356439013 42761260661207052066832315)
        ·
          refine ⟨64141890991810578100248473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42761260661207052066832315 64141890991810578100248473)
          ·
            refine ⟨48106418243857933575186355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64141890991810578100248473 48106418243857933575186355)
            ·
              refine ⟨72159627365786900362779533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48106418243857933575186355 72159627365786900362779533)
              ·
                refine ⟨27059860262170087636042325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72159627365786900362779533 27059860262170087636042325)
                ·
                  refine ⟨317107737447305714484871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27059860262170087636042325 317107737447305714484871)
                  ·
                    rfl

theorem cell22_2779043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_2779043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779043 prefixEnd_2779043 := by exact prefixLift 2779043
  have htrace : WordTrace (prefixWord ++ tailWord_2779043) baseStart_2779043 baseEnd_2779043 := by
    simpa [prefixWord, tailWord_2779043, baseEnd_2779043] using wordTrace_append hprefix tailTrace_2779043
  have hstable : (prefixWord ++ tailWord_2779043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779043).length < 2 ^ (prefixWord ++ tailWord_2779043).sum := by decide
  have hdescent : baseEnd_2779043 < baseStart_2779043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779092 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2779092 : Nat := 118140960795 + 2779092 * 2 ^ 59
def prefixEnd_2779092 : Nat := 4983230072969 + 3 ^ 40 * 2779092 * 2
def baseEnd_2779092 : Nat := 951339986043297348979463

theorem tailTrace_2779092 : CollatzResearch.WordTrace tailWord_2779092 prefixEnd_2779092 951339986043297348979463 := by
  unfold tailWord_2779092
  simp only [CollatzResearch.WordTrace]
  refine ⟨50680906223915894985697765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67574541631887859980930353 50680906223915894985697765)
  ·
    refine ⟨9502669916984230309818331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50680906223915894985697765 9502669916984230309818331)
    ·
      refine ⟨14254004875476345464727497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9502669916984230309818331 14254004875476345464727497)
      ·
        refine ⟨10690503656607259098545623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14254004875476345464727497 10690503656607259098545623)
        ·
          refine ⟨16035755484910888647818435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690503656607259098545623 16035755484910888647818435)
          ·
            refine ⟨24053633227366332971727653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16035755484910888647818435 24053633227366332971727653)
            ·
              refine ⟨4510056230131187432198935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24053633227366332971727653 4510056230131187432198935)
              ·
                refine ⟨6765084345196781148298403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510056230131187432198935 6765084345196781148298403)
                ·
                  refine ⟨10147626517795171722447605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765084345196781148298403 10147626517795171722447605)
                  ·
                    refine ⟨951339986043297348979463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10147626517795171722447605 951339986043297348979463)
                    ·
                      rfl

theorem cell22_2779092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2779092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779092 prefixEnd_2779092 := by exact prefixLift 2779092
  have htrace : WordTrace (prefixWord ++ tailWord_2779092) baseStart_2779092 baseEnd_2779092 := by
    simpa [prefixWord, tailWord_2779092, baseEnd_2779092] using wordTrace_append hprefix tailTrace_2779092
  have hstable : (prefixWord ++ tailWord_2779092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779092).length < 2 ^ (prefixWord ++ tailWord_2779092).sum := by decide
  have hdescent : baseEnd_2779092 < baseStart_2779092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779094 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2779094 : Nat := 118140960795 + 2779094 * 2 ^ 59
def prefixEnd_2779094 : Nat := 4983230072969 + 3 ^ 40 * 2779094 * 2
def baseEnd_2779094 : Nat := 317113556894723336809819

theorem tailTrace_2779094 : CollatzResearch.WordTrace tailWord_2779094 prefixEnd_2779094 317113556894723336809819 := by
  unfold tailWord_2779094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335117837114034019560521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67574590262549696208645557 6335117837114034019560521)
  ·
    refine ⟨4751338377835525514670391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6335117837114034019560521 4751338377835525514670391)
    ·
      refine ⟨7127007566753288272005587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751338377835525514670391 7127007566753288272005587)
      ·
        refine ⟨10690511350129932408008381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127007566753288272005587 10690511350129932408008381)
        ·
          refine ⟨4008941756298724653003143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10690511350129932408008381 4008941756298724653003143)
          ·
            refine ⟨6013412634448086979504715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008941756298724653003143 6013412634448086979504715)
            ·
              refine ⟨9020118951672130469257073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013412634448086979504715 9020118951672130469257073)
              ·
                refine ⟨6765089213754097851942805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9020118951672130469257073 6765089213754097851942805)
                ·
                  refine ⟨317113556894723336809819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6765089213754097851942805 317113556894723336809819)
                  ·
                    rfl

theorem cell22_2779094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2779094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779094 prefixEnd_2779094 := by exact prefixLift 2779094
  have htrace : WordTrace (prefixWord ++ tailWord_2779094) baseStart_2779094 baseEnd_2779094 := by
    simpa [prefixWord, tailWord_2779094, baseEnd_2779094] using wordTrace_append hprefix tailTrace_2779094
  have hstable : (prefixWord ++ tailWord_2779094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779094).length < 2 ^ (prefixWord ++ tailWord_2779094).sum := by decide
  have hdescent : baseEnd_2779094 < baseStart_2779094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779107 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 2, 4]
def baseStart_2779107 : Nat := 118140960795 + 2779107 * 2 ^ 59
def prefixEnd_2779107 : Nat := 4983230072969 + 3 ^ 40 * 2779107 * 2
def baseEnd_2779107 : Nat := 951345120849842309854417

theorem tailTrace_2779107 : CollatzResearch.WordTrace tailWord_2779107 prefixEnd_2779107 951345120849842309854417 := by
  unfold tailWord_2779107
  simp only [CollatzResearch.WordTrace]
  refine ⟨101362359542777447533191575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67574906361851631688794383 101362359542777447533191575)
  ·
    refine ⟨152043539314166171299787363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101362359542777447533191575 152043539314166171299787363)
    ·
      refine ⟨228065308971249256949681045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152043539314166171299787363 228065308971249256949681045)
      ·
        refine ⟨10690561358027308919516299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228065308971249256949681045 10690561358027308919516299)
        ·
          refine ⟨16035842037040963379274449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690561358027308919516299 16035842037040963379274449)
          ·
            refine ⟨12026881527780722534455837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16035842037040963379274449 12026881527780722534455837)
            ·
              refine ⟨4510080572917770950420939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12026881527780722534455837 4510080572917770950420939)
              ·
                refine ⟨6765120859376656425631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510080572917770950420939 6765120859376656425631409)
                ·
                  refine ⟨5073840644532492319223557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6765120859376656425631409 5073840644532492319223557)
                  ·
                    refine ⟨951345120849842309854417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5073840644532492319223557 951345120849842309854417)
                    ·
                      rfl

theorem cell22_2779107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 4].length) (baseStart_2779107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779107 prefixEnd_2779107 := by exact prefixLift 2779107
  have htrace : WordTrace (prefixWord ++ tailWord_2779107) baseStart_2779107 baseEnd_2779107 := by
    simpa [prefixWord, tailWord_2779107, baseEnd_2779107] using wordTrace_append hprefix tailTrace_2779107
  have hstable : (prefixWord ++ tailWord_2779107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779107).length < 2 ^ (prefixWord ++ tailWord_2779107).sum := by decide
  have hdescent : baseEnd_2779107 < baseStart_2779107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779188 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2779188 : Nat := 118140960795 + 2779188 * 2 ^ 59
def prefixEnd_2779188 : Nat := 4983230072969 + 3 ^ 40 * 2779188 * 2
def baseEnd_2779188 : Nat := 951372848805185098579169

theorem tailTrace_2779188 : CollatzResearch.WordTrace tailWord_2779188 prefixEnd_2779188 951372848805185098579169 := by
  unfold tailWord_2779188
  simp only [CollatzResearch.WordTrace]
  refine ⟨50682656927741999183445109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67576875903655998911260145 50682656927741999183445109)
  ·
    refine ⟨4751499086975812423447979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50682656927741999183445109 4751499086975812423447979)
    ·
      refine ⟨7127248630463718635171969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751499086975812423447979 7127248630463718635171969)
      ·
        refine ⟨5345436472847788976378977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7127248630463718635171969 5345436472847788976378977)
        ·
          refine ⟨4009077354635841732284233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5345436472847788976378977 4009077354635841732284233)
          ·
            refine ⟨3006808015976881299213175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4009077354635841732284233 3006808015976881299213175)
            ·
              refine ⟨4510212023965321948819763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006808015976881299213175 4510212023965321948819763)
              ·
                refine ⟨6765318035947982923229645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510212023965321948819763 6765318035947982923229645)
                ·
                  refine ⟨2536994263480493596211117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6765318035947982923229645 2536994263480493596211117)
                  ·
                    refine ⟨951372848805185098579169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536994263480493596211117 951372848805185098579169)
                    ·
                      rfl

theorem cell22_2779188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2779188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779188 prefixEnd_2779188 := by exact prefixLift 2779188
  have htrace : WordTrace (prefixWord ++ tailWord_2779188) baseStart_2779188 baseEnd_2779188 := by
    simpa [prefixWord, tailWord_2779188, baseEnd_2779188] using wordTrace_append hprefix tailTrace_2779188
  have hstable : (prefixWord ++ tailWord_2779188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779188).length < 2 ^ (prefixWord ++ tailWord_2779188).sum := by decide
  have hdescent : baseEnd_2779188 < baseStart_2779188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779197 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2779197 : Nat := 118140960795 + 2779197 * 2 ^ 59
def prefixEnd_2779197 : Nat := 4983230072969 + 3 ^ 40 * 2779197 * 2
def baseEnd_2779197 : Nat := 951375929689112075104141

theorem tailTrace_2779197 : CollatzResearch.WordTrace tailWord_2779197 prefixEnd_2779197 951375929689112075104141 := by
  unfold tailWord_2779197
  simp only [CollatzResearch.WordTrace]
  refine ⟨101365642112451392903967845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67577094741634261935978563 101365642112451392903967845)
  ·
    refine ⟨19006057896084636169493971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101365642112451392903967845 19006057896084636169493971)
    ·
      refine ⟨28509086844126954254240957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19006057896084636169493971 28509086844126954254240957)
      ·
        refine ⟨10690907566547607845340359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28509086844126954254240957 10690907566547607845340359)
        ·
          refine ⟨16036361349821411768010539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690907566547607845340359 16036361349821411768010539)
          ·
            refine ⟨24054542024732117652015809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036361349821411768010539 24054542024732117652015809)
            ·
              refine ⟨18040906518549088239011857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24054542024732117652015809 18040906518549088239011857)
              ·
                refine ⟨13530679888911816179258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18040906518549088239011857 13530679888911816179258893)
                ·
                  refine ⟨5074004958341931067222085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13530679888911816179258893 5074004958341931067222085)
                  ·
                    refine ⟨951375929689112075104141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5074004958341931067222085 951375929689112075104141)
                    ·
                      rfl

theorem cell22_2779197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2779197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779197 prefixEnd_2779197 := by exact prefixLift 2779197
  have htrace : WordTrace (prefixWord ++ tailWord_2779197) baseStart_2779197 baseEnd_2779197 := by
    simpa [prefixWord, tailWord_2779197, baseEnd_2779197] using wordTrace_append hprefix tailTrace_2779197
  have hstable : (prefixWord ++ tailWord_2779197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779197).length < 2 ^ (prefixWord ++ tailWord_2779197).sum := by decide
  have hdescent : baseEnd_2779197 < baseStart_2779197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779201 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 5]
def baseStart_2779201 : Nat := 118140960795 + 2779201 * 2 ^ 59
def prefixEnd_2779201 : Nat := 4983230072969 + 3 ^ 40 * 2779201 * 2
def baseEnd_2779201 : Nat := 317125766323619132668043

theorem tailTrace_2779201 : CollatzResearch.WordTrace tailWord_2779201 prefixEnd_2779201 317125766323619132668043 := by
  unfold tailWord_2779201
  simp only [CollatzResearch.WordTrace]
  refine ⟨101365788004436901587113457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67577192002957934391408971 101365788004436901587113457)
  ·
    refine ⟨76024341003327676190335093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101365788004436901587113457 76024341003327676190335093)
    ·
      refine ⟨7127281969061969642843915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76024341003327676190335093 7127281969061969642843915)
      ·
        refine ⟨10690922953592954464265873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127281969061969642843915 10690922953592954464265873)
        ·
          refine ⟨8018192215194715848199405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10690922953592954464265873 8018192215194715848199405)
          ·
            refine ⟨3006822080698018443074777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8018192215194715848199405 3006822080698018443074777)
            ·
              refine ⟨2255116560523513832306083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3006822080698018443074777 2255116560523513832306083)
              ·
                refine ⟨3382674840785270748459125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255116560523513832306083 3382674840785270748459125)
                ·
                  refine ⟨317125766323619132668043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3382674840785270748459125 317125766323619132668043)
                  ·
                    rfl

theorem cell22_2779201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_2779201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779201 prefixEnd_2779201 := by exact prefixLift 2779201
  have htrace : WordTrace (prefixWord ++ tailWord_2779201) baseStart_2779201 baseEnd_2779201 := by
    simpa [prefixWord, tailWord_2779201, baseEnd_2779201] using wordTrace_append hprefix tailTrace_2779201
  have hstable : (prefixWord ++ tailWord_2779201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779201).length < 2 ^ (prefixWord ++ tailWord_2779201).sum := by decide
  have hdescent : baseEnd_2779201 < baseStart_2779201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779214 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_2779214 : Nat := 118140960795 + 2779214 * 2 ^ 59
def prefixEnd_2779214 : Nat := 4983230072969 + 3 ^ 40 * 2779214 * 2
def baseEnd_2779214 : Nat := 951381749136529697429089

theorem tailTrace_2779214 : CollatzResearch.WordTrace tailWord_2779214 prefixEnd_2779214 951381749136529697429089 := by
  unfold tailWord_2779214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12670782769173725600917087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67577508102259869871557797 12670782769173725600917087)
  ·
    refine ⟨19006174153760588401375631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12670782769173725600917087 19006174153760588401375631)
    ·
      refine ⟨28509261230640882602063447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19006174153760588401375631 28509261230640882602063447)
      ·
        refine ⟨42763891845961323903095171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28509261230640882602063447 42763891845961323903095171)
        ·
          refine ⟨64145837768941985854642757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42763891845961323903095171 64145837768941985854642757)
          ·
            refine ⟨12027344581676622347745517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64145837768941985854642757 12027344581676622347745517)
            ·
              refine ⟨4510254218128733380404569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12027344581676622347745517 4510254218128733380404569)
              ·
                refine ⟨3382690663596550035303427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510254218128733380404569 3382690663596550035303427)
                ·
                  refine ⟨5074035995394825052955141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382690663596550035303427 5074035995394825052955141)
                  ·
                    refine ⟨951381749136529697429089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5074035995394825052955141 951381749136529697429089)
                    ·
                      rfl

theorem cell22_2779214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_2779214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779214 prefixEnd_2779214 := by exact prefixLift 2779214
  have htrace : WordTrace (prefixWord ++ tailWord_2779214) baseStart_2779214 baseEnd_2779214 := by
    simpa [prefixWord, tailWord_2779214, baseEnd_2779214] using wordTrace_append hprefix tailTrace_2779214
  have hstable : (prefixWord ++ tailWord_2779214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779214).length < 2 ^ (prefixWord ++ tailWord_2779214).sum := by decide
  have hdescent : baseEnd_2779214 < baseStart_2779214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779240 : List Nat := [2, 1, 4, 15]
def baseStart_2779240 : Nat := 118140960795 + 2779240 * 2 ^ 59
def prefixEnd_2779240 : Nat := 4983230072969 + 3 ^ 40 * 2779240 * 2
def baseEnd_2779240 : Nat := 1305062619297495605321

theorem tailTrace_2779240 : CollatzResearch.WordTrace tailWord_2779240 prefixEnd_2779240 1305062619297495605321 := by
  unfold tailWord_2779240
  simp only [CollatzResearch.WordTrace]
  refine ⟨50683605225647805623891587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67578140300863740831855449 50683605225647805623891587)
  ·
    refine ⟨76025407838471708435837381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50683605225647805623891587 76025407838471708435837381)
    ·
      refine ⟨14254763969713445331719509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76025407838471708435837381 14254763969713445331719509)
      ·
        refine ⟨1305062619297495605321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 14254763969713445331719509 1305062619297495605321)
        ·
          rfl

theorem cell22_2779240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 15].length) (baseStart_2779240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779240 prefixEnd_2779240 := by exact prefixLift 2779240
  have htrace : WordTrace (prefixWord ++ tailWord_2779240) baseStart_2779240 baseEnd_2779240 := by
    simpa [prefixWord, tailWord_2779240, baseEnd_2779240] using wordTrace_append hprefix tailTrace_2779240
  have hstable : (prefixWord ++ tailWord_2779240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779240).length < 2 ^ (prefixWord ++ tailWord_2779240).sum := by decide
  have hdescent : baseEnd_2779240 < baseStart_2779240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779244 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_2779244 : Nat := 118140960795 + 2779244 * 2 ^ 59
def prefixEnd_2779244 : Nat := 4983230072969 + 3 ^ 40 * 2779244 * 2
def baseEnd_2779244 : Nat := 951392018749619619178997

theorem tailTrace_2779244 : CollatzResearch.WordTrace tailWord_2779244 prefixEnd_2779244 951392018749619619178997 := by
  unfold tailWord_2779244
  simp only [CollatzResearch.WordTrace]
  refine ⟨50683678171640559965464393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67578237562187413287285857 50683678171640559965464393)
  ·
    refine ⟨38012758628730419974098295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50683678171640559965464393 38012758628730419974098295)
    ·
      refine ⟨57019137943095629961147443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38012758628730419974098295 57019137943095629961147443)
      ·
        refine ⟨85528706914643444941721165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57019137943095629961147443 85528706914643444941721165)
        ·
          refine ⟨32073265092991291853145437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85528706914643444941721165 32073265092991291853145437)
          ·
            refine ⟨12027474409871734444929539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32073265092991291853145437 12027474409871734444929539)
            ·
              refine ⟨18041211614807601667394309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12027474409871734444929539 18041211614807601667394309)
              ·
                refine ⟨3382727177776425312636433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18041211614807601667394309 3382727177776425312636433)
                ·
                  refine ⟨2537045383332318984477325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382727177776425312636433 2537045383332318984477325)
                  ·
                    refine ⟨951392018749619619178997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2537045383332318984477325 951392018749619619178997)
                    ·
                      rfl

theorem cell22_2779244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_2779244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779244 prefixEnd_2779244 := by exact prefixLift 2779244
  have htrace : WordTrace (prefixWord ++ tailWord_2779244) baseStart_2779244 baseEnd_2779244 := by
    simpa [prefixWord, tailWord_2779244, baseEnd_2779244] using wordTrace_append hprefix tailTrace_2779244
  have hstable : (prefixWord ++ tailWord_2779244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779244).length < 2 ^ (prefixWord ++ tailWord_2779244).sum := by decide
  have hdescent : baseEnd_2779244 < baseStart_2779244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779257 : List Nat := [1, 2, 1, 3, 4, 1, 3, 7]
def baseStart_2779257 : Nat := 118140960795 + 2779257 * 2 ^ 59
def prefixEnd_2779257 : Nat := 4983230072969 + 3 ^ 40 * 2779257 * 2
def baseEnd_2779257 : Nat := 105710718768365768733773

theorem tailTrace_2779257 : CollatzResearch.WordTrace tailWord_2779257 prefixEnd_2779257 105710718768365768733773 := by
  unfold tailWord_2779257
  simp only [CollatzResearch.WordTrace]
  refine ⟨101367830492234023151152025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67578553661489348767434683 101367830492234023151152025)
  ·
    refine ⟨76025872869175517363364019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101367830492234023151152025 76025872869175517363364019)
    ·
      refine ⟨114038809303763276045046029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76025872869175517363364019 114038809303763276045046029)
      ·
        refine ⟨42764553488911228516892261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114038809303763276045046029 42764553488911228516892261)
        ·
          refine ⟨8018353779170855346917299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42764553488911228516892261 8018353779170855346917299)
          ·
            refine ⟨12027530668756283020375949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8018353779170855346917299 12027530668756283020375949)
            ·
              refine ⟨4510324000783606132640981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12027530668756283020375949 4510324000783606132640981)
              ·
                refine ⟨105710718768365768733773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4510324000783606132640981 105710718768365768733773)
                ·
                  rfl

theorem cell22_2779257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 7].length) (baseStart_2779257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779257 prefixEnd_2779257 := by exact prefixLift 2779257
  have htrace : WordTrace (prefixWord ++ tailWord_2779257) baseStart_2779257 baseEnd_2779257 := by
    simpa [prefixWord, tailWord_2779257, baseEnd_2779257] using wordTrace_append hprefix tailTrace_2779257
  have hstable : (prefixWord ++ tailWord_2779257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779257).length < 2 ^ (prefixWord ++ tailWord_2779257).sum := by decide
  have hdescent : baseEnd_2779257 < baseStart_2779257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779274 : List Nat := [3, 1, 2, 3, 1, 3, 3, 6]
def baseStart_2779274 : Nat := 118140960795 + 2779274 * 2 ^ 59
def prefixEnd_2779274 : Nat := 4983230072969 + 3 ^ 40 * 2779274 * 2
def baseEnd_2779274 : Nat := 105711365373634393436545

theorem tailTrace_2779274 : CollatzResearch.WordTrace tailWord_2779274 prefixEnd_2779274 105711365373634393436545 := by
  unfold tailWord_2779274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342112633293108763630219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67578967022114956703013917 25342112633293108763630219)
  ·
    refine ⟨38013168949939663145445329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25342112633293108763630219 38013168949939663145445329)
    ·
      refine ⟨28509876712454747359083997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38013168949939663145445329 28509876712454747359083997)
      ·
        refine ⟨10691203767170530259656499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28509876712454747359083997 10691203767170530259656499)
        ·
          refine ⟨16036805650755795389484749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10691203767170530259656499 16036805650755795389484749)
          ·
            refine ⟨6013802119033423271056781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16036805650755795389484749 6013802119033423271056781)
            ·
              refine ⟨2255175794637533726646293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6013802119033423271056781 2255175794637533726646293)
              ·
                refine ⟨105711365373634393436545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2255175794637533726646293 105711365373634393436545)
                ·
                  rfl

theorem cell22_2779274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_2779274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779274 prefixEnd_2779274 := by exact prefixLift 2779274
  have htrace : WordTrace (prefixWord ++ tailWord_2779274) baseStart_2779274 baseEnd_2779274 := by
    simpa [prefixWord, tailWord_2779274, baseEnd_2779274] using wordTrace_append hprefix tailTrace_2779274
  have hstable : (prefixWord ++ tailWord_2779274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779274).length < 2 ^ (prefixWord ++ tailWord_2779274).sum := by decide
  have hdescent : baseEnd_2779274 < baseStart_2779274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779377 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2779377 : Nat := 118140960795 + 2779377 * 2 ^ 59
def prefixEnd_2779377 : Nat := 4983230072969 + 3 ^ 40 * 2779377 * 2
def baseEnd_2779377 : Nat := 951437547367651605603589

theorem tailTrace_2779377 : CollatzResearch.WordTrace tailWord_2779377 prefixEnd_2779377 951437547367651605603589 := by
  unfold tailWord_2779377
  simp only [CollatzResearch.WordTrace]
  refine ⟨101372207251799283645520385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67581471501199522430346923 101372207251799283645520385)
  ·
    refine ⟨76029155438849462734140289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101372207251799283645520385 76029155438849462734140289)
    ·
      refine ⟨57021866579137097050605217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76029155438849462734140289 57021866579137097050605217)
      ·
        refine ⟨42766399934352822787953913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57021866579137097050605217 42766399934352822787953913)
        ·
          refine ⟨32074799950764617090965435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42766399934352822787953913 32074799950764617090965435)
          ·
            refine ⟨48112199926146925636448153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32074799950764617090965435 48112199926146925636448153)
            ·
              refine ⟨36084149944610194227336115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48112199926146925636448153 36084149944610194227336115)
              ·
                refine ⟨54126224916915291341004173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36084149944610194227336115 54126224916915291341004173)
                ·
                  refine ⟨20297334343843234252876565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54126224916915291341004173 20297334343843234252876565)
                  ·
                    refine ⟨951437547367651605603589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20297334343843234252876565 951437547367651605603589)
                    ·
                      rfl

theorem cell22_2779377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2779377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779377 prefixEnd_2779377 := by exact prefixLift 2779377
  have htrace : WordTrace (prefixWord ++ tailWord_2779377) baseStart_2779377 baseEnd_2779377 := by
    simpa [prefixWord, tailWord_2779377, baseEnd_2779377] using wordTrace_append hprefix tailTrace_2779377
  have hstable : (prefixWord ++ tailWord_2779377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779377).length < 2 ^ (prefixWord ++ tailWord_2779377).sum := by decide
  have hdescent : baseEnd_2779377 < baseStart_2779377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779392 : List Nat := [2, 1, 1, 2, 1, 1, 6, 8]
def baseStart_2779392 : Nat := 118140960795 + 2779392 * 2 ^ 59
def prefixEnd_2779392 : Nat := 4983230072969 + 3 ^ 40 * 2779392 * 2
def baseEnd_2779392 : Nat := 105715853574910729608727

theorem tailTrace_2779392 : CollatzResearch.WordTrace tailWord_2779392 prefixEnd_2779392 105715853574910729608727 := by
  unfold tailWord_2779392
  simp only [CollatzResearch.WordTrace]
  refine ⟨50686377173372470603658215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67581836231163294138210953 50686377173372470603658215)
  ·
    refine ⟨76029565760058705905487323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50686377173372470603658215 76029565760058705905487323)
    ·
      refine ⟨114044348640088058858230985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76029565760058705905487323 114044348640088058858230985)
      ·
        refine ⟨85533261480066044143673239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114044348640088058858230985 85533261480066044143673239)
        ·
          refine ⟨128299892220099066215509859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85533261480066044143673239 128299892220099066215509859)
          ·
            refine ⟨192449838330148599323264789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128299892220099066215509859 192449838330148599323264789)
            ·
              refine ⟨9021086171725715593278037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192449838330148599323264789 9021086171725715593278037)
              ·
                refine ⟨105715853574910729608727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9021086171725715593278037 105715853574910729608727)
                ·
                  rfl

theorem cell22_2779392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_2779392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779392 prefixEnd_2779392 := by exact prefixLift 2779392
  have htrace : WordTrace (prefixWord ++ tailWord_2779392) baseStart_2779392 baseEnd_2779392 := by
    simpa [prefixWord, tailWord_2779392, baseEnd_2779392] using wordTrace_append hprefix tailTrace_2779392
  have hstable : (prefixWord ++ tailWord_2779392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779392).length < 2 ^ (prefixWord ++ tailWord_2779392).sum := by decide
  have hdescent : baseEnd_2779392 < baseStart_2779392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779396 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2779396 : Nat := 118140960795 + 2779396 * 2 ^ 59
def prefixEnd_2779396 : Nat := 4983230072969 + 3 ^ 40 * 2779396 * 2
def baseEnd_2779396 : Nat := 951444051455941889378531

theorem tailTrace_2779396 : CollatzResearch.WordTrace tailWord_2779396 prefixEnd_2779396 951444051455941889378531 := by
  unfold tailWord_2779396
  simp only [CollatzResearch.WordTrace]
  refine ⟨50686450119365224945231021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67581933492486966593641361 50686450119365224945231021)
  ·
    refine ⟨19007418794761959354461633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50686450119365224945231021 19007418794761959354461633)
    ·
      refine ⟨14255564096071469515846225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19007418794761959354461633 14255564096071469515846225)
      ·
        refine ⟨10691673072053602136884669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14255564096071469515846225 10691673072053602136884669)
        ·
          refine ⟨4009377402020100801331751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10691673072053602136884669 4009377402020100801331751)
          ·
            refine ⟨6014066103030151201997627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009377402020100801331751 6014066103030151201997627)
            ·
              refine ⟨9021099154545226802996441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6014066103030151201997627 9021099154545226802996441)
              ·
                refine ⟨6765824365908920102247331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9021099154545226802996441 6765824365908920102247331)
                ·
                  refine ⟨10148736548863380153370997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765824365908920102247331 10148736548863380153370997)
                  ·
                    refine ⟨951444051455941889378531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10148736548863380153370997 951444051455941889378531)
                    ·
                      rfl

theorem cell22_2779396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2779396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779396 prefixEnd_2779396 := by exact prefixLift 2779396
  have htrace : WordTrace (prefixWord ++ tailWord_2779396) baseStart_2779396 baseEnd_2779396 := by
    simpa [prefixWord, tailWord_2779396, baseEnd_2779396] using wordTrace_append hprefix tailTrace_2779396
  have hstable : (prefixWord ++ tailWord_2779396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779396).length < 2 ^ (prefixWord ++ tailWord_2779396).sum := by decide
  have hdescent : baseEnd_2779396 < baseStart_2779396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779426 : List Nat := [3, 3, 1, 1, 3, 3, 1, 7]
def baseStart_2779426 : Nat := 118140960795 + 2779426 * 2 ^ 59
def prefixEnd_2779426 : Nat := 4983230072969 + 3 ^ 40 * 2779426 * 2
def baseEnd_2779426 : Nat := 105717146785447979014271

theorem tailTrace_2779426 : CollatzResearch.WordTrace tailWord_2779426 prefixEnd_2779426 105717146785447979014271 := by
  unfold tailWord_2779426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25343498607155441253513533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67582662952414510009369421 25343498607155441253513533)
  ·
    refine ⟨9503811977683290470067575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25343498607155441253513533 9503811977683290470067575)
    ·
      refine ⟨14255717966524935705101363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503811977683290470067575 14255717966524935705101363)
      ·
        refine ⟨21383576949787403557652045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14255717966524935705101363 21383576949787403557652045)
        ·
          refine ⟨8018841356170276334119517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21383576949787403557652045 8018841356170276334119517)
          ·
            refine ⟨3007065508563853625294819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8018841356170276334119517 3007065508563853625294819)
            ·
              refine ⟨4510598262845780437942229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007065508563853625294819 4510598262845780437942229)
              ·
                refine ⟨105717146785447979014271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4510598262845780437942229 105717146785447979014271)
                ·
                  rfl

theorem cell22_2779426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_2779426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779426 prefixEnd_2779426 := by exact prefixLift 2779426
  have htrace : WordTrace (prefixWord ++ tailWord_2779426) baseStart_2779426 baseEnd_2779426 := by
    simpa [prefixWord, tailWord_2779426, baseEnd_2779426] using wordTrace_append hprefix tailTrace_2779426
  have hstable : (prefixWord ++ tailWord_2779426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779426).length < 2 ^ (prefixWord ++ tailWord_2779426).sum := by decide
  have hdescent : baseEnd_2779426 < baseStart_2779426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779488 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 5]
def baseStart_2779488 : Nat := 118140960795 + 2779488 * 2 ^ 59
def prefixEnd_2779488 : Nat := 4983230072969 + 3 ^ 40 * 2779488 * 2
def baseEnd_2779488 : Nat := 317158514978694772026083

theorem tailTrace_2779488 : CollatzResearch.WordTrace tailWord_2779488 prefixEnd_2779488 317158514978694772026083 := by
  unfold tailWord_2779488
  simp only [CollatzResearch.WordTrace]
  refine ⟨50688127877198574801405559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67584170502931433068540745 50688127877198574801405559)
  ·
    refine ⟨76032191815797862202108339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50688127877198574801405559 76032191815797862202108339)
    ·
      refine ⟨114048287723696793303162509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76032191815797862202108339 114048287723696793303162509)
      ·
        refine ⟨42768107896386297488685941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114048287723696793303162509 42768107896386297488685941)
        ·
          refine ⟨4009510115286215389564307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42768107896386297488685941 4009510115286215389564307)
          ·
            refine ⟨6014265172929323084346461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009510115286215389564307 6014265172929323084346461)
            ·
              refine ⟨2255349439848496156629923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6014265172929323084346461 2255349439848496156629923)
              ·
                refine ⟨3383024159772744234944885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255349439848496156629923 3383024159772744234944885)
                ·
                  refine ⟨317158514978694772026083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3383024159772744234944885 317158514978694772026083)
                  ·
                    rfl

theorem cell22_2779488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_2779488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779488 prefixEnd_2779488 := by exact prefixLift 2779488
  have htrace : WordTrace (prefixWord ++ tailWord_2779488) baseStart_2779488 baseEnd_2779488 := by
    simpa [prefixWord, tailWord_2779488, baseEnd_2779488] using wordTrace_append hprefix tailTrace_2779488
  have hstable : (prefixWord ++ tailWord_2779488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779488).length < 2 ^ (prefixWord ++ tailWord_2779488).sum := by decide
  have hdescent : baseEnd_2779488 < baseStart_2779488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779516 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 4]
def baseStart_2779516 : Nat := 118140960795 + 2779516 * 2 ^ 59
def prefixEnd_2779516 : Nat := 4983230072969 + 3 ^ 40 * 2779516 * 2
def baseEnd_2779516 : Nat := 317161709969433858792721

theorem tailTrace_2779516 : CollatzResearch.WordTrace tailWord_2779516 prefixEnd_2779516 317161709969433858792721 := by
  unfold tailWord_2779516
  simp only [CollatzResearch.WordTrace]
  refine ⟨50688638499147855192415201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67584851332197140256553601 50688638499147855192415201)
  ·
    refine ⟨38016478874360891394311401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50688638499147855192415201 38016478874360891394311401)
    ·
      refine ⟨28512359155770668545733551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38016478874360891394311401 28512359155770668545733551)
      ·
        refine ⟨42768538733656002818600327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28512359155770668545733551 42768538733656002818600327)
        ·
          refine ⟨64152808100484004227900491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42768538733656002818600327 64152808100484004227900491)
          ·
            refine ⟨96229212150726006341850737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64152808100484004227900491 96229212150726006341850737)
            ·
              refine ⟨72171909113044504756388053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96229212150726006341850737 72171909113044504756388053)
              ·
                refine ⟨1691529119836980580227845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72171909113044504756388053 1691529119836980580227845)
                ·
                  refine ⟨317161709969433858792721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691529119836980580227845 317161709969433858792721)
                  ·
                    rfl

theorem cell22_2779516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_2779516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779516 prefixEnd_2779516 := by exact prefixLift 2779516
  have htrace : WordTrace (prefixWord ++ tailWord_2779516) baseStart_2779516 baseEnd_2779516 := by
    simpa [prefixWord, tailWord_2779516, baseEnd_2779516] using wordTrace_append hprefix tailTrace_2779516
  have hstable : (prefixWord ++ tailWord_2779516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779516).length < 2 ^ (prefixWord ++ tailWord_2779516).sum := by decide
  have hdescent : baseEnd_2779516 < baseStart_2779516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779531 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 4, 3]
def baseStart_2779531 : Nat := 118140960795 + 2779531 * 2 ^ 59
def prefixEnd_2779531 : Nat := 4983230072969 + 3 ^ 40 * 2779531 * 2
def baseEnd_2779531 : Nat := 951490264714846537253117

theorem tailTrace_2779531 : CollatzResearch.WordTrace tailWord_2779531 prefixEnd_2779531 951490264714846537253117 := by
  unfold tailWord_2779531
  simp only [CollatzResearch.WordTrace]
  refine ⟨101377824093241367946626447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67585216062160911964417631 101377824093241367946626447)
  ·
    refine ⟨152066736139862051919939671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101377824093241367946626447 152066736139862051919939671)
    ·
      refine ⟨228100104209793077879909507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152066736139862051919939671 228100104209793077879909507)
      ·
        refine ⟨342150156314689616819864261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228100104209793077879909507 342150156314689616819864261)
        ·
          refine ⟨64153154309004303153724549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342150156314689616819864261 64153154309004303153724549)
          ·
            refine ⟨12028716432938306841323353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64153154309004303153724549 12028716432938306841323353)
            ·
              refine ⟨9021537324703730130992515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12028716432938306841323353 9021537324703730130992515)
              ·
                refine ⟨13532305987055595196488773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9021537324703730130992515 13532305987055595196488773)
                ·
                  refine ⟨2537307372572924099341645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13532305987055595196488773 2537307372572924099341645)
                  ·
                    refine ⟨951490264714846537253117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2537307372572924099341645 951490264714846537253117)
                    ·
                      rfl

theorem cell22_2779531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 3].length) (baseStart_2779531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779531 prefixEnd_2779531 := by exact prefixLift 2779531
  have htrace : WordTrace (prefixWord ++ tailWord_2779531) baseStart_2779531 baseEnd_2779531 := by
    simpa [prefixWord, tailWord_2779531, baseEnd_2779531] using wordTrace_append hprefix tailTrace_2779531
  have hstable : (prefixWord ++ tailWord_2779531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779531).length < 2 ^ (prefixWord ++ tailWord_2779531).sum := by decide
  have hdescent : baseEnd_2779531 < baseStart_2779531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779651 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 6]
def baseStart_2779651 : Nat := 118140960795 + 2779651 * 2 ^ 59
def prefixEnd_2779651 : Nat := 4983230072969 + 3 ^ 40 * 2779651 * 2
def baseEnd_2779651 : Nat := 317177114389068741417583

theorem tailTrace_2779651 : CollatzResearch.WordTrace tailWord_2779651 prefixEnd_2779651 317177114389068741417583 := by
  unfold tailWord_2779651
  simp only [CollatzResearch.WordTrace]
  refine ⟨101382200852806628440994807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67588133901871085627329871 101382200852806628440994807)
  ·
    refine ⟨152073301279209942661492211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101382200852806628440994807 152073301279209942661492211)
    ·
      refine ⟨228109951918814913992238317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152073301279209942661492211 228109951918814913992238317)
      ·
        refine ⟨85541231969555592747089369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228109951918814913992238317 85541231969555592747089369)
        ·
          refine ⟨64155923977166694560317027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85541231969555592747089369 64155923977166694560317027)
          ·
            refine ⟨96233885965750041840475541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64155923977166694560317027 96233885965750041840475541)
            ·
              refine ⟨4510963404644533211272291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96233885965750041840475541 4510963404644533211272291)
              ·
                refine ⟨6766445106966799816908437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510963404644533211272291 6766445106966799816908437)
                ·
                  refine ⟨317177114389068741417583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6766445106966799816908437 317177114389068741417583)
                  ·
                    rfl

theorem cell22_2779651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 6].length) (baseStart_2779651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779651 prefixEnd_2779651 := by exact prefixLift 2779651
  have htrace : WordTrace (prefixWord ++ tailWord_2779651) baseStart_2779651 baseEnd_2779651 := by
    simpa [prefixWord, tailWord_2779651, baseEnd_2779651] using wordTrace_append hprefix tailTrace_2779651
  have hstable : (prefixWord ++ tailWord_2779651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779651).length < 2 ^ (prefixWord ++ tailWord_2779651).sum := by decide
  have hdescent : baseEnd_2779651 < baseStart_2779651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779681 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2779681 : Nat := 118140960795 + 2779681 * 2 ^ 59
def prefixEnd_2779681 : Nat := 4983230072969 + 3 ^ 40 * 2779681 * 2
def baseEnd_2779681 : Nat := 951541612780296146002657

theorem tailTrace_2779681 : CollatzResearch.WordTrace tailWord_2779681 prefixEnd_2779681 951541612780296146002657 := by
  unfold tailWord_2779681
  simp only [CollatzResearch.WordTrace]
  refine ⟨101383295042697943564586897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67588863361798629043057931 101383295042697943564586897)
  ·
    refine ⟨76037471282023457673440173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101383295042697943564586897 76037471282023457673440173)
    ·
      refine ⟨28514051730758796627540065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76037471282023457673440173 28514051730758796627540065)
      ·
        refine ⟨21385538798069097470655049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28514051730758796627540065 21385538798069097470655049)
        ·
          refine ⟨16039154098551823102991287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21385538798069097470655049 16039154098551823102991287)
          ·
            refine ⟨24058731147827734654486931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16039154098551823102991287 24058731147827734654486931)
            ·
              refine ⟨36088096721741601981730397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24058731147827734654486931 36088096721741601981730397)
              ·
                refine ⟨13533036270653100743148899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36088096721741601981730397 13533036270653100743148899)
                ·
                  refine ⟨20299554405979651114723349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13533036270653100743148899 20299554405979651114723349)
                  ·
                    refine ⟨951541612780296146002657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20299554405979651114723349 951541612780296146002657)
                    ·
                      rfl

theorem cell22_2779681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2779681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779681 prefixEnd_2779681 := by exact prefixLift 2779681
  have htrace : WordTrace (prefixWord ++ tailWord_2779681) baseStart_2779681 baseEnd_2779681 := by
    simpa [prefixWord, tailWord_2779681, baseEnd_2779681] using wordTrace_append hprefix tailTrace_2779681
  have hstable : (prefixWord ++ tailWord_2779681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779681).length < 2 ^ (prefixWord ++ tailWord_2779681).sum := by decide
  have hdescent : baseEnd_2779681 < baseStart_2779681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779683 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 4, 3]
def baseStart_2779683 : Nat := 118140960795 + 2779683 * 2 ^ 59
def prefixEnd_2779683 : Nat := 4983230072969 + 3 ^ 40 * 2779683 * 2
def baseEnd_2779683 : Nat := 951542297421168807452651

theorem tailTrace_2779683 : CollatzResearch.WordTrace tailWord_2779683 prefixEnd_2779683 951542297421168807452651 := by
  unfold tailWord_2779683
  simp only [CollatzResearch.WordTrace]
  refine ⟨101383367988690697906159703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67588911992460465270773135 101383367988690697906159703)
  ·
    refine ⟨152075051983036046859239555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101383367988690697906159703 152075051983036046859239555)
    ·
      refine ⟨228112577974554070288859333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152075051983036046859239555 228112577974554070288859333)
      ·
        refine ⟨42771108370228888179161125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228112577974554070288859333 42771108370228888179161125)
        ·
          refine ⟨8019582819417916533592711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42771108370228888179161125 8019582819417916533592711)
          ·
            refine ⟨12029374229126874800389067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019582819417916533592711 12029374229126874800389067)
            ·
              refine ⟨18044061343690312200583601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12029374229126874800389067 18044061343690312200583601)
              ·
                refine ⟨13533046007767734150437701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18044061343690312200583601 13533046007767734150437701)
                ·
                  refine ⟨2537446126456450153207069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13533046007767734150437701 2537446126456450153207069)
                  ·
                    refine ⟨951542297421168807452651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2537446126456450153207069 951542297421168807452651)
                    ·
                      rfl

theorem cell22_2779683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 3].length) (baseStart_2779683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779683 prefixEnd_2779683 := by exact prefixLift 2779683
  have htrace : WordTrace (prefixWord ++ tailWord_2779683) baseStart_2779683 baseEnd_2779683 := by
    simpa [prefixWord, tailWord_2779683, baseEnd_2779683] using wordTrace_append hprefix tailTrace_2779683
  have hstable : (prefixWord ++ tailWord_2779683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779683).length < 2 ^ (prefixWord ++ tailWord_2779683).sum := by decide
  have hdescent : baseEnd_2779683 < baseStart_2779683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779713 : List Nat := [1, 2, 5, 1, 1, 3, 2, 7]
def baseStart_2779713 : Nat := 118140960795 + 2779713 * 2 ^ 59
def prefixEnd_2779713 : Nat := 4983230072969 + 3 ^ 40 * 2779713 * 2
def baseEnd_2779713 : Nat := 105728063003806525466951

theorem tailTrace_2779713 : CollatzResearch.WordTrace tailWord_2779713 prefixEnd_2779713 105728063003806525466951 := by
  unfold tailWord_2779713
  simp only [CollatzResearch.WordTrace]
  refine ⟨101384462178582013029751793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67589641452388008686501195 101384462178582013029751793)
  ·
    refine ⟨76038346633936509772313845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101384462178582013029751793 76038346633936509772313845)
    ·
      refine ⟨7128594996931547791154423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76038346633936509772313845 7128594996931547791154423)
      ·
        refine ⟨10692892495397321686731635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7128594996931547791154423 10692892495397321686731635)
        ·
          refine ⟨16039338743095982530097453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10692892495397321686731635 16039338743095982530097453)
          ·
            refine ⟨6014752028660993448786545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16039338743095982530097453 6014752028660993448786545)
            ·
              refine ⟨4511064021495745086589909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014752028660993448786545 4511064021495745086589909)
              ·
                refine ⟨105728063003806525466951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4511064021495745086589909 105728063003806525466951)
                ·
                  rfl

theorem cell22_2779713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 7].length) (baseStart_2779713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779713 prefixEnd_2779713 := by exact prefixLift 2779713
  have htrace : WordTrace (prefixWord ++ tailWord_2779713) baseStart_2779713 baseEnd_2779713 := by
    simpa [prefixWord, tailWord_2779713, baseEnd_2779713] using wordTrace_append hprefix tailTrace_2779713
  have hstable : (prefixWord ++ tailWord_2779713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779713).length < 2 ^ (prefixWord ++ tailWord_2779713).sum := by decide
  have hdescent : baseEnd_2779713 < baseStart_2779713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779717 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_2779717 : Nat := 118140960795 + 2779717 * 2 ^ 59
def prefixEnd_2779717 : Nat := 4983230072969 + 3 ^ 40 * 2779717 * 2
def baseEnd_2779717 : Nat := 951553936316004052102547

theorem tailTrace_2779717 : CollatzResearch.WordTrace tailWord_2779717 prefixEnd_2779717 951553936316004052102547 := by
  unfold tailWord_2779717
  simp only [CollatzResearch.WordTrace]
  refine ⟨101384608070567521712897405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67589738713711681141931603 101384608070567521712897405)
  ·
    refine ⟨38019228026462820642336527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101384608070567521712897405 38019228026462820642336527)
    ·
      refine ⟨57028842039694230963504791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38019228026462820642336527 57028842039694230963504791)
      ·
        refine ⟨85543263059541346445257187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57028842039694230963504791 85543263059541346445257187)
        ·
          refine ⟨128314894589312019667885781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85543263059541346445257187 128314894589312019667885781)
          ·
            refine ⟨3007380341937000460966073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128314894589312019667885781 3007380341937000460966073)
            ·
              refine ⟨2255535256452750345724555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007380341937000460966073 2255535256452750345724555)
              ·
                refine ⟨3383302884679125518586833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255535256452750345724555 3383302884679125518586833)
                ·
                  refine ⟨2537477163509344138940125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383302884679125518586833 2537477163509344138940125)
                  ·
                    refine ⟨951553936316004052102547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2537477163509344138940125 951553936316004052102547)
                    ·
                      rfl

theorem cell22_2779717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_2779717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779717 prefixEnd_2779717 := by exact prefixLift 2779717
  have htrace : WordTrace (prefixWord ++ tailWord_2779717) baseStart_2779717 baseEnd_2779717 := by
    simpa [prefixWord, tailWord_2779717, baseEnd_2779717] using wordTrace_append hprefix tailTrace_2779717
  have hstable : (prefixWord ++ tailWord_2779717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779717).length < 2 ^ (prefixWord ++ tailWord_2779717).sum := by decide
  have hdescent : baseEnd_2779717 < baseStart_2779717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779848 : List Nat := [2, 1, 3, 1, 2, 4, 1, 8]
def baseStart_2779848 : Nat := 118140960795 + 2779848 * 2 ^ 59
def prefixEnd_2779848 : Nat := 4983230072969 + 3 ^ 40 * 2779848 * 2
def baseEnd_2779848 : Nat := 105733197810351486341905

theorem tailTrace_2779848 : CollatzResearch.WordTrace tailWord_2779848 prefixEnd_2779848 105733197810351486341905 := by
  unfold tailWord_2779848
  simp only [CollatzResearch.WordTrace]
  refine ⟨50694693016546465542958099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67592924022061954057277465 50694693016546465542958099)
  ·
    refine ⟨76042039524819698314437149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50694693016546465542958099 76042039524819698314437149)
    ·
      refine ⟨28515764821807386867913931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76042039524819698314437149 28515764821807386867913931)
      ·
        refine ⟨42773647232711080301870897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28515764821807386867913931 42773647232711080301870897)
        ·
          refine ⟨32080235424533310226403173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42773647232711080301870897 32080235424533310226403173)
          ·
            refine ⟨6015044142099995667450595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32080235424533310226403173 6015044142099995667450595)
            ·
              refine ⟨9022566213149993501175893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015044142099995667450595 9022566213149993501175893)
              ·
                refine ⟨105733197810351486341905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9022566213149993501175893 105733197810351486341905)
                ·
                  rfl

theorem cell22_2779848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_2779848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779848 prefixEnd_2779848 := by exact prefixLift 2779848
  have htrace : WordTrace (prefixWord ++ tailWord_2779848) baseStart_2779848 baseEnd_2779848 := by
    simpa [prefixWord, tailWord_2779848, baseEnd_2779848] using wordTrace_append hprefix tailTrace_2779848
  have hstable : (prefixWord ++ tailWord_2779848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779848).length < 2 ^ (prefixWord ++ tailWord_2779848).sum := by decide
  have hdescent : baseEnd_2779848 < baseStart_2779848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779927 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 5]
def baseStart_2779927 : Nat := 118140960795 + 2779927 * 2 ^ 59
def prefixEnd_2779927 : Nat := 4983230072969 + 3 ^ 40 * 2779927 * 2
def baseEnd_2779927 : Nat := 317208607869211168117301

theorem tailTrace_2779927 : CollatzResearch.WordTrace tailWord_2779927 prefixEnd_2779927 317208607869211168117301 := by
  unfold tailWord_2779927
  simp only [CollatzResearch.WordTrace]
  refine ⟨101392267399806727578042035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67594844933204485052028023 101392267399806727578042035)
  ·
    refine ⟨152088401099710091367063053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101392267399806727578042035 152088401099710091367063053)
    ·
      refine ⟨57033150412391284262648645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152088401099710091367063053 57033150412391284262648645)
      ·
        refine ⟨10693715702323365799246621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57033150412391284262648645 10693715702323365799246621)
        ·
          refine ⟨4010143388371262174717483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10693715702323365799246621 4010143388371262174717483)
          ·
            refine ⟨6015215082556893262076225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010143388371262174717483 6015215082556893262076225)
            ·
              refine ⟨4511411311917669946557169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6015215082556893262076225 4511411311917669946557169)
              ·
                refine ⟨3383558483938252459917877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511411311917669946557169 3383558483938252459917877)
                ·
                  refine ⟨317208607869211168117301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3383558483938252459917877 317208607869211168117301)
                  ·
                    rfl

theorem cell22_2779927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 5].length) (baseStart_2779927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779927 prefixEnd_2779927 := by exact prefixLift 2779927
  have htrace : WordTrace (prefixWord ++ tailWord_2779927) baseStart_2779927 baseEnd_2779927 := by
    simpa [prefixWord, tailWord_2779927, baseEnd_2779927] using wordTrace_append hprefix tailTrace_2779927
  have hstable : (prefixWord ++ tailWord_2779927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779927).length < 2 ^ (prefixWord ++ tailWord_2779927).sum := by decide
  have hdescent : baseEnd_2779927 < baseStart_2779927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779955 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 6]
def baseStart_2779955 : Nat := 118140960795 + 2779955 * 2 ^ 59
def prefixEnd_2779955 : Nat := 4983230072969 + 3 ^ 40 * 2779955 * 2
def baseEnd_2779955 : Nat := 317211802859950254883939

theorem tailTrace_2779955 : CollatzResearch.WordTrace tailWord_2779955 prefixEnd_2779955 317211802859950254883939 := by
  unfold tailWord_2779955
  simp only [CollatzResearch.WordTrace]
  refine ⟨101393288643705288360061319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67595525762470192240040879 101393288643705288360061319)
  ·
    refine ⟨152089932965557932540091979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101393288643705288360061319 152089932965557932540091979)
    ·
      refine ⟨228134899448336898810137969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152089932965557932540091979 228134899448336898810137969)
      ·
        refine ⟨171101174586252674107603477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228134899448336898810137969 171101174586252674107603477)
        ·
          refine ⟨8020367558730594098793913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171101174586252674107603477 8020367558730594098793913)
          ·
            refine ⟨6015275669047945574095435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8020367558730594098793913 6015275669047945574095435)
            ·
              refine ⟨9022913503571918361143153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015275669047945574095435 9022913503571918361143153)
              ·
                refine ⟨6767185127678938770857365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9022913503571918361143153 6767185127678938770857365)
                ·
                  refine ⟨317211802859950254883939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6767185127678938770857365 317211802859950254883939)
                  ·
                    rfl

theorem cell22_2779955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_2779955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2779955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2779955 prefixEnd_2779955 := by exact prefixLift 2779955
  have htrace : WordTrace (prefixWord ++ tailWord_2779955) baseStart_2779955 baseEnd_2779955 := by
    simpa [prefixWord, tailWord_2779955, baseEnd_2779955] using wordTrace_append hprefix tailTrace_2779955
  have hstable : (prefixWord ++ tailWord_2779955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779955).length < 2 ^ (prefixWord ++ tailWord_2779955).sum := by decide
  have hdescent : baseEnd_2779955 < baseStart_2779955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780017 : List Nat := [1, 2, 2, 2, 1, 6, 2, 6]
def baseStart_2780017 : Nat := 118140960795 + 2780017 * 2 ^ 59
def prefixEnd_2780017 : Nat := 4983230072969 + 3 ^ 40 * 2780017 * 2
def baseEnd_2780017 : Nat := 105739625827433696622403

theorem tailTrace_2780017 : CollatzResearch.WordTrace tailWord_2780017 prefixEnd_2780017 105739625827433696622403 := by
  unfold tailWord_2780017
  simp only [CollatzResearch.WordTrace]
  refine ⟨101395549969480672948818305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67597033312987115299212203 101395549969480672948818305)
  ·
    refine ⟨76046662477110504711613729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101395549969480672948818305 76046662477110504711613729)
    ·
      refine ⟨57034996857832878533710297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76046662477110504711613729 57034996857832878533710297)
      ·
        refine ⟨42776247643374658900282723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57034996857832878533710297 42776247643374658900282723)
        ·
          refine ⟨64164371465061988350424085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42776247643374658900282723 64164371465061988350424085)
          ·
            refine ⟨3007704912424780703926129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64164371465061988350424085 3007704912424780703926129)
            ·
              refine ⟨2255778684318585527944597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007704912424780703926129 2255778684318585527944597)
              ·
                refine ⟨105739625827433696622403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2255778684318585527944597 105739625827433696622403)
                ·
                  rfl

theorem cell22_2780017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 6].length) (baseStart_2780017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780017 prefixEnd_2780017 := by exact prefixLift 2780017
  have htrace : WordTrace (prefixWord ++ tailWord_2780017) baseStart_2780017 baseEnd_2780017 := by
    simpa [prefixWord, tailWord_2780017, baseEnd_2780017] using wordTrace_append hprefix tailTrace_2780017
  have hstable : (prefixWord ++ tailWord_2780017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780017).length < 2 ^ (prefixWord ++ tailWord_2780017).sum := by decide
  have hdescent : baseEnd_2780017 < baseStart_2780017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780075 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 3, 4]
def baseStart_2780075 : Nat := 118140960795 + 2780075 * 2 ^ 59
def prefixEnd_2780075 : Nat := 4983230072969 + 3 ^ 40 * 2780075 * 2
def baseEnd_2780075 : Nat := 951676487032210451651449

theorem tailTrace_2780075 : CollatzResearch.WordTrace tailWord_2780075 prefixEnd_2780075 951676487032210451651449 := by
  unfold tailWord_2780075
  simp only [CollatzResearch.WordTrace]
  refine ⟨101397665403270548854429679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67598443602180365902953119 101397665403270548854429679)
  ·
    refine ⟨152096498104905823281644519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101397665403270548854429679 152096498104905823281644519)
    ·
      refine ⟨228144747157358734922466779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152096498104905823281644519 228144747157358734922466779)
      ·
        refine ⟨342217120736038102383700169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228144747157358734922466779 342217120736038102383700169)
        ·
          refine ⟨256662840552028576787775127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342217120736038102383700169 256662840552028576787775127)
          ·
            refine ⟨384994260828042865181662691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256662840552028576787775127 384994260828042865181662691)
            ·
              refine ⟨577491391242064297772494037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384994260828042865181662691 577491391242064297772494037)
              ·
                refine ⟨13534954482235881979042829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 577491391242064297772494037 13534954482235881979042829)
                ·
                  refine ⟨5075607930838455742141061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13534954482235881979042829 5075607930838455742141061)
                  ·
                    refine ⟨951676487032210451651449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075607930838455742141061 951676487032210451651449)
                    ·
                      rfl

theorem cell22_2780075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_2780075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780075 prefixEnd_2780075 := by exact prefixLift 2780075
  have htrace : WordTrace (prefixWord ++ tailWord_2780075) baseStart_2780075 baseEnd_2780075 := by
    simpa [prefixWord, tailWord_2780075, baseEnd_2780075] using wordTrace_append hprefix tailTrace_2780075
  have hstable : (prefixWord ++ tailWord_2780075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780075).length < 2 ^ (prefixWord ++ tailWord_2780075).sum := by decide
  have hdescent : baseEnd_2780075 < baseStart_2780075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780122 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_2780122 : Nat := 118140960795 + 2780122 * 2 ^ 59
def prefixEnd_2780122 : Nat := 4983230072969 + 3 ^ 40 * 2780122 * 2
def baseEnd_2780122 : Nat := 951692576092717995726305

theorem tailTrace_2780122 : CollatzResearch.WordTrace tailWord_2780122 prefixEnd_2780122 951692576092717995726305 := by
  unfold tailWord_2780122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25349844908525068970347655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67599586422733517254260413 25349844908525068970347655)
  ·
    refine ⟨38024767362787603455521483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25349844908525068970347655 38024767362787603455521483)
    ·
      refine ⟨57037151044181405183282225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38024767362787603455521483 57037151044181405183282225)
      ·
        refine ⟨42777863283136053887461669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57037151044181405183282225 42777863283136053887461669)
        ·
          refine ⟨8020849365588010103899063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42777863283136053887461669 8020849365588010103899063)
          ·
            refine ⟨12031274048382015155848595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020849365588010103899063 12031274048382015155848595)
            ·
              refine ⟨18046911072573022733772893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12031274048382015155848595 18046911072573022733772893)
              ·
                refine ⟨6767591652214883525164835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18046911072573022733772893 6767591652214883525164835)
                ·
                  refine ⟨10151387478322325287747253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6767591652214883525164835 10151387478322325287747253)
                  ·
                    refine ⟨951692576092717995726305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10151387478322325287747253 951692576092717995726305)
                    ·
                      rfl

theorem cell22_2780122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_2780122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780122 prefixEnd_2780122 := by exact prefixLift 2780122
  have htrace : WordTrace (prefixWord ++ tailWord_2780122) baseStart_2780122 baseEnd_2780122 := by
    simpa [prefixWord, tailWord_2780122, baseEnd_2780122] using wordTrace_append hprefix tailTrace_2780122
  have hstable : (prefixWord ++ tailWord_2780122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780122).length < 2 ^ (prefixWord ++ tailWord_2780122).sum := by decide
  have hdescent : baseEnd_2780122 < baseStart_2780122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780156 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_2780156 : Nat := 118140960795 + 2780156 * 2 ^ 59
def prefixEnd_2780156 : Nat := 4983230072969 + 3 ^ 40 * 2780156 * 2
def baseEnd_2780156 : Nat := 951704214987553240376201

theorem tailTrace_2780156 : CollatzResearch.WordTrace tailWord_2780156 prefixEnd_2780156 951704214987553240376201 := by
  unfold tailWord_2780156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50700309857988549844064161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67600413143984733125418881 50700309857988549844064161)
  ·
    refine ⟨38025232393491412383048121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50700309857988549844064161 38025232393491412383048121)
    ·
      refine ⟨28518924295118559287286091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38025232393491412383048121 28518924295118559287286091)
      ·
        refine ⟨42778386442677838930929137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28518924295118559287286091 42778386442677838930929137)
        ·
          refine ⟨32083789832008379198196853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42778386442677838930929137 32083789832008379198196853)
          ·
            refine ⟨3007855296750785549830955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32083789832008379198196853 3007855296750785549830955)
            ·
              refine ⟨4511782945126178324746433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007855296750785549830955 4511782945126178324746433)
              ·
                refine ⟨3383837208844633743559825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511782945126178324746433 3383837208844633743559825)
                ·
                  refine ⟨2537877906633475307669869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383837208844633743559825 2537877906633475307669869)
                  ·
                    refine ⟨951704214987553240376201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2537877906633475307669869 951704214987553240376201)
                    ·
                      rfl

theorem cell22_2780156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_2780156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780156 prefixEnd_2780156 := by exact prefixLift 2780156
  have htrace : WordTrace (prefixWord ++ tailWord_2780156) baseStart_2780156 baseEnd_2780156 := by
    simpa [prefixWord, tailWord_2780156, baseEnd_2780156] using wordTrace_append hprefix tailTrace_2780156
  have hstable : (prefixWord ++ tailWord_2780156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780156).length < 2 ^ (prefixWord ++ tailWord_2780156).sum := by decide
  have hdescent : baseEnd_2780156 < baseStart_2780156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780184 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 3, 3]
def baseStart_2780184 : Nat := 118140960795 + 2780184 * 2 ^ 59
def prefixEnd_2780184 : Nat := 4983230072969 + 3 ^ 40 * 2780184 * 2
def baseEnd_2780184 : Nat := 951713799959770500676115

theorem tailTrace_2780184 : CollatzResearch.WordTrace tailWord_2780184 prefixEnd_2780184 951713799959770500676115 := by
  unfold tailWord_2780184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50700820479937830235073803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67601093973250440313431737 50700820479937830235073803)
  ·
    refine ⟨76051230719906745352610705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50700820479937830235073803 76051230719906745352610705)
    ·
      refine ⟨57038423039930059014458029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76051230719906745352610705 57038423039930059014458029)
      ·
        refine ⟨21389408639973772130421761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57038423039930059014458029 21389408639973772130421761)
        ·
          refine ⟨16042056479980329097816321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21389408639973772130421761 16042056479980329097816321)
          ·
            refine ⟨12031542359985246823362241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16042056479980329097816321 12031542359985246823362241)
            ·
              refine ⟨9023656769988935117521681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12031542359985246823362241 9023656769988935117521681)
              ·
                refine ⟨6767742577491701338141261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9023656769988935117521681 6767742577491701338141261)
                ·
                  refine ⟨2537903466559388001802973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6767742577491701338141261 2537903466559388001802973)
                  ·
                    refine ⟨951713799959770500676115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2537903466559388001802973 951713799959770500676115)
                    ·
                      rfl

theorem cell22_2780184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_2780184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780184 prefixEnd_2780184 := by exact prefixLift 2780184
  have htrace : WordTrace (prefixWord ++ tailWord_2780184) baseStart_2780184 baseEnd_2780184 := by
    simpa [prefixWord, tailWord_2780184, baseEnd_2780184] using wordTrace_append hprefix tailTrace_2780184
  have hstable : (prefixWord ++ tailWord_2780184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780184).length < 2 ^ (prefixWord ++ tailWord_2780184).sum := by decide
  have hdescent : baseEnd_2780184 < baseStart_2780184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780214 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2780214 : Nat := 118140960795 + 2780214 * 2 ^ 59
def prefixEnd_2780214 : Nat := 4983230072969 + 3 ^ 40 * 2780214 * 2
def baseEnd_2780214 : Nat := 317241356524286807475341

theorem tailTrace_2780214 : CollatzResearch.WordTrace tailWord_2780214 prefixEnd_2780214 317241356524286807475341 := by
  unfold tailWord_2780214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337670946860435974608731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67601823433177983729159797 6337670946860435974608731)
  ·
    refine ⟨9506506420290653961913097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6337670946860435974608731 9506506420290653961913097)
    ·
      refine ⟨7129879815217990471434823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9506506420290653961913097 7129879815217990471434823)
      ·
        refine ⟨10694819722826985707152235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7129879815217990471434823 10694819722826985707152235)
        ·
          refine ⟨16042229584240478560728353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10694819722826985707152235 16042229584240478560728353)
          ·
            refine ⟨12031672188180358920546265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16042229584240478560728353 12031672188180358920546265)
            ·
              refine ⟨9023754141135269190409699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12031672188180358920546265 9023754141135269190409699)
              ·
                refine ⟨13535631211702903785614549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9023754141135269190409699 13535631211702903785614549)
                ·
                  refine ⟨317241356524286807475341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13535631211702903785614549 317241356524286807475341)
                  ·
                    rfl

theorem cell22_2780214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2780214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780214 prefixEnd_2780214 := by exact prefixLift 2780214
  have htrace : WordTrace (prefixWord ++ tailWord_2780214) baseStart_2780214 baseEnd_2780214 := by
    simpa [prefixWord, tailWord_2780214, baseEnd_2780214] using wordTrace_append hprefix tailTrace_2780214
  have hstable : (prefixWord ++ tailWord_2780214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780214).length < 2 ^ (prefixWord ++ tailWord_2780214).sum := by decide
  have hdescent : baseEnd_2780214 < baseStart_2780214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780227 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 3, 4]
def baseStart_2780227 : Nat := 118140960795 + 2780227 * 2 ^ 59
def prefixEnd_2780227 : Nat := 4983230072969 + 3 ^ 40 * 2780227 * 2
def baseEnd_2780227 : Nat := 951728519738532721850983

theorem tailTrace_2780227 : CollatzResearch.WordTrace tailWord_2780227 prefixEnd_2780227 951728519738532721850983 := by
  unfold tailWord_2780227
  simp only [CollatzResearch.WordTrace]
  refine ⟨101403209298719878813962935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67602139532479919209308623 101403209298719878813962935)
  ·
    refine ⟨152104813948079818220944403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101403209298719878813962935 152104813948079818220944403)
    ·
      refine ⟨228157220922119727331416605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152104813948079818220944403 228157220922119727331416605)
      ·
        refine ⟨85558957845794897749281227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228157220922119727331416605 85558957845794897749281227)
        ·
          refine ⟨128338436768692346623921841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85558957845794897749281227 128338436768692346623921841)
          ·
            refine ⟨96253827576519259967941381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128338436768692346623921841 96253827576519259967941381)
            ·
              refine ⟨18047592670597361243989009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96253827576519259967941381 18047592670597361243989009)
              ·
                refine ⟨13535694502948020932991757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18047592670597361243989009 13535694502948020932991757)
                ·
                  refine ⟨5075885438605507849871909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13535694502948020932991757 5075885438605507849871909)
                  ·
                    refine ⟨951728519738532721850983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075885438605507849871909 951728519738532721850983)
                    ·
                      rfl

theorem cell22_2780227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_2780227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780227 prefixEnd_2780227 := by exact prefixLift 2780227
  have htrace : WordTrace (prefixWord ++ tailWord_2780227) baseStart_2780227 baseEnd_2780227 := by
    simpa [prefixWord, tailWord_2780227, baseEnd_2780227] using wordTrace_append hprefix tailTrace_2780227
  have hstable : (prefixWord ++ tailWord_2780227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780227).length < 2 ^ (prefixWord ++ tailWord_2780227).sum := by decide
  have hdescent : baseEnd_2780227 < baseStart_2780227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780231 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 5]
def baseStart_2780231 : Nat := 118140960795 + 2780231 * 2 ^ 59
def prefixEnd_2780231 : Nat := 4983230072969 + 3 ^ 40 * 2780231 * 2
def baseEnd_2780231 : Nat := 317243296340092681583657

theorem tailTrace_2780231 : CollatzResearch.WordTrace tailWord_2780231 prefixEnd_2780231 317243296340092681583657 := by
  unfold tailWord_2780231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101403355190705387497108547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67602236793803591664739031 101403355190705387497108547)
  ·
    refine ⟨152105032786058081245662821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101403355190705387497108547 152105032786058081245662821)
    ·
      refine ⟨28519693647385890233561779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152105032786058081245662821 28519693647385890233561779)
      ·
        refine ⟨42779540471078835350342669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28519693647385890233561779 42779540471078835350342669)
        ·
          refine ⟨16042327676654563256378501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42779540471078835350342669 16042327676654563256378501)
          ·
            refine ⟨3007936439372730610570969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16042327676654563256378501 3007936439372730610570969)
            ·
              refine ⟨2255952329529547957928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007936439372730610570969 2255952329529547957928227)
              ·
                refine ⟨3383928494294321936892341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255952329529547957928227 3383928494294321936892341)
                ·
                  refine ⟨317243296340092681583657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3383928494294321936892341 317243296340092681583657)
                  ·
                    rfl

theorem cell22_2780231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 5].length) (baseStart_2780231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780231 prefixEnd_2780231 := by exact prefixLift 2780231
  have htrace : WordTrace (prefixWord ++ tailWord_2780231) baseStart_2780231 baseEnd_2780231 := by
    simpa [prefixWord, tailWord_2780231, baseEnd_2780231] using wordTrace_append hprefix tailTrace_2780231
  have hstable : (prefixWord ++ tailWord_2780231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780231).length < 2 ^ (prefixWord ++ tailWord_2780231).sum := by decide
  have hdescent : baseEnd_2780231 < baseStart_2780231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780257 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2780257 : Nat := 118140960795 + 2780257 * 2 ^ 59
def prefixEnd_2780257 : Nat := 4983230072969 + 3 ^ 40 * 2780257 * 2
def baseEnd_2780257 : Nat := 951738789351622643600891

theorem tailTrace_2780257 : CollatzResearch.WordTrace tailWord_2780257 prefixEnd_2780257 951738789351622643600891 := by
  unfold tailWord_2780257
  simp only [CollatzResearch.WordTrace]
  refine ⟨101404303488611193937555025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67602868992407462625036683 101404303488611193937555025)
  ·
    refine ⟨76053227616458395453166269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101404303488611193937555025 76053227616458395453166269)
    ·
      refine ⟨28519960356171898294937351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76053227616458395453166269 28519960356171898294937351)
      ·
        refine ⟨42779940534257847442406027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28519960356171898294937351 42779940534257847442406027)
        ·
          refine ⟨64169910801386771163609041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42779940534257847442406027 64169910801386771163609041)
          ·
            refine ⟨48127433101040078372706781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64169910801386771163609041 48127433101040078372706781)
            ·
              refine ⟨18047787412890029389765043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48127433101040078372706781 18047787412890029389765043)
              ·
                refine ⟨27071681119335044084647565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18047787412890029389765043 27071681119335044084647565)
                ·
                  refine ⟨10151880419750641531742837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27071681119335044084647565 10151880419750641531742837)
                  ·
                    refine ⟨951738789351622643600891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10151880419750641531742837 951738789351622643600891)
                    ·
                      rfl

theorem cell22_2780257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2780257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780257 prefixEnd_2780257 := by exact prefixLift 2780257
  have htrace : WordTrace (prefixWord ++ tailWord_2780257) baseStart_2780257 baseEnd_2780257 := by
    simpa [prefixWord, tailWord_2780257, baseEnd_2780257] using wordTrace_append hprefix tailTrace_2780257
  have hstable : (prefixWord ++ tailWord_2780257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780257).length < 2 ^ (prefixWord ++ tailWord_2780257).sum := by decide
  have hdescent : baseEnd_2780257 < baseStart_2780257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780259 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 4]
def baseStart_2780259 : Nat := 118140960795 + 2780259 * 2 ^ 59
def prefixEnd_2780259 : Nat := 4983230072969 + 3 ^ 40 * 2780259 * 2
def baseEnd_2780259 : Nat := 317246491330831768350295

theorem tailTrace_2780259 : CollatzResearch.WordTrace tailWord_2780259 prefixEnd_2780259 317246491330831768350295 := by
  unfold tailWord_2780259
  simp only [CollatzResearch.WordTrace]
  refine ⟨101404376434603948279127831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67602917623069298852751887 101404376434603948279127831)
  ·
    refine ⟨152106564651905922418691747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101404376434603948279127831 152106564651905922418691747)
    ·
      refine ⟨228159846977858883628037621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152106564651905922418691747 228159846977858883628037621)
      ·
        refine ⟨21389985654174270340128527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228159846977858883628037621 21389985654174270340128527)
        ·
          refine ⟨32084978481261405510192791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21389985654174270340128527 32084978481261405510192791)
          ·
            refine ⟨48127467721892108265289187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32084978481261405510192791 48127467721892108265289187)
            ·
              refine ⟨72191201582838162397933781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48127467721892108265289187 72191201582838162397933781)
              ·
                refine ⟨1691981287097769431201573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72191201582838162397933781 1691981287097769431201573)
                ·
                  refine ⟨317246491330831768350295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691981287097769431201573 317246491330831768350295)
                  ·
                    rfl

theorem cell22_2780259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 4].length) (baseStart_2780259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780259 prefixEnd_2780259 := by exact prefixLift 2780259
  have htrace : WordTrace (prefixWord ++ tailWord_2780259) baseStart_2780259 baseEnd_2780259 := by
    simpa [prefixWord, tailWord_2780259, baseEnd_2780259] using wordTrace_append hprefix tailTrace_2780259
  have hstable : (prefixWord ++ tailWord_2780259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780259).length < 2 ^ (prefixWord ++ tailWord_2780259).sum := by decide
  have hdescent : baseEnd_2780259 < baseStart_2780259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780261 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_2780261 : Nat := 118140960795 + 2780261 * 2 ^ 59
def prefixEnd_2780261 : Nat := 4983230072969 + 3 ^ 40 * 2780261 * 2
def baseEnd_2780261 : Nat := 951740158633367966500879

theorem tailTrace_2780261 : CollatzResearch.WordTrace tailWord_2780261 prefixEnd_2780261 951740158633367966500879 := by
  unfold tailWord_2780261
  simp only [CollatzResearch.WordTrace]
  refine ⟨101404449380596702620700637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67602966253731135080467091 101404449380596702620700637)
  ·
    refine ⟨38026668517723763482762739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101404449380596702620700637 38026668517723763482762739)
    ·
      refine ⟨57040002776585645224144109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38026668517723763482762739 57040002776585645224144109)
      ·
        refine ⟨21390001041219616959054041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57040002776585645224144109 21390001041219616959054041)
        ·
          refine ⟨16042500780914712719290531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21390001041219616959054041 16042500780914712719290531)
          ·
            refine ⟨24063751171372069078935797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16042500780914712719290531 24063751171372069078935797)
            ·
              refine ⟨2255976672316131476150231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24063751171372069078935797 2255976672316131476150231)
              ·
                refine ⟨3383965008474197214225347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255976672316131476150231 3383965008474197214225347)
                ·
                  refine ⟨5075947512711295821338021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383965008474197214225347 5075947512711295821338021)
                  ·
                    refine ⟨951740158633367966500879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5075947512711295821338021 951740158633367966500879)
                    ·
                      rfl

theorem cell22_2780261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_2780261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780261 prefixEnd_2780261 := by exact prefixLift 2780261
  have htrace : WordTrace (prefixWord ++ tailWord_2780261) baseStart_2780261 baseEnd_2780261 := by
    simpa [prefixWord, tailWord_2780261, baseEnd_2780261] using wordTrace_append hprefix tailTrace_2780261
  have hstable : (prefixWord ++ tailWord_2780261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780261).length < 2 ^ (prefixWord ++ tailWord_2780261).sum := by decide
  have hdescent : baseEnd_2780261 < baseStart_2780261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780306 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2780306 : Nat := 118140960795 + 2780306 * 2 ^ 59
def prefixEnd_2780306 : Nat := 4983230072969 + 3 ^ 40 * 2780306 * 2
def baseEnd_2780306 : Nat := 951755563053002849125741

theorem tailTrace_2780306 : CollatzResearch.WordTrace tailWord_2780306 prefixEnd_2780306 951755563053002849125741 := by
  unfold tailWord_2780306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25351522666358418826522193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67604060443622450204059181 25351522666358418826522193)
  ·
    refine ⟨19013641999768814119891645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25351522666358418826522193 19013641999768814119891645)
    ·
      refine ⟨7130115749913305294959367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19013641999768814119891645 7130115749913305294959367)
      ·
        refine ⟨10695173624869957942439051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130115749913305294959367 10695173624869957942439051)
        ·
          refine ⟨16042760437304936913658577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10695173624869957942439051 16042760437304936913658577)
          ·
            refine ⟨12032070327978702685243933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16042760437304936913658577 12032070327978702685243933)
            ·
              refine ⟨4512026372992013506966475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12032070327978702685243933 4512026372992013506966475)
              ·
                refine ⟨6768039559488020260449713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512026372992013506966475 6768039559488020260449713)
                ·
                  refine ⟨5076029669616015195337285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768039559488020260449713 5076029669616015195337285)
                  ·
                    refine ⟨951755563053002849125741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076029669616015195337285 951755563053002849125741)
                    ·
                      rfl

theorem cell22_2780306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2780306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780306 prefixEnd_2780306 := by exact prefixLift 2780306
  have htrace : WordTrace (prefixWord ++ tailWord_2780306) baseStart_2780306 baseEnd_2780306 := by
    simpa [prefixWord, tailWord_2780306, baseEnd_2780306] using wordTrace_append hprefix tailTrace_2780306
  have hstable : (prefixWord ++ tailWord_2780306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780306).length < 2 ^ (prefixWord ++ tailWord_2780306).sum := by decide
  have hdescent : baseEnd_2780306 < baseStart_2780306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780342 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2780342 : Nat := 118140960795 + 2780342 * 2 ^ 59
def prefixEnd_2780342 : Nat := 4983230072969 + 3 ^ 40 * 2780342 * 2
def baseEnd_2780342 : Nat := 951767886588710755225631

theorem tailTrace_2780342 : CollatzResearch.WordTrace tailWord_2780342 prefixEnd_2780342 951767886588710755225631 := by
  unfold tailWord_2780342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337962730831453340899955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67604935795535502302932853 6337962730831453340899955)
  ·
    refine ⟨9506944096247180011349933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6337962730831453340899955 9506944096247180011349933)
    ·
      refine ⟨3565104036092692504256225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9506944096247180011349933 3565104036092692504256225)
      ·
        refine ⟨2673828027069519378192169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3565104036092692504256225 2673828027069519378192169)
        ·
          refine ⟨2005371020302139533644127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673828027069519378192169 2005371020302139533644127)
          ·
            refine ⟨3008056530453209300466191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005371020302139533644127 3008056530453209300466191)
            ·
              refine ⟨4512084795679813950699287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008056530453209300466191 4512084795679813950699287)
              ·
                refine ⟨6768127193519720926048931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512084795679813950699287 6768127193519720926048931)
                ·
                  refine ⟨10152190790279581389073397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768127193519720926048931 10152190790279581389073397)
                  ·
                    refine ⟨951767886588710755225631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10152190790279581389073397 951767886588710755225631)
                    ·
                      rfl

theorem cell22_2780342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2780342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780342 prefixEnd_2780342 := by exact prefixLift 2780342
  have htrace : WordTrace (prefixWord ++ tailWord_2780342) baseStart_2780342 baseEnd_2780342 := by
    simpa [prefixWord, tailWord_2780342, baseEnd_2780342] using wordTrace_append hprefix tailTrace_2780342
  have hstable : (prefixWord ++ tailWord_2780342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780342).length < 2 ^ (prefixWord ++ tailWord_2780342).sum := by decide
  have hdescent : baseEnd_2780342 < baseStart_2780342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780347 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_2780347 : Nat := 118140960795 + 2780347 * 2 ^ 59
def prefixEnd_2780347 : Nat := 4983230072969 + 3 ^ 40 * 2780347 * 2
def baseEnd_2780347 : Nat := 951769598190892408850615

theorem tailTrace_2780347 : CollatzResearch.WordTrace tailWord_2780347 prefixEnd_2780347 951769598190892408850615 := by
  unfold tailWord_2780347
  simp only [CollatzResearch.WordTrace]
  refine ⟨101407586058285139308331295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67605057372190092872220863 101407586058285139308331295)
  ·
    refine ⟨152111379087427708962496943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101407586058285139308331295 152111379087427708962496943)
    ·
      refine ⟨228167068631141563443745415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152111379087427708962496943 228167068631141563443745415)
      ·
        refine ⟨342250602946712345165618123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228167068631141563443745415 342250602946712345165618123)
        ·
          refine ⟨513375904420068517748427185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342250602946712345165618123 513375904420068517748427185)
          ·
            refine ⟨385031928315051388311320389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513375904420068517748427185 385031928315051388311320389)
            ·
              refine ⟨72193486559072135308372573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 385031928315051388311320389 72193486559072135308372573)
              ·
                refine ⟨27072557459652050740639715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72193486559072135308372573 27072557459652050740639715)
                ·
                  refine ⟨40608836189478076110959573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27072557459652050740639715 40608836189478076110959573)
                  ·
                    refine ⟨951769598190892408850615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40608836189478076110959573 951769598190892408850615)
                    ·
                      rfl

theorem cell22_2780347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_2780347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780347 prefixEnd_2780347 := by exact prefixLift 2780347
  have htrace : WordTrace (prefixWord ++ tailWord_2780347) baseStart_2780347 baseEnd_2780347 := by
    simpa [prefixWord, tailWord_2780347, baseEnd_2780347] using wordTrace_append hprefix tailTrace_2780347
  have hstable : (prefixWord ++ tailWord_2780347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780347).length < 2 ^ (prefixWord ++ tailWord_2780347).sum := by decide
  have hdescent : baseEnd_2780347 < baseStart_2780347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780349 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 5]
def baseStart_2780349 : Nat := 118140960795 + 2780349 * 2 ^ 59
def prefixEnd_2780349 : Nat := 4983230072969 + 3 ^ 40 * 2780349 * 2
def baseEnd_2780349 : Nat := 317256760943921690100203

theorem tailTrace_2780349 : CollatzResearch.WordTrace tailWord_2780349 prefixEnd_2780349 317256760943921690100203 := by
  unfold tailWord_2780349
  simp only [CollatzResearch.WordTrace]
  refine ⟨101407659004277893649904101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67605106002851929099936067 101407659004277893649904101)
  ·
    refine ⟨19013936063302105059357019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101407659004277893649904101 19013936063302105059357019)
    ·
      refine ⟨28520904094953157589035529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19013936063302105059357019 28520904094953157589035529)
      ·
        refine ⟨21390678071214868191776647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28520904094953157589035529 21390678071214868191776647)
        ·
          refine ⟨32086017106822302287664971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21390678071214868191776647 32086017106822302287664971)
          ·
            refine ⟨48129025660233453431497457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32086017106822302287664971 48129025660233453431497457)
            ·
              refine ⟨36096769245175090073623093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48129025660233453431497457 36096769245175090073623093)
              ·
                refine ⟨3384072116735164694402165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36096769245175090073623093 3384072116735164694402165)
                ·
                  refine ⟨317256760943921690100203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3384072116735164694402165 317256760943921690100203)
                  ·
                    rfl

theorem cell22_2780349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_2780349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780349 prefixEnd_2780349 := by exact prefixLift 2780349
  have htrace : WordTrace (prefixWord ++ tailWord_2780349) baseStart_2780349 baseEnd_2780349 := by
    simpa [prefixWord, tailWord_2780349, baseEnd_2780349] using wordTrace_append hprefix tailTrace_2780349
  have hstable : (prefixWord ++ tailWord_2780349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780349).length < 2 ^ (prefixWord ++ tailWord_2780349).sum := by decide
  have hdescent : baseEnd_2780349 < baseStart_2780349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780353 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2780353 : Nat := 118140960795 + 2780353 * 2 ^ 59
def prefixEnd_2780353 : Nat := 4983230072969 + 3 ^ 40 * 2780353 * 2
def baseEnd_2780353 : Nat := 951771652113510393200597

theorem tailTrace_2780353 : CollatzResearch.WordTrace tailWord_2780353 prefixEnd_2780353 951771652113510393200597 := by
  unfold tailWord_2780353
  simp only [CollatzResearch.WordTrace]
  refine ⟨101407804896263402333049713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67605203264175601555366475 101407804896263402333049713)
  ·
    refine ⟨76055853672197551749787285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101407804896263402333049713 76055853672197551749787285)
    ·
      refine ⟨3565118140884260238271279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76055853672197551749787285 3565118140884260238271279)
      ·
        refine ⟨5347677211326390357406919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565118140884260238271279 5347677211326390357406919)
        ·
          refine ⟨8021515816989585536110379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347677211326390357406919 8021515816989585536110379)
          ·
            refine ⟨12032273725484378304165569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021515816989585536110379 12032273725484378304165569)
            ·
              refine ⟨9024205294113283728124177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12032273725484378304165569 9024205294113283728124177)
              ·
                refine ⟨6768153970584962796093133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9024205294113283728124177 6768153970584962796093133)
                ·
                  refine ⟨2538057738969361048534925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6768153970584962796093133 2538057738969361048534925)
                  ·
                    refine ⟨951771652113510393200597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538057738969361048534925 951771652113510393200597)
                    ·
                      rfl

theorem cell22_2780353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2780353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780353 prefixEnd_2780353 := by exact prefixLift 2780353
  have htrace : WordTrace (prefixWord ++ tailWord_2780353) baseStart_2780353 baseEnd_2780353 := by
    simpa [prefixWord, tailWord_2780353, baseEnd_2780353] using wordTrace_append hprefix tailTrace_2780353
  have hstable : (prefixWord ++ tailWord_2780353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780353).length < 2 ^ (prefixWord ++ tailWord_2780353).sum := by decide
  have hdescent : baseEnd_2780353 < baseStart_2780353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780409 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_2780409 : Nat := 118140960795 + 2780409 * 2 ^ 59
def prefixEnd_2780409 : Nat := 4983230072969 + 3 ^ 40 * 2780409 * 2
def baseEnd_2780409 : Nat := 951790822057944913800425

theorem tailTrace_2780409 : CollatzResearch.WordTrace tailWord_2780409 prefixEnd_2780409 951790822057944913800425 := by
  unfold tailWord_2780409
  simp only [CollatzResearch.WordTrace]
  refine ⟨101409847384060523897088281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67606564922707015931392187 101409847384060523897088281)
  ·
    refine ⟨76057385538045392922816211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101409847384060523897088281 76057385538045392922816211)
    ·
      refine ⟨114086078307068089384224317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76057385538045392922816211 114086078307068089384224317)
      ·
        refine ⟨42782279365150533519084119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114086078307068089384224317 42782279365150533519084119)
        ·
          refine ⟨64173419047725800278626179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42782279365150533519084119 64173419047725800278626179)
          ·
            refine ⟨96260128571588700417939269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64173419047725800278626179 96260128571588700417939269)
            ·
              refine ⟨18048774107172881328363613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96260128571588700417939269 18048774107172881328363613)
              ·
                refine ⟨6768290290189830498136355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18048774107172881328363613 6768290290189830498136355)
                ·
                  refine ⟨10152435435284745747204533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6768290290189830498136355 10152435435284745747204533)
                  ·
                    refine ⟨951790822057944913800425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10152435435284745747204533 951790822057944913800425)
                    ·
                      rfl

theorem cell22_2780409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_2780409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780409 prefixEnd_2780409 := by exact prefixLift 2780409
  have htrace : WordTrace (prefixWord ++ tailWord_2780409) baseStart_2780409 baseEnd_2780409 := by
    simpa [prefixWord, tailWord_2780409, baseEnd_2780409] using wordTrace_append hprefix tailTrace_2780409
  have hstable : (prefixWord ++ tailWord_2780409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780409).length < 2 ^ (prefixWord ++ tailWord_2780409).sum := by decide
  have hdescent : baseEnd_2780409 < baseStart_2780409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780445 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 4]
def baseStart_2780445 : Nat := 118140960795 + 2780445 * 2 ^ 59
def prefixEnd_2780445 : Nat := 4983230072969 + 3 ^ 40 * 2780445 * 2
def baseEnd_2780445 : Nat := 317267715197884273300105

theorem tailTrace_2780445 : CollatzResearch.WordTrace tailWord_2780445 prefixEnd_2780445 317267715197884273300105 := by
  unfold tailWord_2780445
  simp only [CollatzResearch.WordTrace]
  refine ⟨101411160411930102045398789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67607440274620068030265859 101411160411930102045398789)
  ·
    refine ⟨19014592577236894133512273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101411160411930102045398789 19014592577236894133512273)
    ·
      refine ⟨14260944432927670600134205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19014592577236894133512273 14260944432927670600134205)
      ·
        refine ⟨5347854162347876475050327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14260944432927670600134205 5347854162347876475050327)
        ·
          refine ⟨8021781243521814712575491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347854162347876475050327 8021781243521814712575491)
          ·
            refine ⟨12032671865282722068863237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021781243521814712575491 12032671865282722068863237)
            ·
              refine ⟨2256125974740510387911857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12032671865282722068863237 2256125974740510387911857)
              ·
                refine ⟨1692094481055382790933893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256125974740510387911857 1692094481055382790933893)
                ·
                  refine ⟨317267715197884273300105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692094481055382790933893 317267715197884273300105)
                  ·
                    rfl

theorem cell22_2780445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_2780445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780445 prefixEnd_2780445 := by exact prefixLift 2780445
  have htrace : WordTrace (prefixWord ++ tailWord_2780445) baseStart_2780445 baseEnd_2780445 := by
    simpa [prefixWord, tailWord_2780445, baseEnd_2780445] using wordTrace_append hprefix tailTrace_2780445
  have hstable : (prefixWord ++ tailWord_2780445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780445).length < 2 ^ (prefixWord ++ tailWord_2780445).sum := by decide
  have hdescent : baseEnd_2780445 < baseStart_2780445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780456 : List Nat := [2, 1, 5, 1, 2, 1, 3, 7]
def baseStart_2780456 : Nat := 118140960795 + 2780456 * 2 ^ 59
def prefixEnd_2780456 : Nat := 4983230072969 + 3 ^ 40 * 2780456 * 2
def baseEnd_2780456 : Nat := 105756323457605828652809

theorem tailTrace_2780456 : CollatzResearch.WordTrace tailWord_2780456 prefixEnd_2780456 105756323457605828652809 := by
  unfold tailWord_2780456
  simp only [CollatzResearch.WordTrace]
  refine ⟨50705780807445125462024611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67607707743260167282699481 50705780807445125462024611)
  ·
    refine ⟨76058671211167688193036917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50705780807445125462024611 76058671211167688193036917)
    ·
      refine ⟨7130500426046970768097211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76058671211167688193036917 7130500426046970768097211)
      ·
        refine ⟨10695750639070456152145817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130500426046970768097211 10695750639070456152145817)
        ·
          refine ⟨8021812979302842114109363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10695750639070456152145817 8021812979302842114109363)
          ·
            refine ⟨12032719468954263171164045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021812979302842114109363 12032719468954263171164045)
            ·
              refine ⟨4512269800857848689186517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12032719468954263171164045 4512269800857848689186517)
              ·
                refine ⟨105756323457605828652809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4512269800857848689186517 105756323457605828652809)
                ·
                  rfl

theorem cell22_2780456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_2780456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780456 prefixEnd_2780456 := by exact prefixLift 2780456
  have htrace : WordTrace (prefixWord ++ tailWord_2780456) baseStart_2780456 baseEnd_2780456 := by
    simpa [prefixWord, tailWord_2780456, baseEnd_2780456] using wordTrace_append hprefix tailTrace_2780456
  have hstable : (prefixWord ++ tailWord_2780456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780456).length < 2 ^ (prefixWord ++ tailWord_2780456).sum := by decide
  have hdescent : baseEnd_2780456 < baseStart_2780456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780473 : List Nat := [1, 2, 1, 6, 2, 1, 3, 6]
def baseStart_2780473 : Nat := 118140960795 + 2780473 * 2 ^ 59
def prefixEnd_2780473 : Nat := 4983230072969 + 3 ^ 40 * 2780473 * 2
def baseEnd_2780473 : Nat := 105756970062874453355581

theorem tailTrace_2780473 : CollatzResearch.WordTrace tailWord_2780473 prefixEnd_2780473 105756970062874453355581 := by
  unfold tailWord_2780473
  simp only [CollatzResearch.WordTrace]
  refine ⟨101412181655828662827418073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67608121103885775218278715 101412181655828662827418073)
  ·
    refine ⟨76059136241871497120563555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101412181655828662827418073 76059136241871497120563555)
    ·
      refine ⟨114088704362807245680845333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76059136241871497120563555 114088704362807245680845333)
      ·
        refine ⟨5347908017006589641289625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114088704362807245680845333 5347908017006589641289625)
        ·
          refine ⟨4010931012754942230967219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5347908017006589641289625 4010931012754942230967219)
          ·
            refine ⟨6016396519132413346450829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010931012754942230967219 6016396519132413346450829)
            ·
              refine ⟨2256148694674655004919061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6016396519132413346450829 2256148694674655004919061)
              ·
                refine ⟨105756970062874453355581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2256148694674655004919061 105756970062874453355581)
                ·
                  rfl

theorem cell22_2780473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 6].length) (baseStart_2780473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780473 prefixEnd_2780473 := by exact prefixLift 2780473
  have htrace : WordTrace (prefixWord ++ tailWord_2780473) baseStart_2780473 baseEnd_2780473 := by
    simpa [prefixWord, tailWord_2780473, baseEnd_2780473] using wordTrace_append hprefix tailTrace_2780473
  have hstable : (prefixWord ++ tailWord_2780473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780473).length < 2 ^ (prefixWord ++ tailWord_2780473).sum := by decide
  have hdescent : baseEnd_2780473 < baseStart_2780473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780499 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_2780499 : Nat := 118140960795 + 2780499 * 2 ^ 59
def prefixEnd_2780499 : Nat := 4983230072969 + 3 ^ 40 * 2780499 * 2
def baseEnd_2780499 : Nat := 951821630897214679050149

theorem tailTrace_2780499 : CollatzResearch.WordTrace tailWord_2780499 prefixEnd_2780499 951821630897214679050149 := by
  unfold tailWord_2780499
  simp only [CollatzResearch.WordTrace]
  refine ⟨101413129953734469267864551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67608753302489646178576367 101413129953734469267864551)
  ·
    refine ⟨152119694930601703901796827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101413129953734469267864551 152119694930601703901796827)
    ·
      refine ⟨228179542395902555852695241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152119694930601703901796827 228179542395902555852695241)
      ·
        refine ⟨171134656796926916889521431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228179542395902555852695241 171134656796926916889521431)
        ·
          refine ⟨256701985195390375334282147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171134656796926916889521431 256701985195390375334282147)
          ·
            refine ⟨385052977793085563001423221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256701985195390375334282147 385052977793085563001423221)
            ·
              refine ⟨36098716668101771531383427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 385052977793085563001423221 36098716668101771531383427)
              ·
                refine ⟨54148075002152657297075141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36098716668101771531383427 54148075002152657297075141)
                ·
                  refine ⟨10152764062903623243201589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54148075002152657297075141 10152764062903623243201589)
                  ·
                    refine ⟨951821630897214679050149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10152764062903623243201589 951821630897214679050149)
                    ·
                      rfl

theorem cell22_2780499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_2780499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780499 prefixEnd_2780499 := by exact prefixLift 2780499
  have htrace : WordTrace (prefixWord ++ tailWord_2780499) baseStart_2780499 baseEnd_2780499 := by
    simpa [prefixWord, tailWord_2780499, baseEnd_2780499] using wordTrace_append hprefix tailTrace_2780499
  have hstable : (prefixWord ++ tailWord_2780499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780499).length < 2 ^ (prefixWord ++ tailWord_2780499).sum := by decide
  have hdescent : baseEnd_2780499 < baseStart_2780499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780501 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 7]
def baseStart_2780501 : Nat := 118140960795 + 2780501 * 2 ^ 59
def prefixEnd_2780501 : Nat := 4983230072969 + 3 ^ 40 * 2780501 * 2
def baseEnd_2780501 : Nat := 317274105179362446833381

theorem tailTrace_2780501 : CollatzResearch.WordTrace tailWord_2780501 prefixEnd_2780501 317274105179362446833381 := by
  unfold tailWord_2780501
  simp only [CollatzResearch.WordTrace]
  refine ⟨101413202899727223609437357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67608801933151482406291571 101413202899727223609437357)
  ·
    refine ⟨38029951087397708853539009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101413202899727223609437357 38029951087397708853539009)
    ·
      refine ⟨28522463315548281640154257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38029951087397708853539009 28522463315548281640154257)
      ·
        refine ⟨21391847486661211230115693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28522463315548281640154257 21391847486661211230115693)
        ·
          refine ⟨8021942807497954211293385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21391847486661211230115693 8021942807497954211293385)
          ·
            refine ⟨6016457105623465658470039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8021942807497954211293385 6016457105623465658470039)
            ·
              refine ⟨9024685658435198487705059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016457105623465658470039 9024685658435198487705059)
              ·
                refine ⟨13537028487652797731557589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9024685658435198487705059 13537028487652797731557589)
                ·
                  refine ⟨317274105179362446833381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13537028487652797731557589 317274105179362446833381)
                  ·
                    rfl

theorem cell22_2780501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_2780501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780501 prefixEnd_2780501 := by exact prefixLift 2780501
  have htrace : WordTrace (prefixWord ++ tailWord_2780501) baseStart_2780501 baseEnd_2780501 := by
    simpa [prefixWord, tailWord_2780501, baseEnd_2780501] using wordTrace_append hprefix tailTrace_2780501
  have hstable : (prefixWord ++ tailWord_2780501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780501).length < 2 ^ (prefixWord ++ tailWord_2780501).sum := by decide
  have hdescent : baseEnd_2780501 < baseStart_2780501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780516 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2780516 : Nat := 118140960795 + 2780516 * 2 ^ 59
def prefixEnd_2780516 : Nat := 4983230072969 + 3 ^ 40 * 2780516 * 2
def baseEnd_2780516 : Nat := 951827450344632301375097

theorem tailTrace_2780516 : CollatzResearch.WordTrace tailWord_2780516 prefixEnd_2780516 951827450344632301375097 := by
  unfold tailWord_2780516
  simp only [CollatzResearch.WordTrace]
  refine ⟨50706874997336440585616701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67609166663115254114155601 50706874997336440585616701)
  ·
    refine ⟨19015078124001165219606263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50706874997336440585616701 19015078124001165219606263)
    ·
      refine ⟨28522617186001747829409395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19015078124001165219606263 28522617186001747829409395)
      ·
        refine ⟨42783925779002621744114093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28522617186001747829409395 42783925779002621744114093)
        ·
          refine ⟨16043972167125983154042785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42783925779002621744114093 16043972167125983154042785)
          ·
            refine ⟨12032979125344487365532089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16043972167125983154042785 12032979125344487365532089)
            ·
              refine ⟨9024734344008365524149067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12032979125344487365532089 9024734344008365524149067)
              ·
                refine ⟨13537101516012548286223601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9024734344008365524149067 13537101516012548286223601)
                ·
                  refine ⟨10152826137009411214667701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13537101516012548286223601 10152826137009411214667701)
                  ·
                    refine ⟨951827450344632301375097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10152826137009411214667701 951827450344632301375097)
                    ·
                      rfl

theorem cell22_2780516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2780516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780516 prefixEnd_2780516 := by exact prefixLift 2780516
  have htrace : WordTrace (prefixWord ++ tailWord_2780516) baseStart_2780516 baseEnd_2780516 := by
    simpa [prefixWord, tailWord_2780516, baseEnd_2780516] using wordTrace_append hprefix tailTrace_2780516
  have hstable : (prefixWord ++ tailWord_2780516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780516).length < 2 ^ (prefixWord ++ tailWord_2780516).sum := by decide
  have hdescent : baseEnd_2780516 < baseStart_2780516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780548 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2780548 : Nat := 118140960795 + 2780548 * 2 ^ 59
def prefixEnd_2780548 : Nat := 4983230072969 + 3 ^ 40 * 2780548 * 2
def baseEnd_2780548 : Nat := 951838404598594884574999

theorem tailTrace_2780548 : CollatzResearch.WordTrace tailWord_2780548 prefixEnd_2780548 951838404598594884574999 := by
  unfold tailWord_2780548
  simp only [CollatzResearch.WordTrace]
  refine ⟨50707458565278475318199149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67609944753704633757598865 50707458565278475318199149)
  ·
    refine ⟨19015296961979428244324681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50707458565278475318199149 19015296961979428244324681)
    ·
      refine ⟨14261472721484571183243511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19015296961979428244324681 14261472721484571183243511)
      ·
        refine ⟨21392209082226856774865267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14261472721484571183243511 21392209082226856774865267)
        ·
          refine ⟨32088313623340285162297901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392209082226856774865267 32088313623340285162297901)
          ·
            refine ⟨12033117608752606935861713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32088313623340285162297901 12033117608752606935861713)
            ·
              refine ⟨9024838206564455201896285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12033117608752606935861713 9024838206564455201896285)
              ·
                refine ⟨3384314327461670700711107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9024838206564455201896285 3384314327461670700711107)
                ·
                  refine ⟨5076471491192506051066661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384314327461670700711107 5076471491192506051066661)
                  ·
                    refine ⟨951838404598594884574999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076471491192506051066661 951838404598594884574999)
                    ·
                      rfl

theorem cell22_2780548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2780548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780548 prefixEnd_2780548 := by exact prefixLift 2780548
  have htrace : WordTrace (prefixWord ++ tailWord_2780548) baseStart_2780548 baseEnd_2780548 := by
    simpa [prefixWord, tailWord_2780548, baseEnd_2780548] using wordTrace_append hprefix tailTrace_2780548
  have hstable : (prefixWord ++ tailWord_2780548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780548).length < 2 ^ (prefixWord ++ tailWord_2780548).sum := by decide
  have hdescent : baseEnd_2780548 < baseStart_2780548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780559 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_2780559 : Nat := 118140960795 + 2780559 * 2 ^ 59
def prefixEnd_2780559 : Nat := 4983230072969 + 3 ^ 40 * 2780559 * 2
def baseEnd_2780559 : Nat := 951842170123394522549965

theorem tailTrace_2780559 : CollatzResearch.WordTrace tailWord_2780559 prefixEnd_2780559 951842170123394522549965 := by
  unfold tailWord_2780559
  simp only [CollatzResearch.WordTrace]
  refine ⟨101415318333517099515048731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67610212222344733010032487 101415318333517099515048731)
  ·
    refine ⟨152122977500275649272573097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101415318333517099515048731 152122977500275649272573097)
    ·
      refine ⟨114092233125206736954429823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152122977500275649272573097 114092233125206736954429823)
      ·
        refine ⟨171138349687810105431644735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114092233125206736954429823 171138349687810105431644735)
        ·
          refine ⟨256707524531715158147467103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171138349687810105431644735 256707524531715158147467103)
          ·
            refine ⟨385061286797572737221200655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256707524531715158147467103 385061286797572737221200655)
            ·
              refine ⟨577591930196359105831800983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385061286797572737221200655 577591930196359105831800983)
              ·
                refine ⟨866387895294538658747701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577591930196359105831800983 866387895294538658747701475)
                ·
                  refine ⟨1299581842941807988121552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866387895294538658747701475 1299581842941807988121552213)
                  ·
                    refine ⟨951842170123394522549965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1299581842941807988121552213 951842170123394522549965)
                    ·
                      rfl

theorem cell22_2780559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_2780559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780559 prefixEnd_2780559 := by exact prefixLift 2780559
  have htrace : WordTrace (prefixWord ++ tailWord_2780559) baseStart_2780559 baseEnd_2780559 := by
    simpa [prefixWord, tailWord_2780559, baseEnd_2780559] using wordTrace_append hprefix tailTrace_2780559
  have hstable : (prefixWord ++ tailWord_2780559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780559).length < 2 ^ (prefixWord ++ tailWord_2780559).sum := by decide
  have hdescent : baseEnd_2780559 < baseStart_2780559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780576 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_2780576 : Nat := 118140960795 + 2780576 * 2 ^ 59
def prefixEnd_2780576 : Nat := 4983230072969 + 3 ^ 40 * 2780576 * 2
def baseEnd_2780576 : Nat := 951847989570812144874913

theorem tailTrace_2780576 : CollatzResearch.WordTrace tailWord_2780576 prefixEnd_2780576 951847989570812144874913 := by
  unfold tailWord_2780576
  simp only [CollatzResearch.WordTrace]
  refine ⟨50707969187227755709208791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67610625582970340945611721 50707969187227755709208791)
  ·
    refine ⟨76061953780841633563813187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50707969187227755709208791 76061953780841633563813187)
    ·
      refine ⟨114092930671262450345719781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76061953780841633563813187 114092930671262450345719781)
      ·
        refine ⟨21392424500861709439822459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114092930671262450345719781 21392424500861709439822459)
        ·
          refine ⟨32088636751292564159733689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21392424500861709439822459 32088636751292564159733689)
          ·
            refine ⟨24066477563469423119800267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32088636751292564159733689 24066477563469423119800267)
            ·
              refine ⟨36099716345204134679700401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24066477563469423119800267 36099716345204134679700401)
              ·
                refine ⟨27074787258903101009775301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36099716345204134679700401 27074787258903101009775301)
                ·
                  refine ⟨5076522611044331439332869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27074787258903101009775301 5076522611044331439332869)
                  ·
                    refine ⟨951847989570812144874913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076522611044331439332869 951847989570812144874913)
                    ·
                      rfl

theorem cell22_2780576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_2780576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780576 prefixEnd_2780576 := by exact prefixLift 2780576
  have htrace : WordTrace (prefixWord ++ tailWord_2780576) baseStart_2780576 baseEnd_2780576 := by
    simpa [prefixWord, tailWord_2780576, baseEnd_2780576] using wordTrace_append hprefix tailTrace_2780576
  have hstable : (prefixWord ++ tailWord_2780576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780576).length < 2 ^ (prefixWord ++ tailWord_2780576).sum := by decide
  have hdescent : baseEnd_2780576 < baseStart_2780576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780593 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_2780593 : Nat := 118140960795 + 2780593 * 2 ^ 59
def prefixEnd_2780593 : Nat := 4983230072969 + 3 ^ 40 * 2780593 * 2
def baseEnd_2780593 : Nat := 951853809018229767199861

theorem tailTrace_2780593 : CollatzResearch.WordTrace tailWord_2780593 prefixEnd_2780593 951853809018229767199861 := by
  unfold tailWord_2780593
  simp only [CollatzResearch.WordTrace]
  refine ⟨101416558415393923321786433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67611038943595948881190955 101416558415393923321786433)
  ·
    refine ⟨76062418811545442491339825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101416558415393923321786433 76062418811545442491339825)
    ·
      refine ⟨57046814108659081868504869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76062418811545442491339825 57046814108659081868504869)
      ·
        refine ⟨10696277645373577850344663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57046814108659081868504869 10696277645373577850344663)
        ·
          refine ⟨16044416468060366775516995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10696277645373577850344663 16044416468060366775516995)
          ·
            refine ⟨24066624702090550163275493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16044416468060366775516995 24066624702090550163275493)
            ·
              refine ⟨4512492131641978155614155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24066624702090550163275493 4512492131641978155614155)
              ·
                refine ⟨6768738197462967233421233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512492131641978155614155 6768738197462967233421233)
                ·
                  refine ⟨5076553648097225425065925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768738197462967233421233 5076553648097225425065925)
                  ·
                    refine ⟨951853809018229767199861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076553648097225425065925 951853809018229767199861)
                    ·
                      rfl

theorem cell22_2780593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_2780593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780593 prefixEnd_2780593 := by exact prefixLift 2780593
  have htrace : WordTrace (prefixWord ++ tailWord_2780593) baseStart_2780593 baseEnd_2780593 := by
    simpa [prefixWord, tailWord_2780593, baseEnd_2780593] using wordTrace_append hprefix tailTrace_2780593
  have hstable : (prefixWord ++ tailWord_2780593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780593).length < 2 ^ (prefixWord ++ tailWord_2780593).sum := by decide
  have hdescent : baseEnd_2780593 < baseStart_2780593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780612 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2780612 : Nat := 118140960795 + 2780612 * 2 ^ 59
def prefixEnd_2780612 : Nat := 4983230072969 + 3 ^ 40 * 2780612 * 2
def baseEnd_2780612 : Nat := 951860313106520050974803

theorem tailTrace_2780612 : CollatzResearch.WordTrace tailWord_2780612 prefixEnd_2780612 951860313106520050974803 := by
  unfold tailWord_2780612
  simp only [CollatzResearch.WordTrace]
  refine ⟨50708625701162544783364045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67611500934883393044485393 50708625701162544783364045)
  ·
    refine ⟨19015734637935954293761517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50708625701162544783364045 19015734637935954293761517)
    ·
      refine ⟨7130900489225982860160569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19015734637935954293761517 7130900489225982860160569)
      ·
        refine ⟨5348175366919487145120427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7130900489225982860160569 5348175366919487145120427)
        ·
          refine ⟨8022263050379230717680641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5348175366919487145120427 8022263050379230717680641)
          ·
            refine ⟨6016697287784423038260481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8022263050379230717680641 6016697287784423038260481)
            ·
              refine ⟨4512522965838317278695361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6016697287784423038260481 4512522965838317278695361)
              ·
                refine ⟨3384392224378737959021521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4512522965838317278695361 3384392224378737959021521)
                ·
                  refine ⟨2538294168284053469266141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384392224378737959021521 2538294168284053469266141)
                  ·
                    refine ⟨951860313106520050974803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538294168284053469266141 951860313106520050974803)
                    ·
                      rfl

theorem cell22_2780612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2780612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780612 prefixEnd_2780612 := by exact prefixLift 2780612
  have htrace : WordTrace (prefixWord ++ tailWord_2780612) baseStart_2780612 baseEnd_2780612 := by
    simpa [prefixWord, tailWord_2780612, baseEnd_2780612] using wordTrace_append hprefix tailTrace_2780612
  have hstable : (prefixWord ++ tailWord_2780612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780612).length < 2 ^ (prefixWord ++ tailWord_2780612).sum := by decide
  have hdescent : baseEnd_2780612 < baseStart_2780612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780657 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 1, 3]
def baseStart_2780657 : Nat := 118140960795 + 2780657 * 2 ^ 59
def prefixEnd_2780657 : Nat := 4983230072969 + 3 ^ 40 * 2780657 * 2
def baseEnd_2780657 : Nat := 951875717526154933599665

theorem tailTrace_2780657 : CollatzResearch.WordTrace tailWord_2780657 prefixEnd_2780657 951875717526154933599665 := by
  unfold tailWord_2780657
  simp only [CollatzResearch.WordTrace]
  refine ⟨101418892687162062252116225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67612595124774708168077483 101418892687162062252116225)
  ·
    refine ⟨76064169515371546689087169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101418892687162062252116225 76064169515371546689087169)
    ·
      refine ⟨57048127136528660016815377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76064169515371546689087169 57048127136528660016815377)
      ·
        refine ⟨42786095352396495012611533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57048127136528660016815377 42786095352396495012611533)
        ·
          refine ⟨16044785757148685629729325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42786095352396495012611533 16044785757148685629729325)
          ·
            refine ⟨6016794658930757111148497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16044785757148685629729325 6016794658930757111148497)
            ·
              refine ⟨4512595994198067833361373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6016794658930757111148497 4512595994198067833361373)
              ·
                refine ⟨1692223497824275437510515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4512595994198067833361373 1692223497824275437510515)
                ·
                  refine ⟨2538335246736413156265773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692223497824275437510515 2538335246736413156265773)
                  ·
                    refine ⟨951875717526154933599665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538335246736413156265773 951875717526154933599665)
                    ·
                      rfl

theorem cell22_2780657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_2780657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780657 prefixEnd_2780657 := by exact prefixLift 2780657
  have htrace : WordTrace (prefixWord ++ tailWord_2780657) baseStart_2780657 baseEnd_2780657 := by
    simpa [prefixWord, tailWord_2780657, baseEnd_2780657] using wordTrace_append hprefix tailTrace_2780657
  have hstable : (prefixWord ++ tailWord_2780657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780657).length < 2 ^ (prefixWord ++ tailWord_2780657).sum := by decide
  have hdescent : baseEnd_2780657 < baseStart_2780657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780674 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2780674 : Nat := 118140960795 + 2780674 * 2 ^ 59
def prefixEnd_2780674 : Nat := 4983230072969 + 3 ^ 40 * 2780674 * 2
def baseEnd_2780674 : Nat := 951881536973572555924613

theorem tailTrace_2780674 : CollatzResearch.WordTrace tailWord_2780674 prefixEnd_2780674 951881536973572555924613 := by
  unfold tailWord_2780674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25354878182025118538871269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67613008485400316103656717 25354878182025118538871269)
  ·
    refine ⟨4754039659129709726038363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25354878182025118538871269 4754039659129709726038363)
    ·
      refine ⟨7131059488694564589057545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4754039659129709726038363 7131059488694564589057545)
      ·
        refine ⟨5348294616520923441793159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7131059488694564589057545 5348294616520923441793159)
        ·
          refine ⟨8022441924781385162689739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5348294616520923441793159 8022441924781385162689739)
          ·
            refine ⟨12033662887172077744034609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8022441924781385162689739 12033662887172077744034609)
            ·
              refine ⟨9025247165379058308025957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12033662887172077744034609 9025247165379058308025957)
              ·
                refine ⟨1692233843508573432754867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9025247165379058308025957 1692233843508573432754867)
                ·
                  refine ⟨2538350765262860149132301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692233843508573432754867 2538350765262860149132301)
                  ·
                    refine ⟨951881536973572555924613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538350765262860149132301 951881536973572555924613)
                    ·
                      rfl

theorem cell22_2780674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2780674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780674 prefixEnd_2780674 := by exact prefixLift 2780674
  have htrace : WordTrace (prefixWord ++ tailWord_2780674) baseStart_2780674 baseEnd_2780674 := by
    simpa [prefixWord, tailWord_2780674, baseEnd_2780674] using wordTrace_append hprefix tailTrace_2780674
  have hstable : (prefixWord ++ tailWord_2780674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780674).length < 2 ^ (prefixWord ++ tailWord_2780674).sum := by decide
  have hdescent : baseEnd_2780674 < baseStart_2780674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780700 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2780700 : Nat := 118140960795 + 2780700 * 2 ^ 59
def prefixEnd_2780700 : Nat := 4983230072969 + 3 ^ 40 * 2780700 * 2
def baseEnd_2780700 : Nat := 951890437304917154774533

theorem tailTrace_2780700 : CollatzResearch.WordTrace tailWord_2780700 prefixEnd_2780700 951890437304917154774533 := by
  unfold tailWord_2780700
  simp only [CollatzResearch.WordTrace]
  refine ⟨50710230513003140297965777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67613640684004187063954369 50710230513003140297965777)
  ·
    refine ⟨38032672884752355223474333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50710230513003140297965777 38032672884752355223474333)
    ·
      refine ⟨14262252331782133208802875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38032672884752355223474333 14262252331782133208802875)
      ·
        refine ⟨21393378497673199813204313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14262252331782133208802875 21393378497673199813204313)
        ·
          refine ⟨16045033873254899859903235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21393378497673199813204313 16045033873254899859903235)
          ·
            refine ⟨24067550809882349789854853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16045033873254899859903235 24067550809882349789854853)
            ·
              refine ⟨4512665776852940585597785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24067550809882349789854853 4512665776852940585597785)
              ·
                refine ⟨3384499332639705439198339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4512665776852940585597785 3384499332639705439198339)
                ·
                  refine ⟨5076748998959558158797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384499332639705439198339 5076748998959558158797509)
                  ·
                    refine ⟨951890437304917154774533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076748998959558158797509 951890437304917154774533)
                    ·
                      rfl

theorem cell22_2780700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2780700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780700 prefixEnd_2780700 := by exact prefixLift 2780700
  have htrace : WordTrace (prefixWord ++ tailWord_2780700) baseStart_2780700 baseEnd_2780700 := by
    simpa [prefixWord, tailWord_2780700, baseEnd_2780700] using wordTrace_append hprefix tailTrace_2780700
  have hstable : (prefixWord ++ tailWord_2780700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780700).length < 2 ^ (prefixWord ++ tailWord_2780700).sum := by decide
  have hdescent : baseEnd_2780700 < baseStart_2780700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780728 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_2780728 : Nat := 118140960795 + 2780728 * 2 ^ 59
def prefixEnd_2780728 : Nat := 4983230072969 + 3 ^ 40 * 2780728 * 2
def baseEnd_2780728 : Nat := 951900022277134415074447

theorem tailTrace_2780728 : CollatzResearch.WordTrace tailWord_2780728 prefixEnd_2780728 951900022277134415074447 := by
  unfold tailWord_2780728
  simp only [CollatzResearch.WordTrace]
  refine ⟨50710741134952420688975419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67614321513269894251967225 50710741134952420688975419)
  ·
    refine ⟨76066111702428631033463129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50710741134952420688975419 76066111702428631033463129)
    ·
      refine ⟨57049583776821473275097347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76066111702428631033463129 57049583776821473275097347)
      ·
        refine ⟨85574375665232209912646021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57049583776821473275097347 85574375665232209912646021)
        ·
          refine ⟨16045195437231039358621129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85574375665232209912646021 16045195437231039358621129)
          ·
            refine ⟨12033896577923279518965847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16045195437231039358621129 12033896577923279518965847)
            ·
              refine ⟨18050844866884919278448771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12033896577923279518965847 18050844866884919278448771)
              ·
                refine ⟨27076267300327378917673157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18050844866884919278448771 27076267300327378917673157)
                ·
                  refine ⟨5076800118811383547063717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27076267300327378917673157 5076800118811383547063717)
                  ·
                    refine ⟨951900022277134415074447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076800118811383547063717 951900022277134415074447)
                    ·
                      rfl

theorem cell22_2780728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_2780728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780728 prefixEnd_2780728 := by exact prefixLift 2780728
  have htrace : WordTrace (prefixWord ++ tailWord_2780728) baseStart_2780728 baseEnd_2780728 := by
    simpa [prefixWord, tailWord_2780728, baseEnd_2780728] using wordTrace_append hprefix tailTrace_2780728
  have hstable : (prefixWord ++ tailWord_2780728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780728).length < 2 ^ (prefixWord ++ tailWord_2780728).sum := by decide
  have hdescent : baseEnd_2780728 < baseStart_2780728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780730 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_2780730 : Nat := 118140960795 + 2780730 * 2 ^ 59
def prefixEnd_2780730 : Nat := 4983230072969 + 3 ^ 40 * 2780730 * 2
def baseEnd_2780730 : Nat := 951900706918007076524441

theorem tailTrace_2780730 : CollatzResearch.WordTrace tailWord_2780730 prefixEnd_2780730 951900706918007076524441 := by
  unfold tailWord_2780730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25355388803974398929880911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67614370143931730479682429 25355388803974398929880911)
  ·
    refine ⟨38033083205961598394821367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25355388803974398929880911 38033083205961598394821367)
    ·
      refine ⟨57049624808942397592232051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38033083205961598394821367 57049624808942397592232051)
      ·
        refine ⟨85574437213413596388348077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57049624808942397592232051 85574437213413596388348077)
        ·
          refine ⟨32090413955030098645630529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85574437213413596388348077 32090413955030098645630529)
          ·
            refine ⟨24067810466272573984222897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32090413955030098645630529 24067810466272573984222897)
            ·
              refine ⟨18050857849704430488167173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24067810466272573984222897 18050857849704430488167173)
              ·
                refine ⟨3384535846819580716531345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18050857849704430488167173 3384535846819580716531345)
                ·
                  refine ⟨2538401885114685537398509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384535846819580716531345 2538401885114685537398509)
                  ·
                    refine ⟨951900706918007076524441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538401885114685537398509 951900706918007076524441)
                    ·
                      rfl

theorem cell22_2780730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_2780730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780730 prefixEnd_2780730 := by exact prefixLift 2780730
  have htrace : WordTrace (prefixWord ++ tailWord_2780730) baseStart_2780730 baseEnd_2780730 := by
    simpa [prefixWord, tailWord_2780730, baseEnd_2780730] using wordTrace_append hprefix tailTrace_2780730
  have hstable : (prefixWord ++ tailWord_2780730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780730).length < 2 ^ (prefixWord ++ tailWord_2780730).sum := by decide
  have hdescent : baseEnd_2780730 < baseStart_2780730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780732 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 6]
def baseStart_2780732 : Nat := 118140960795 + 2780732 * 2 ^ 59
def prefixEnd_2780732 : Nat := 4983230072969 + 3 ^ 40 * 2780732 * 2
def baseEnd_2780732 : Nat := 317300463852959912658145

theorem tailTrace_2780732 : CollatzResearch.WordTrace tailWord_2780732 prefixEnd_2780732 317300463852959912658145 := by
  unfold tailWord_2780732
  simp only [CollatzResearch.WordTrace]
  refine ⟨50710814080945175030548225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67614418774593566707397633 50710814080945175030548225)
  ·
    refine ⟨38033110560708881272911169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50710814080945175030548225 38033110560708881272911169)
    ·
      refine ⟨28524832920531660954683377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38033110560708881272911169 28524832920531660954683377)
      ·
        refine ⟨21393624690398745716012533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28524832920531660954683377 21393624690398745716012533)
        ·
          refine ⟨2005652314724882410876175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21393624690398745716012533 2005652314724882410876175)
          ·
            refine ⟨3008478472087323616314263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005652314724882410876175 3008478472087323616314263)
            ·
              refine ⟨4512717708130985424471395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008478472087323616314263 4512717708130985424471395)
              ·
                refine ⟨6769076562196478136707093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512717708130985424471395 6769076562196478136707093)
                ·
                  refine ⟨317300463852959912658145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6769076562196478136707093 317300463852959912658145)
                  ·
                    rfl

theorem cell22_2780732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_2780732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780732 prefixEnd_2780732 := by exact prefixLift 2780732
  have htrace : WordTrace (prefixWord ++ tailWord_2780732) baseStart_2780732 baseEnd_2780732 := by
    simpa [prefixWord, tailWord_2780732, baseEnd_2780732] using wordTrace_append hprefix tailTrace_2780732
  have hstable : (prefixWord ++ tailWord_2780732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780732).length < 2 ^ (prefixWord ++ tailWord_2780732).sum := by decide
  have hdescent : baseEnd_2780732 < baseStart_2780732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780790 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_2780790 : Nat := 118140960795 + 2780790 * 2 ^ 59
def prefixEnd_2780790 : Nat := 4983230072969 + 3 ^ 40 * 2780790 * 2
def baseEnd_2780790 : Nat := 951921246144186920024257

theorem tailTrace_2780790 : CollatzResearch.WordTrace tailWord_2780790 prefixEnd_2780790 951921246144186920024257 := by
  unfold tailWord_2780790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338983974730014122919239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67615829063786817311138549 6338983974730014122919239)
  ·
    refine ⟨9508475962095021184378859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6338983974730014122919239 9508475962095021184378859)
    ·
      refine ⟨14262713943142531776568289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9508475962095021184378859 14262713943142531776568289)
      ·
        refine ⟨10697035457356898832426217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14262713943142531776568289 10697035457356898832426217)
        ·
          refine ⟨8022776593017674124319663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10697035457356898832426217 8022776593017674124319663)
          ·
            refine ⟨12034164889526511186479495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8022776593017674124319663 12034164889526511186479495)
            ·
              refine ⟨18051247334289766779719243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034164889526511186479495 18051247334289766779719243)
              ·
                refine ⟨27076871001434650169578865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18051247334289766779719243 27076871001434650169578865)
                ·
                  refine ⟨20307653251075987627184149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27076871001434650169578865 20307653251075987627184149)
                  ·
                    refine ⟨951921246144186920024257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20307653251075987627184149 951921246144186920024257)
                    ·
                      rfl

theorem cell22_2780790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_2780790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780790 prefixEnd_2780790 := by exact prefixLift 2780790
  have htrace : WordTrace (prefixWord ++ tailWord_2780790) baseStart_2780790 baseEnd_2780790 := by
    simpa [prefixWord, tailWord_2780790, baseEnd_2780790] using wordTrace_append hprefix tailTrace_2780790
  have hstable : (prefixWord ++ tailWord_2780790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780790).length < 2 ^ (prefixWord ++ tailWord_2780790).sum := by decide
  have hdescent : baseEnd_2780790 < baseStart_2780790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780835 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 1, 4]
def baseStart_2780835 : Nat := 118140960795 + 2780835 * 2 ^ 59
def prefixEnd_2780835 : Nat := 4983230072969 + 3 ^ 40 * 2780835 * 2
def baseEnd_2780835 : Nat := 951936650563821802649119

theorem tailTrace_2780835 : CollatzResearch.WordTrace tailWord_2780835 prefixEnd_2780835 951936650563821802649119 := by
  unfold tailWord_2780835
  simp only [CollatzResearch.WordTrace]
  refine ⟨101425384880517198652095959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67616923253678132434730639 101425384880517198652095959)
  ·
    refine ⟨152138077320775797978143939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101425384880517198652095959 152138077320775797978143939)
    ·
      refine ⟨228207115981163696967215909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152138077320775797978143939 228207115981163696967215909)
      ·
        refine ⟨42788834246468193181352983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228207115981163696967215909 42788834246468193181352983)
        ·
          refine ⟨64183251369702289772029475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42788834246468193181352983 64183251369702289772029475)
          ·
            refine ⟨96274877054553434658044213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64183251369702289772029475 96274877054553434658044213)
            ·
              refine ⟨9025769723864384499191645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96274877054553434658044213 9025769723864384499191645)
              ·
                refine ⟨3384663646449144187196867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9025769723864384499191645 3384663646449144187196867)
                ·
                  refine ⟨5076995469673716280795301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384663646449144187196867 5076995469673716280795301)
                  ·
                    refine ⟨951936650563821802649119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5076995469673716280795301 951936650563821802649119)
                    ·
                      rfl

theorem cell22_2780835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 4].length) (baseStart_2780835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780835 prefixEnd_2780835 := by exact prefixLift 2780835
  have htrace : WordTrace (prefixWord ++ tailWord_2780835) baseStart_2780835 baseEnd_2780835 := by
    simpa [prefixWord, tailWord_2780835, baseEnd_2780835] using wordTrace_append hprefix tailTrace_2780835
  have hstable : (prefixWord ++ tailWord_2780835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780835).length < 2 ^ (prefixWord ++ tailWord_2780835).sum := by decide
  have hdescent : baseEnd_2780835 < baseStart_2780835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780848 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_2780848 : Nat := 118140960795 + 2780848 * 2 ^ 59
def prefixEnd_2780848 : Nat := 4983230072969 + 3 ^ 40 * 2780848 * 2
def baseEnd_2780848 : Nat := 951941100729494102074079

theorem tailTrace_2780848 : CollatzResearch.WordTrace tailWord_2780848 prefixEnd_2780848 951941100729494102074079 := by
  unfold tailWord_2780848
  simp only [CollatzResearch.WordTrace]
  refine ⟨50712929514735050936159599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67617239352980067914879465 50712929514735050936159599)
  ·
    refine ⟨76069394272102576404239399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50712929514735050936159599 76069394272102576404239399)
    ·
      refine ⟨114104091408153864606359099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76069394272102576404239399 114104091408153864606359099)
      ·
        refine ⟨171156137112230796909538649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114104091408153864606359099 171156137112230796909538649)
        ·
          refine ⟨128367102834173097682153987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171156137112230796909538649 128367102834173097682153987)
          ·
            refine ⟨192550654251259646523230981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128367102834173097682153987 192550654251259646523230981)
            ·
              refine ⟨36103247672111183723105809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192550654251259646523230981 36103247672111183723105809)
              ·
                refine ⟨27077435754083387792329357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36103247672111183723105809 27077435754083387792329357)
                ·
                  refine ⟨10154038407781270422123509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27077435754083387792329357 10154038407781270422123509)
                  ·
                    refine ⟨951941100729494102074079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10154038407781270422123509 951941100729494102074079)
                    ·
                      rfl

theorem cell22_2780848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_2780848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780848 prefixEnd_2780848 := by exact prefixLift 2780848
  have htrace : WordTrace (prefixWord ++ tailWord_2780848) baseStart_2780848 baseEnd_2780848 := by
    simpa [prefixWord, tailWord_2780848, baseEnd_2780848] using wordTrace_append hprefix tailTrace_2780848
  have hstable : (prefixWord ++ tailWord_2780848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780848).length < 2 ^ (prefixWord ++ tailWord_2780848).sum := by decide
  have hdescent : baseEnd_2780848 < baseStart_2780848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780863 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_2780863 : Nat := 118140960795 + 2780863 * 2 ^ 59
def prefixEnd_2780863 : Nat := 4983230072969 + 3 ^ 40 * 2780863 * 2
def baseEnd_2780863 : Nat := 951946235536039062949033

theorem tailTrace_2780863 : CollatzResearch.WordTrace tailWord_2780863 prefixEnd_2780863 951946235536039062949033 := by
  unfold tailWord_2780863
  simp only [CollatzResearch.WordTrace]
  refine ⟨101426406124415759434115243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67617604082943839622743495 101426406124415759434115243)
  ·
    refine ⟨152139609186623639151172865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101426406124415759434115243 152139609186623639151172865)
    ·
      refine ⟨114104706889967729363379649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152139609186623639151172865 114104706889967729363379649)
      ·
        refine ⟨85578530167475797022534737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114104706889967729363379649 85578530167475797022534737)
        ·
          refine ⟨64183897625606847766901053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85578530167475797022534737 64183897625606847766901053)
          ·
            refine ⟨24068961609602567912587895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64183897625606847766901053 24068961609602567912587895)
            ·
              refine ⟨36103442414403851868881843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24068961609602567912587895 36103442414403851868881843)
              ·
                refine ⟨54155163621605777803322765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36103442414403851868881843 54155163621605777803322765)
                ·
                  refine ⟨20308186358102166676246037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54155163621605777803322765 20308186358102166676246037)
                  ·
                    refine ⟨951946235536039062949033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20308186358102166676246037 951946235536039062949033)
                    ·
                      rfl

theorem cell22_2780863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_2780863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780863 prefixEnd_2780863 := by exact prefixLift 2780863
  have htrace : WordTrace (prefixWord ++ tailWord_2780863) baseStart_2780863 baseEnd_2780863 := by
    simpa [prefixWord, tailWord_2780863, baseEnd_2780863] using wordTrace_append hprefix tailTrace_2780863
  have hstable : (prefixWord ++ tailWord_2780863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780863).length < 2 ^ (prefixWord ++ tailWord_2780863).sum := by decide
  have hdescent : baseEnd_2780863 < baseStart_2780863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780882 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2780882 : Nat := 118140960795 + 2780882 * 2 ^ 59
def prefixEnd_2780882 : Nat := 4983230072969 + 3 ^ 40 * 2780882 * 2
def baseEnd_2780882 : Nat := 951952739624329346723975

theorem tailTrace_2780882 : CollatzResearch.WordTrace tailWord_2780882 prefixEnd_2780882 951952739624329346723975 := by
  unfold tailWord_2780882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356774777836731419764225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67618066074231283786037933 25356774777836731419764225)
  ·
    refine ⟨19017581083377548564823169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25356774777836731419764225 19017581083377548564823169)
    ·
      refine ⟨14263185812533161423617377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19017581083377548564823169 14263185812533161423617377)
      ·
        refine ⟨10697389359399871067713033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14263185812533161423617377 10697389359399871067713033)
        ·
          refine ⟨8023042019549903300784775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10697389359399871067713033 8023042019549903300784775)
          ·
            refine ⟨12034563029324854951177163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023042019549903300784775 12034563029324854951177163)
            ·
              refine ⟨18051844543987282426765745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034563029324854951177163 18051844543987282426765745)
              ·
                refine ⟨13538883407990461820074309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18051844543987282426765745 13538883407990461820074309)
                ·
                  refine ⟨2538540638998211591263933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13538883407990461820074309 2538540638998211591263933)
                  ·
                    refine ⟨951952739624329346723975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538540638998211591263933 951952739624329346723975)
                    ·
                      rfl

theorem cell22_2780882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2780882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780882 prefixEnd_2780882 := by exact prefixLift 2780882
  have htrace : WordTrace (prefixWord ++ tailWord_2780882) baseStart_2780882 baseEnd_2780882 := by
    simpa [prefixWord, tailWord_2780882, baseEnd_2780882] using wordTrace_append hprefix tailTrace_2780882
  have hstable : (prefixWord ++ tailWord_2780882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780882).length < 2 ^ (prefixWord ++ tailWord_2780882).sum := by decide
  have hdescent : baseEnd_2780882 < baseStart_2780882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780884 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2780884 : Nat := 118140960795 + 2780884 * 2 ^ 59
def prefixEnd_2780884 : Nat := 4983230072969 + 3 ^ 40 * 2780884 * 2
def baseEnd_2780884 : Nat := 317317808088400669391323

theorem tailTrace_2780884 : CollatzResearch.WordTrace tailWord_2780884 prefixEnd_2780884 317317808088400669391323 := by
  unfold tailWord_2780884
  simp only [CollatzResearch.WordTrace]
  refine ⟨50713586028669840010314853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67618114704893120013753137 50713586028669840010314853)
  ·
    refine ⟨9508797380375595001934035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50713586028669840010314853 9508797380375595001934035)
    ·
      refine ⟨14263196070563392502901053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9508797380375595001934035 14263196070563392502901053)
      ·
        refine ⟨5348698526461272188587895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14263196070563392502901053 5348698526461272188587895)
        ·
          refine ⟨8023047789691908282881843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5348698526461272188587895 8023047789691908282881843)
          ·
            refine ⟨12034571684537862424322765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023047789691908282881843 12034571684537862424322765)
            ·
              refine ⟨4512964381701698409121037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12034571684537862424322765 4512964381701698409121037)
              ·
                refine ⟨1692361643138136903420389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4512964381701698409121037 1692361643138136903420389)
                ·
                  refine ⟨317317808088400669391323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692361643138136903420389 317317808088400669391323)
                  ·
                    rfl

theorem cell22_2780884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2780884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780884 prefixEnd_2780884 := by exact prefixLift 2780884
  have htrace : WordTrace (prefixWord ++ tailWord_2780884) baseStart_2780884 baseEnd_2780884 := by
    simpa [prefixWord, tailWord_2780884, baseEnd_2780884] using wordTrace_append hprefix tailTrace_2780884
  have hstable : (prefixWord ++ tailWord_2780884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780884).length < 2 ^ (prefixWord ++ tailWord_2780884).sum := by decide
  have hdescent : baseEnd_2780884 < baseStart_2780884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780897 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2780897 : Nat := 118140960795 + 2780897 * 2 ^ 59
def prefixEnd_2780897 : Nat := 4983230072969 + 3 ^ 40 * 2780897 * 2
def baseEnd_2780897 : Nat := 951957874430874307598929

theorem tailTrace_2780897 : CollatzResearch.WordTrace tailWord_2780897 prefixEnd_2780897 951957874430874307598929 := by
  unfold tailWord_2780897
  simp only [CollatzResearch.WordTrace]
  refine ⟨101427646206292583240852945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67618430804195055493901963 101427646206292583240852945)
  ·
    refine ⟨76070734654719437430639709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101427646206292583240852945 76070734654719437430639709)
    ·
      refine ⟨28526525495519789036489891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76070734654719437430639709 28526525495519789036489891)
      ·
        refine ⟨42789788243279683554734837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28526525495519789036489891 42789788243279683554734837)
        ·
          refine ⟨4011542647807470333256391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42789788243279683554734837 4011542647807470333256391)
          ·
            refine ⟨6017313971711205499884587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011542647807470333256391 6017313971711205499884587)
            ·
              refine ⟨9025970957566808249826881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017313971711205499884587 9025970957566808249826881)
              ·
                refine ⟨6769478218175106187370161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9025970957566808249826881 6769478218175106187370161)
                ·
                  refine ⟨5077108663631329640527621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6769478218175106187370161 5077108663631329640527621)
                  ·
                    refine ⟨951957874430874307598929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077108663631329640527621 951957874430874307598929)
                    ·
                      rfl

theorem cell22_2780897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2780897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780897 prefixEnd_2780897 := by exact prefixLift 2780897
  have htrace : WordTrace (prefixWord ++ tailWord_2780897) baseStart_2780897 baseEnd_2780897 := by
    simpa [prefixWord, tailWord_2780897, baseEnd_2780897] using wordTrace_append hprefix tailTrace_2780897
  have hstable : (prefixWord ++ tailWord_2780897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780897).length < 2 ^ (prefixWord ++ tailWord_2780897).sum := by decide
  have hdescent : baseEnd_2780897 < baseStart_2780897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780923 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 9]
def baseStart_2780923 : Nat := 118140960795 + 2780923 * 2 ^ 59
def prefixEnd_2780923 : Nat := 4983230072969 + 3 ^ 40 * 2780923 * 2
def baseEnd_2780923 : Nat := 317322258254072968816283

theorem tailTrace_2780923 : CollatzResearch.WordTrace tailWord_2780923 prefixEnd_2780923 317322258254072968816283 := by
  unfold tailWord_2780923
  simp only [CollatzResearch.WordTrace]
  refine ⟨101428594504198389681299423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67619063002798926454199615 101428594504198389681299423)
  ·
    refine ⟨152142891756297584521949135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101428594504198389681299423 152142891756297584521949135)
    ·
      refine ⟨228214337634446376782923703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152142891756297584521949135 228214337634446376782923703)
      ·
        refine ⟨342321506451669565174385555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228214337634446376782923703 342321506451669565174385555)
        ·
          refine ⟨513482259677504347761578333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342321506451669565174385555 513482259677504347761578333)
          ·
            refine ⟨192555847379064130410591875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513482259677504347761578333 192555847379064130410591875)
            ·
              refine ⟨288833771068596195615887813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192555847379064130410591875 288833771068596195615887813)
              ·
                refine ⟨54156332075361786677978965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288833771068596195615887813 54156332075361786677978965)
                ·
                  refine ⟨317322258254072968816283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54156332075361786677978965 317322258254072968816283)
                  ·
                    rfl

theorem cell22_2780923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_2780923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780923 prefixEnd_2780923 := by exact prefixLift 2780923
  have htrace : WordTrace (prefixWord ++ tailWord_2780923) baseStart_2780923 baseEnd_2780923 := by
    simpa [prefixWord, tailWord_2780923, baseEnd_2780923] using wordTrace_append hprefix tailTrace_2780923
  have hstable : (prefixWord ++ tailWord_2780923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780923).length < 2 ^ (prefixWord ++ tailWord_2780923).sum := by decide
  have hdescent : baseEnd_2780923 < baseStart_2780923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780961 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2780961 : Nat := 118140960795 + 2780961 * 2 ^ 59
def prefixEnd_2780961 : Nat := 4983230072969 + 3 ^ 40 * 2780961 * 2
def baseEnd_2780961 : Nat := 951979782938799473998733

theorem tailTrace_2780961 : CollatzResearch.WordTrace tailWord_2780961 prefixEnd_2780961 951979782938799473998733 := by
  unfold tailWord_2780961
  simp only [CollatzResearch.WordTrace]
  refine ⟨101429980478060722171182737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67619986985373814780788491 101429980478060722171182737)
  ·
    refine ⟨76072485358545541628387053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101429980478060722171182737 76072485358545541628387053)
    ·
      refine ⟨28527182009454578110645145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76072485358545541628387053 28527182009454578110645145)
      ·
        refine ⟨21395386507090933582983859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28527182009454578110645145 21395386507090933582983859)
        ·
          refine ⟨32093079760636400374475789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21395386507090933582983859 32093079760636400374475789)
          ·
            refine ⟨12034904910238650140428421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32093079760636400374475789 12034904910238650140428421)
            ·
              refine ⟨2256544670669746901330329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12034904910238650140428421 2256544670669746901330329)
              ·
                refine ⟨1692408503002310175997747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256544670669746901330329 1692408503002310175997747)
                ·
                  refine ⟨2538612754503465263996621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692408503002310175997747 2538612754503465263996621)
                  ·
                    refine ⟨951979782938799473998733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538612754503465263996621 951979782938799473998733)
                    ·
                      rfl

theorem cell22_2780961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2780961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2780961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2780961 prefixEnd_2780961 := by exact prefixLift 2780961
  have htrace : WordTrace (prefixWord ++ tailWord_2780961) baseStart_2780961 baseEnd_2780961 := by
    simpa [prefixWord, tailWord_2780961, baseEnd_2780961] using wordTrace_append hprefix tailTrace_2780961
  have hstable : (prefixWord ++ tailWord_2780961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780961).length < 2 ^ (prefixWord ++ tailWord_2780961).sum := by decide
  have hdescent : baseEnd_2780961 < baseStart_2780961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781004 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_2781004 : Nat := 118140960795 + 2781004 * 2 ^ 59
def prefixEnd_2781004 : Nat := 4983230072969 + 3 ^ 40 * 2781004 * 2
def baseEnd_2781004 : Nat := 951994502717561695173601

theorem tailTrace_2781004 : CollatzResearch.WordTrace tailWord_2781004 prefixEnd_2781004 951994502717561695173601 := by
  unfold tailWord_2781004
  simp only [CollatzResearch.WordTrace]
  refine ⟨50715774408452470257499033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67621032544603293676665377 50715774408452470257499033)
  ·
    refine ⟨38036830806339352693124275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50715774408452470257499033 38036830806339352693124275)
    ·
      refine ⟨57055246209509029039686413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38036830806339352693124275 57055246209509029039686413)
      ·
        refine ⟨21395717328565885889882405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57055246209509029039686413 21395717328565885889882405)
        ·
          refine ⟨4011696999106103604352951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21395717328565885889882405 4011696999106103604352951)
          ·
            refine ⟨6017545498659155406529427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011696999106103604352951 6017545498659155406529427)
            ·
              refine ⟨9026318247988733109794141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017545498659155406529427 9026318247988733109794141)
              ·
                refine ⟨3384869342995774916172803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9026318247988733109794141 3384869342995774916172803)
                ·
                  refine ⟨5077304014493662374259205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384869342995774916172803 5077304014493662374259205)
                  ·
                    refine ⟨951994502717561695173601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077304014493662374259205 951994502717561695173601)
                    ·
                      rfl

theorem cell22_2781004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_2781004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781004 prefixEnd_2781004 := by exact prefixLift 2781004
  have htrace : WordTrace (prefixWord ++ tailWord_2781004) baseStart_2781004 baseEnd_2781004 := by
    simpa [prefixWord, tailWord_2781004, baseEnd_2781004] using wordTrace_append hprefix tailTrace_2781004
  have hstable : (prefixWord ++ tailWord_2781004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781004).length < 2 ^ (prefixWord ++ tailWord_2781004).sum := by decide
  have hdescent : baseEnd_2781004 < baseStart_2781004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781017 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_2781017 : Nat := 118140960795 + 2781017 * 2 ^ 59
def prefixEnd_2781017 : Nat := 4983230072969 + 3 ^ 40 * 2781017 * 2
def baseEnd_2781017 : Nat := 951998952883233994598561

theorem tailTrace_2781017 : CollatzResearch.WordTrace tailWord_2781017 prefixEnd_2781017 951998952883233994598561 := by
  unfold tailWord_2781017
  simp only [CollatzResearch.WordTrace]
  refine ⟨101432022965857843735221305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67621348643905229156814203 101432022965857843735221305)
  ·
    refine ⟨76074017224393382801415979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101432022965857843735221305 76074017224393382801415979)
    ·
      refine ⟨114111025836590074202123969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76074017224393382801415979 114111025836590074202123969)
      ·
        refine ⟨85583269377442555651592977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114111025836590074202123969 85583269377442555651592977)
        ·
          refine ⟨64187452033081916738694733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85583269377442555651592977 64187452033081916738694733)
          ·
            refine ⟨24070294512405718777010525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64187452033081916738694733 24070294512405718777010525)
            ·
              refine ⟨9026360442152144541378947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24070294512405718777010525 9026360442152144541378947)
              ·
                refine ⟨13539540663228216812068421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9026360442152144541378947 13539540663228216812068421)
                ·
                  refine ⟨2538663874355290652262829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13539540663228216812068421 2538663874355290652262829)
                  ·
                    refine ⟨951998952883233994598561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538663874355290652262829 951998952883233994598561)
                    ·
                      rfl

theorem cell22_2781017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_2781017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781017 prefixEnd_2781017 := by exact prefixLift 2781017
  have htrace : WordTrace (prefixWord ++ tailWord_2781017) baseStart_2781017 baseEnd_2781017 := by
    simpa [prefixWord, tailWord_2781017, baseEnd_2781017] using wordTrace_append hprefix tailTrace_2781017
  have hstable : (prefixWord ++ tailWord_2781017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781017).length < 2 ^ (prefixWord ++ tailWord_2781017).sum := by decide
  have hdescent : baseEnd_2781017 < baseStart_2781017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781064 : List Nat := [2, 1, 3, 3, 4, 1, 8]
def baseStart_2781064 : Nat := 118140960795 + 2781064 * 2 ^ 59
def prefixEnd_2781064 : Nat := 4983230072969 + 3 ^ 40 * 2781064 * 2
def baseEnd_2781064 : Nat := 35259816368286723654571

theorem tailTrace_2781064 : CollatzResearch.WordTrace tailWord_2781064 prefixEnd_2781064 35259816368286723654571 := by
  unfold tailWord_2781064
  simp only [CollatzResearch.WordTrace]
  refine ⟨50716868598343785381091123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67622491464458380508121497 50716868598343785381091123)
  ·
    refine ⟨76075302897515678071636685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50716868598343785381091123 76075302897515678071636685)
    ·
      refine ⟨28528238586568379276863757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76075302897515678071636685 28528238586568379276863757)
      ·
        refine ⟨10698089469963142228823909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28528238586568379276863757 10698089469963142228823909)
        ·
          refine ⟨2005891775618089167904483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10698089469963142228823909 2005891775618089167904483)
          ·
            refine ⟨3008837663427133751856725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005891775618089167904483 3008837663427133751856725)
            ·
              refine ⟨35259816368286723654571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3008837663427133751856725 35259816368286723654571)
              ·
                rfl

theorem cell22_2781064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 8].length) (baseStart_2781064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781064 prefixEnd_2781064 := by exact prefixLift 2781064
  have htrace : WordTrace (prefixWord ++ tailWord_2781064) baseStart_2781064 baseEnd_2781064 := by
    simpa [prefixWord, tailWord_2781064, baseEnd_2781064] using wordTrace_append hprefix tailTrace_2781064
  have hstable : (prefixWord ++ tailWord_2781064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781064).length < 2 ^ (prefixWord ++ tailWord_2781064).sum := by decide
  have hdescent : baseEnd_2781064 < baseStart_2781064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781079 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 3, 3]
def baseStart_2781079 : Nat := 118140960795 + 2781079 * 2 ^ 59
def prefixEnd_2781079 : Nat := 4983230072969 + 3 ^ 40 * 2781079 * 2
def baseEnd_2781079 : Nat := 952020176750286499548371

theorem tailTrace_2781079 : CollatzResearch.WordTrace tailWord_2781079 prefixEnd_2781079 952020176750286499548371 := by
  unfold tailWord_2781079
  simp only [CollatzResearch.WordTrace]
  refine ⟨101434284291633228323978291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67622856194422152215985527 101434284291633228323978291)
  ·
    refine ⟨152151426437449842485967437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101434284291633228323978291 152151426437449842485967437)
    ·
      refine ⟨57056784914043690932237789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152151426437449842485967437 57056784914043690932237789)
      ·
        refine ⟨21396294342766384099589171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57056784914043690932237789 21396294342766384099589171)
        ·
          refine ⟨32094441514149576149383757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21396294342766384099589171 32094441514149576149383757)
          ·
            refine ⟨12035415567806091056018909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32094441514149576149383757 12035415567806091056018909)
            ·
              refine ⟨4513280837927284146007091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12035415567806091056018909 4513280837927284146007091)
              ·
                refine ⟨6769921256890926219010637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513280837927284146007091 6769921256890926219010637)
                ·
                  refine ⟨2538720471334097332128989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6769921256890926219010637 2538720471334097332128989)
                  ·
                    refine ⟨952020176750286499548371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538720471334097332128989 952020176750286499548371)
                    ·
                      rfl

theorem cell22_2781079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_2781079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781079 prefixEnd_2781079 := by exact prefixLift 2781079
  have htrace : WordTrace (prefixWord ++ tailWord_2781079) baseStart_2781079 baseEnd_2781079 := by
    simpa [prefixWord, tailWord_2781079, baseEnd_2781079] using wordTrace_append hprefix tailTrace_2781079
  have hstable : (prefixWord ++ tailWord_2781079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781079).length < 2 ^ (prefixWord ++ tailWord_2781079).sum := by decide
  have hdescent : baseEnd_2781079 < baseStart_2781079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781167 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 1, 6]
def baseStart_2781167 : Nat := 118140960795 + 2781167 * 2 ^ 59
def prefixEnd_2781167 : Nat := 4983230072969 + 3 ^ 40 * 2781167 * 2
def baseEnd_2781167 : Nat := 952050300948683603348101

theorem tailTrace_2781167 : CollatzResearch.WordTrace tailWord_2781167 prefixEnd_2781167 952050300948683603348101 := by
  unfold tailWord_2781167
  simp only [CollatzResearch.WordTrace]
  refine ⟨101437493915314419353181755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67624995943542946235454503 101437493915314419353181755)
  ·
    refine ⟨152156240872971629029772633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101437493915314419353181755 152156240872971629029772633)
    ·
      refine ⟨114117180654728721772329475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152156240872971629029772633 114117180654728721772329475)
      ·
        refine ⟨171175770982093082658494213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114117180654728721772329475 171175770982093082658494213)
        ·
          refine ⟨32095457059142452998467665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171175770982093082658494213 32095457059142452998467665)
          ·
            refine ⟨24071592794356839748850749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32095457059142452998467665 24071592794356839748850749)
            ·
              refine ⟨9026847297883814905819031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24071592794356839748850749 9026847297883814905819031)
              ·
                refine ⟨13540270946825722358728547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9026847297883814905819031 13540270946825722358728547)
                ·
                  refine ⟨20310406420238583538092821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13540270946825722358728547 20310406420238583538092821)
                  ·
                    refine ⟨952050300948683603348101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20310406420238583538092821 952050300948683603348101)
                    ·
                      rfl

theorem cell22_2781167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_2781167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781167 prefixEnd_2781167 := by exact prefixLift 2781167
  have htrace : WordTrace (prefixWord ++ tailWord_2781167) baseStart_2781167 baseEnd_2781167 := by
    simpa [prefixWord, tailWord_2781167, baseEnd_2781167] using wordTrace_append hprefix tailTrace_2781167
  have hstable : (prefixWord ++ tailWord_2781167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781167).length < 2 ^ (prefixWord ++ tailWord_2781167).sum := by decide
  have hdescent : baseEnd_2781167 < baseStart_2781167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781231 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 1, 3]
def baseStart_2781231 : Nat := 118140960795 + 2781231 * 2 ^ 59
def prefixEnd_2781231 : Nat := 4983230072969 + 3 ^ 40 * 2781231 * 2
def baseEnd_2781231 : Nat := 952072209456608769747905

theorem tailTrace_2781231 : CollatzResearch.WordTrace tailWord_2781231 prefixEnd_2781231 952072209456608769747905 := by
  unfold tailWord_2781231
  simp only [CollatzResearch.WordTrace]
  refine ⟨101439828187082558283511547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67626552124721705522341031 101439828187082558283511547)
  ·
    refine ⟨152159742280623837425267321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101439828187082558283511547 152159742280623837425267321)
    ·
      refine ⟨114119806710467878068950491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152159742280623837425267321 114119806710467878068950491)
      ·
        refine ⟨171179710065701817103425737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114119806710467878068950491 171179710065701817103425737)
        ·
          refine ⟨128384782549276362827569303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171179710065701817103425737 128384782549276362827569303)
          ·
            refine ⟨192577173823914544241353955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128384782549276362827569303 192577173823914544241353955)
            ·
              refine ⟨288865760735871816362030933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192577173823914544241353955 288865760735871816362030933)
              ·
                refine ⟨1692572816811748923996275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 288865760735871816362030933 1692572816811748923996275)
                ·
                  refine ⟨2538859225217623385994413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692572816811748923996275 2538859225217623385994413)
                  ·
                    refine ⟨952072209456608769747905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538859225217623385994413 952072209456608769747905)
                    ·
                      rfl

theorem cell22_2781231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_2781231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781231 prefixEnd_2781231 := by exact prefixLift 2781231
  have htrace : WordTrace (prefixWord ++ tailWord_2781231) baseStart_2781231 baseEnd_2781231 := by
    simpa [prefixWord, tailWord_2781231, baseEnd_2781231] using wordTrace_append hprefix tailTrace_2781231
  have hstable : (prefixWord ++ tailWord_2781231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781231).length < 2 ^ (prefixWord ++ tailWord_2781231).sum := by decide
  have hdescent : baseEnd_2781231 < baseStart_2781231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781244 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_2781244 : Nat := 118140960795 + 2781244 * 2 ^ 59
def prefixEnd_2781244 : Nat := 4983230072969 + 3 ^ 40 * 2781244 * 2
def baseEnd_2781244 : Nat := 317358886540760356390955

theorem tailTrace_2781244 : CollatzResearch.WordTrace tailWord_2781244 prefixEnd_2781244 317358886540760356390955 := by
  unfold tailWord_2781244
  simp only [CollatzResearch.WordTrace]
  refine ⟨50720151168017730751867393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67626868224023641002489857 50720151168017730751867393)
  ·
    refine ⟨38040113376013298063900545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50720151168017730751867393 38040113376013298063900545)
    ·
      refine ⟨28530085032009973547925409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38040113376013298063900545 28530085032009973547925409)
      ·
        refine ⟨21397563774007480160944057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28530085032009973547925409 21397563774007480160944057)
        ·
          refine ⟨16048172830505610120708043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21397563774007480160944057 16048172830505610120708043)
          ·
            refine ⟨24072259245758415181062065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16048172830505610120708043 24072259245758415181062065)
            ·
              refine ⟨18054194434318811385796549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24072259245758415181062065 18054194434318811385796549)
              ·
                refine ⟨3385161456434777134836853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18054194434318811385796549 3385161456434777134836853)
                ·
                  refine ⟨317358886540760356390955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3385161456434777134836853 317358886540760356390955)
                  ·
                    rfl

theorem cell22_2781244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_2781244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781244 prefixEnd_2781244 := by exact prefixLift 2781244
  have htrace : WordTrace (prefixWord ++ tailWord_2781244) baseStart_2781244 baseEnd_2781244 := by
    simpa [prefixWord, tailWord_2781244, baseEnd_2781244] using wordTrace_append hprefix tailTrace_2781244
  have hstable : (prefixWord ++ tailWord_2781244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781244).length < 2 ^ (prefixWord ++ tailWord_2781244).sum := by decide
  have hdescent : baseEnd_2781244 < baseStart_2781244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781261 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2781261 : Nat := 118140960795 + 2781261 * 2 ^ 59
def prefixEnd_2781261 : Nat := 4983230072969 + 3 ^ 40 * 2781261 * 2
def baseEnd_2781261 : Nat := 317360826356566230499271

theorem tailTrace_2781261 : CollatzResearch.WordTrace tailWord_2781261 prefixEnd_2781261 317360826356566230499271 := by
  unfold tailWord_2781261
  simp only [CollatzResearch.WordTrace]
  refine ⟨101440922376973873407103637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67627281584649248938069091 101440922376973873407103637)
  ·
    refine ⟨4755043236420650315957983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101440922376973873407103637 4755043236420650315957983)
    ·
      refine ⟨7132564854630975473936975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4755043236420650315957983 7132564854630975473936975)
      ·
        refine ⟨10698847281946463210905463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7132564854630975473936975 10698847281946463210905463)
        ·
          refine ⟨16048270922919694816358195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10698847281946463210905463 16048270922919694816358195)
          ·
            refine ⟨24072406384379542224537293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16048270922919694816358195 24072406384379542224537293)
            ·
              refine ⟨9027152394142328334201485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24072406384379542224537293 9027152394142328334201485)
              ·
                refine ⟨3385182147803373125325557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9027152394142328334201485 3385182147803373125325557)
                ·
                  refine ⟨317360826356566230499271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3385182147803373125325557 317360826356566230499271)
                  ·
                    rfl

theorem cell22_2781261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2781261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781261 prefixEnd_2781261 := by exact prefixLift 2781261
  have htrace : WordTrace (prefixWord ++ tailWord_2781261) baseStart_2781261 baseEnd_2781261 := by
    simpa [prefixWord, tailWord_2781261, baseEnd_2781261] using wordTrace_append hprefix tailTrace_2781261
  have hstable : (prefixWord ++ tailWord_2781261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781261).length < 2 ^ (prefixWord ++ tailWord_2781261).sum := by decide
  have hdescent : baseEnd_2781261 < baseStart_2781261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781274 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_2781274 : Nat := 118140960795 + 2781274 * 2 ^ 59
def prefixEnd_2781274 : Nat := 4983230072969 + 3 ^ 40 * 2781274 * 2
def baseEnd_2781274 : Nat := 952086929235370990922773

theorem tailTrace_2781274 : CollatzResearch.WordTrace tailWord_2781274 prefixEnd_2781274 952086929235370990922773 := by
  unfold tailWord_2781274
  simp only [CollatzResearch.WordTrace]
  refine ⟨25360349131481694156831719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67627597683951184418217917 25360349131481694156831719)
  ·
    refine ⟨38040523697222541235247579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25360349131481694156831719 38040523697222541235247579)
    ·
      refine ⟨57060785545833811852871369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38040523697222541235247579 57060785545833811852871369)
      ·
        refine ⟨42795589159375358889653527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57060785545833811852871369 42795589159375358889653527)
        ·
          refine ⟨64193383739063038334480291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42795589159375358889653527 64193383739063038334480291)
          ·
            refine ⟨96290075608594557501720437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64193383739063038334480291 96290075608594557501720437)
            ·
              refine ⟨9027194588305739765786291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96290075608594557501720437 9027194588305739765786291)
              ·
                refine ⟨13540791882458609648679437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9027194588305739765786291 13540791882458609648679437)
                ·
                  refine ⟨5077796955921978618254789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13540791882458609648679437 5077796955921978618254789)
                  ·
                    refine ⟨952086929235370990922773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077796955921978618254789 952086929235370990922773)
                    ·
                      rfl

theorem cell22_2781274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_2781274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781274 prefixEnd_2781274 := by exact prefixLift 2781274
  have htrace : WordTrace (prefixWord ++ tailWord_2781274) baseStart_2781274 baseEnd_2781274 := by
    simpa [prefixWord, tailWord_2781274, baseEnd_2781274] using wordTrace_append hprefix tailTrace_2781274
  have hstable : (prefixWord ++ tailWord_2781274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781274).length < 2 ^ (prefixWord ++ tailWord_2781274).sum := by decide
  have hdescent : baseEnd_2781274 < baseStart_2781274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781319 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2781319 : Nat := 118140960795 + 2781319 * 2 ^ 59
def prefixEnd_2781319 : Nat := 4983230072969 + 3 ^ 40 * 2781319 * 2
def baseEnd_2781319 : Nat := 952102333655005873547635

theorem tailTrace_2781319 : CollatzResearch.WordTrace tailWord_2781319 prefixEnd_2781319 952102333655005873547635 := by
  unfold tailWord_2781319
  simp only [CollatzResearch.WordTrace]
  refine ⟨101443037810763749312715011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67628691873842499541810007 101443037810763749312715011)
  ·
    refine ⟨152164556716145623969072517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101443037810763749312715011 152164556716145623969072517)
    ·
      refine ⟨28530854384277304494201097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152164556716145623969072517 28530854384277304494201097)
      ·
        refine ⟨21398140788207978370650823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28530854384277304494201097 21398140788207978370650823)
        ·
          refine ⟨32097211182311967555976235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21398140788207978370650823 32097211182311967555976235)
          ·
            refine ⟨48145816773467951333964353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32097211182311967555976235 48145816773467951333964353)
            ·
              refine ⟨36109362580100963500473265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48145816773467951333964353 36109362580100963500473265)
              ·
                refine ⟨27082021935075722625354949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36109362580100963500473265 27082021935075722625354949)
                ·
                  refine ⟨5077879112826697992254053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27082021935075722625354949 5077879112826697992254053)
                  ·
                    refine ⟨952102333655005873547635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077879112826697992254053 952102333655005873547635)
                    ·
                      rfl

theorem cell22_2781319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2781319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781319 prefixEnd_2781319 := by exact prefixLift 2781319
  have htrace : WordTrace (prefixWord ++ tailWord_2781319) baseStart_2781319 baseEnd_2781319 := by
    simpa [prefixWord, tailWord_2781319, baseEnd_2781319] using wordTrace_append hprefix tailTrace_2781319
  have hstable : (prefixWord ++ tailWord_2781319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781319).length < 2 ^ (prefixWord ++ tailWord_2781319).sum := by decide
  have hdescent : baseEnd_2781319 < baseStart_2781319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781321 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 2, 3]
def baseStart_2781321 : Nat := 118140960795 + 2781321 * 2 ^ 59
def prefixEnd_2781321 : Nat := 4983230072969 + 3 ^ 40 * 2781321 * 2
def baseEnd_2781321 : Nat := 952103018295878534997629

theorem tailTrace_2781321 : CollatzResearch.WordTrace tailWord_2781321 prefixEnd_2781321 952103018295878534997629 := by
  unfold tailWord_2781321
  simp only [CollatzResearch.WordTrace]
  refine ⟨101443110756756503654287817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67628740504504335769525211 101443110756756503654287817)
  ·
    refine ⟨76082333067567377740715863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101443110756756503654287817 76082333067567377740715863)
    ·
      refine ⟨114123499601351066611073795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76082333067567377740715863 114123499601351066611073795)
      ·
        refine ⟨171185249402026599916610693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114123499601351066611073795 171185249402026599916610693)
        ·
          refine ⟨32097234262879987484364505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171185249402026599916610693 32097234262879987484364505)
          ·
            refine ⟨24072925697159990613273379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32097234262879987484364505 24072925697159990613273379)
            ·
              refine ⟨36109388545739985919910069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24072925697159990613273379 36109388545739985919910069)
              ·
                refine ⟨3385255176163123679991569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36109388545739985919910069 3385255176163123679991569)
                ·
                  refine ⟨2538941382122342759993677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385255176163123679991569 2538941382122342759993677)
                  ·
                    refine ⟨952103018295878534997629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538941382122342759993677 952103018295878534997629)
                    ·
                      rfl

theorem cell22_2781321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_2781321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781321 prefixEnd_2781321 := by exact prefixLift 2781321
  have htrace : WordTrace (prefixWord ++ tailWord_2781321) baseStart_2781321 baseEnd_2781321 := by
    simpa [prefixWord, tailWord_2781321, baseEnd_2781321] using wordTrace_append hprefix tailTrace_2781321
  have hstable : (prefixWord ++ tailWord_2781321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781321).length < 2 ^ (prefixWord ++ tailWord_2781321).sum := by decide
  have hdescent : baseEnd_2781321 < baseStart_2781321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781336 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_2781336 : Nat := 118140960795 + 2781336 * 2 ^ 59
def prefixEnd_2781336 : Nat := 4983230072969 + 3 ^ 40 * 2781336 * 2
def baseEnd_2781336 : Nat := 952108153102423495872583

theorem tailTrace_2781336 : CollatzResearch.WordTrace tailWord_2781336 prefixEnd_2781336 952108153102423495872583 := by
  unfold tailWord_2781336
  simp only [CollatzResearch.WordTrace]
  refine ⟨50721828925851080608041931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67629105234468107477389241 50721828925851080608041931)
  ·
    refine ⟨76082743388776620912062897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50721828925851080608041931 76082743388776620912062897)
    ·
      refine ⟨57062057541582465684047173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76082743388776620912062897 57062057541582465684047173)
      ·
        refine ⟨10699135789046712315758845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57062057541582465684047173 10699135789046712315758845)
        ·
          refine ⟨4012175920892517118409567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10699135789046712315758845 4012175920892517118409567)
          ·
            refine ⟨6018263881338775677614351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012175920892517118409567 6018263881338775677614351)
            ·
              refine ⟨9027395822008163516421527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018263881338775677614351 9027395822008163516421527)
              ·
                refine ⟨13541093733012245274632291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9027395822008163516421527 13541093733012245274632291)
                ·
                  refine ⟨20311640599518367911948437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13541093733012245274632291 20311640599518367911948437)
                  ·
                    refine ⟨952108153102423495872583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20311640599518367911948437 952108153102423495872583)
                    ·
                      rfl

theorem cell22_2781336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_2781336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781336 prefixEnd_2781336 := by exact prefixLift 2781336
  have htrace : WordTrace (prefixWord ++ tailWord_2781336) baseStart_2781336 baseEnd_2781336 := by
    simpa [prefixWord, tailWord_2781336, baseEnd_2781336] using wordTrace_append hprefix tailTrace_2781336
  have hstable : (prefixWord ++ tailWord_2781336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781336).length < 2 ^ (prefixWord ++ tailWord_2781336).sum := by decide
  have hdescent : baseEnd_2781336 < baseStart_2781336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781342 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2781342 : Nat := 118140960795 + 2781342 * 2 ^ 59
def prefixEnd_2781342 : Nat := 4983230072969 + 3 ^ 40 * 2781342 * 2
def baseEnd_2781342 : Nat := 952110207025041480222565

theorem tailTrace_2781342 : CollatzResearch.WordTrace tailWord_2781342 prefixEnd_2781342 952110207025041480222565 := by
  unfold tailWord_2781342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680484586210053030100285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67629251126453616160534853 12680484586210053030100285)
  ·
    refine ⟨4755181719828769886287607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12680484586210053030100285 4755181719828769886287607)
    ·
      refine ⟨7132772579743154829431411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4755181719828769886287607 7132772579743154829431411)
      ·
        refine ⟨10699158869614732244147117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7132772579743154829431411 10699158869614732244147117)
        ·
          refine ⟨4012184576105524591555169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10699158869614732244147117 4012184576105524591555169)
          ·
            refine ⟨3009138432079143443666377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012184576105524591555169 3009138432079143443666377)
            ·
              refine ⟨2256853824059357582749783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009138432079143443666377 2256853824059357582749783)
              ·
                refine ⟨3385280736089036374124675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256853824059357582749783 3385280736089036374124675)
                ·
                  refine ⟨5077921104133554561187013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385280736089036374124675 5077921104133554561187013)
                  ·
                    refine ⟨952110207025041480222565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5077921104133554561187013 952110207025041480222565)
                    ·
                      rfl

theorem cell22_2781342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2781342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781342 prefixEnd_2781342 := by exact prefixLift 2781342
  have htrace : WordTrace (prefixWord ++ tailWord_2781342) baseStart_2781342 baseEnd_2781342 := by
    simpa [prefixWord, tailWord_2781342, baseEnd_2781342] using wordTrace_append hprefix tailTrace_2781342
  have hstable : (prefixWord ++ tailWord_2781342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781342).length < 2 ^ (prefixWord ++ tailWord_2781342).sum := by decide
  have hdescent : baseEnd_2781342 < baseStart_2781342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781351 : List Nat := [1, 1, 6, 2, 2, 1, 9]
def baseStart_2781351 : Nat := 118140960795 + 2781351 * 2 ^ 59
def prefixEnd_2781351 : Nat := 4983230072969 + 3 ^ 40 * 2781351 * 2
def baseEnd_2781351 : Nat := 35263455107739572472131

theorem tailTrace_2781351 : CollatzResearch.WordTrace tailWord_2781351 prefixEnd_2781351 35263455107739572472131 := by
  unfold tailWord_2781351
  simp only [CollatzResearch.WordTrace]
  refine ⟨101444204946647818777879907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67629469964431879185253271 101444204946647818777879907)
  ·
    refine ⟨152166307419971728166819861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101444204946647818777879907 152166307419971728166819861)
    ·
      refine ⟨7132795660311174757819681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152166307419971728166819861 7132795660311174757819681)
      ·
        refine ⟨5349596745233381068364761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7132795660311174757819681 5349596745233381068364761)
        ·
          refine ⟨4012197558925035801273571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349596745233381068364761 4012197558925035801273571)
          ·
            refine ⟨6018296338387553701910357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012197558925035801273571 6018296338387553701910357)
            ·
              refine ⟨35263455107739572472131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6018296338387553701910357 35263455107739572472131)
              ·
                rfl

theorem cell22_2781351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 9].length) (baseStart_2781351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781351 prefixEnd_2781351 := by exact prefixLift 2781351
  have htrace : WordTrace (prefixWord ++ tailWord_2781351) baseStart_2781351 baseEnd_2781351 := by
    simpa [prefixWord, tailWord_2781351, baseEnd_2781351] using wordTrace_append hprefix tailTrace_2781351
  have hstable : (prefixWord ++ tailWord_2781351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781351).length < 2 ^ (prefixWord ++ tailWord_2781351).sum := by decide
  have hdescent : baseEnd_2781351 < baseStart_2781351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781400 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 1, 3]
def baseStart_2781400 : Nat := 118140960795 + 2781400 * 2 ^ 59
def prefixEnd_2781400 : Nat := 4983230072969 + 3 ^ 40 * 2781400 * 2
def baseEnd_2781400 : Nat := 952130061610348662272387

theorem tailTrace_2781400 : CollatzResearch.WordTrace tailWord_2781400 prefixEnd_2781400 952130061610348662272387 := by
  unfold tailWord_2781400
  simp only [CollatzResearch.WordTrace]
  refine ⟨50722996061735150073206827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67630661415646866764275769 50722996061735150073206827)
  ·
    refine ⟨76084494092602725109810241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50722996061735150073206827 76084494092602725109810241)
    ·
      refine ⟨57063370569452043832357681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76084494092602725109810241 57063370569452043832357681)
      ·
        refine ⟨42797527927089032874268261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57063370569452043832357681 42797527927089032874268261)
        ·
          refine ⟨8024536486329193663925299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42797527927089032874268261 8024536486329193663925299)
          ·
            refine ⟨12036804729493790495887949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024536486329193663925299 12036804729493790495887949)
            ·
              refine ⟨4513801773560171435957981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12036804729493790495887949 4513801773560171435957981)
              ·
                refine ⟨1692675665085064288484243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4513801773560171435957981 1692675665085064288484243)
                ·
                  refine ⟨2539013497627596432726365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692675665085064288484243 2539013497627596432726365)
                  ·
                    refine ⟨952130061610348662272387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539013497627596432726365 952130061610348662272387)
                    ·
                      rfl

theorem cell22_2781400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_2781400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781400 prefixEnd_2781400 := by exact prefixLift 2781400
  have htrace : WordTrace (prefixWord ++ tailWord_2781400) baseStart_2781400 baseEnd_2781400 := by
    simpa [prefixWord, tailWord_2781400, baseEnd_2781400] using wordTrace_append hprefix tailTrace_2781400
  have hstable : (prefixWord ++ tailWord_2781400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781400).length < 2 ^ (prefixWord ++ tailWord_2781400).sum := by decide
  have hdescent : baseEnd_2781400 < baseStart_2781400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781473 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_2781473 : Nat := 118140960795 + 2781473 * 2 ^ 59
def prefixEnd_2781473 : Nat := 4983230072969 + 3 ^ 40 * 2781473 * 2
def baseEnd_2781473 : Nat := 952155051002200805197163

theorem tailTrace_2781473 : CollatzResearch.WordTrace tailWord_2781473 prefixEnd_2781473 952155051002200805197163 := by
  unfold tailWord_2781473
  simp only [CollatzResearch.WordTrace]
  refine ⟨101448654652205833613821073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67632436434803889075880715 101448654652205833613821073)
  ·
    refine ⟨76086490989154375210365805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101448654652205833613821073 76086490989154375210365805)
    ·
      refine ⟨28532434120932890703887177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76086490989154375210365805 28532434120932890703887177)
      ·
        refine ⟨21399325590699668027915383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28532434120932890703887177 21399325590699668027915383)
        ·
          refine ⟨32098988386049502041873075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21399325590699668027915383 32098988386049502041873075)
          ·
            refine ⟨48148482579074253062809613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32098988386049502041873075 48148482579074253062809613)
            ·
              refine ⟨18055680967152844898553605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48148482579074253062809613 18055680967152844898553605)
              ·
                refine ⟨3385440181341158418478801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18055680967152844898553605 3385440181341158418478801)
                ·
                  refine ⟨2539080136005868813859101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385440181341158418478801 2539080136005868813859101)
                  ·
                    refine ⟨952155051002200805197163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539080136005868813859101 952155051002200805197163)
                    ·
                      rfl

theorem cell22_2781473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_2781473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781473 prefixEnd_2781473 := by exact prefixLift 2781473
  have htrace : WordTrace (prefixWord ++ tailWord_2781473) baseStart_2781473 baseEnd_2781473 := by
    simpa [prefixWord, tailWord_2781473, baseEnd_2781473] using wordTrace_append hprefix tailTrace_2781473
  have hstable : (prefixWord ++ tailWord_2781473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781473).length < 2 ^ (prefixWord ++ tailWord_2781473).sum := by decide
  have hdescent : baseEnd_2781473 < baseStart_2781473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781535 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 1, 3]
def baseStart_2781535 : Nat := 118140960795 + 2781535 * 2 ^ 59
def prefixEnd_2781535 : Nat := 4983230072969 + 3 ^ 40 * 2781535 * 2
def baseEnd_2781535 : Nat := 952176274869253310146973

theorem tailTrace_2781535 : CollatzResearch.WordTrace tailWord_2781535 prefixEnd_2781535 952176274869253310146973 := by
  unfold tailWord_2781535
  simp only [CollatzResearch.WordTrace]
  refine ⟨101450915977981218202578059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67633943985320812135052039 101450915977981218202578059)
  ·
    refine ⟨152176373966971827303867089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101450915977981218202578059 152176373966971827303867089)
    ·
      refine ⟨114132280475228870477900317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152176373966971827303867089 114132280475228870477900317)
      ·
        refine ⟨42799605178210826429212619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114132280475228870477900317 42799605178210826429212619)
        ·
          refine ⟨64199407767316239643818929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42799605178210826429212619 64199407767316239643818929)
          ·
            refine ⟨48149555825487179732864197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64199407767316239643818929 48149555825487179732864197)
            ·
              refine ⟨9028041717278846199912037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48149555825487179732864197 9028041717278846199912037)
              ·
                refine ⟨1692757821989783662483507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9028041717278846199912037 1692757821989783662483507)
                ·
                  refine ⟨2539136732984675493725261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692757821989783662483507 2539136732984675493725261)
                  ·
                    refine ⟨952176274869253310146973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539136732984675493725261 952176274869253310146973)
                    ·
                      rfl

theorem cell22_2781535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_2781535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781535 prefixEnd_2781535 := by exact prefixLift 2781535
  have htrace : WordTrace (prefixWord ++ tailWord_2781535) baseStart_2781535 baseEnd_2781535 := by
    simpa [prefixWord, tailWord_2781535, baseEnd_2781535] using wordTrace_append hprefix tailTrace_2781535
  have hstable : (prefixWord ++ tailWord_2781535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781535).length < 2 ^ (prefixWord ++ tailWord_2781535).sum := by decide
  have hdescent : baseEnd_2781535 < baseStart_2781535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781569 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 1, 3]
def baseStart_2781569 : Nat := 118140960795 + 2781569 * 2 ^ 59
def prefixEnd_2781569 : Nat := 4983230072969 + 3 ^ 40 * 2781569 * 2
def baseEnd_2781569 : Nat := 952187913764088554796869

theorem tailTrace_2781569 : CollatzResearch.WordTrace tailWord_2781569 prefixEnd_2781569 952187913764088554796869 := by
  unfold tailWord_2781569
  simp only [CollatzResearch.WordTrace]
  refine ⟨101452156059858042009315761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67634770706572028006210507 101452156059858042009315761)
  ·
    refine ⟨76089117044893531506986821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101452156059858042009315761 76089117044893531506986821)
    ·
      refine ⟨14266709445917537157560029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76089117044893531506986821 14266709445917537157560029)
      ·
        refine ⟨5350016042219076434085011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14266709445917537157560029 5350016042219076434085011)
        ·
          refine ⟨8025024063328614651127517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350016042219076434085011 8025024063328614651127517)
          ·
            refine ⟨3009384023748230494172819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8025024063328614651127517 3009384023748230494172819)
            ·
              refine ⟨4514076035622345741259229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009384023748230494172819 4514076035622345741259229)
              ·
                refine ⟨1692778513358379652972211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4514076035622345741259229 1692778513358379652972211)
                ·
                  refine ⟨2539167770037569479458317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692778513358379652972211 2539167770037569479458317)
                  ·
                    refine ⟨952187913764088554796869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539167770037569479458317 952187913764088554796869)
                    ·
                      rfl

theorem cell22_2781569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_2781569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781569 prefixEnd_2781569 := by exact prefixLift 2781569
  have htrace : WordTrace (prefixWord ++ tailWord_2781569) baseStart_2781569 baseEnd_2781569 := by
    simpa [prefixWord, tailWord_2781569, baseEnd_2781569] using wordTrace_append hprefix tailTrace_2781569
  have hstable : (prefixWord ++ tailWord_2781569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781569).length < 2 ^ (prefixWord ++ tailWord_2781569).sum := by decide
  have hdescent : baseEnd_2781569 < baseStart_2781569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781623 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 2, 4]
def baseStart_2781623 : Nat := 118140960795 + 2781623 * 2 ^ 59
def prefixEnd_2781623 : Nat := 4983230072969 + 3 ^ 40 * 2781623 * 2
def baseEnd_2781623 : Nat := 952206399067650413946703

theorem tailTrace_2781623 : CollatzResearch.WordTrace tailWord_2781623 prefixEnd_2781623 952206399067650413946703 := by
  unfold tailWord_2781623
  simp only [CollatzResearch.WordTrace]
  refine ⟨101454125601662409231781523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67636083734441606154521015 101454125601662409231781523)
  ·
    refine ⟨152181188402493613847672285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101454125601662409231781523 152181188402493613847672285)
    ·
      refine ⟨57067945650935105192877107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152181188402493613847672285 57067945650935105192877107)
      ·
        refine ⟨85601918476402657789315661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57067945650935105192877107 85601918476402657789315661)
        ·
          refine ⟨32100719428650996670993373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85601918476402657789315661 32100719428650996670993373)
          ·
            refine ⟨12037769785744123751622515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32100719428650996670993373 12037769785744123751622515)
            ·
              refine ⟨18056654678616185627433773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12037769785744123751622515 18056654678616185627433773)
              ·
                refine ⟨6771245504481069610287665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18056654678616185627433773 6771245504481069610287665)
                ·
                  refine ⟨5078434128360802207715749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6771245504481069610287665 5078434128360802207715749)
                  ·
                    refine ⟨952206399067650413946703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078434128360802207715749 952206399067650413946703)
                    ·
                      rfl

theorem cell22_2781623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_2781623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781623 prefixEnd_2781623 := by exact prefixLift 2781623
  have htrace : WordTrace (prefixWord ++ tailWord_2781623) baseStart_2781623 baseEnd_2781623 := by
    simpa [prefixWord, tailWord_2781623, baseEnd_2781623] using wordTrace_append hprefix tailTrace_2781623
  have hstable : (prefixWord ++ tailWord_2781623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781623).length < 2 ^ (prefixWord ++ tailWord_2781623).sum := by decide
  have hdescent : baseEnd_2781623 < baseStart_2781623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781638 : List Nat := [6, 1, 15]
def baseStart_2781638 : Nat := 118140960795 + 2781638 * 2 ^ 59
def prefixEnd_2781638 : Nat := 4983230072969 + 3 ^ 40 * 2781638 * 2
def baseEnd_2781638 : Nat := 435396220335708904811

theorem tailTrace_2781638 : CollatzResearch.WordTrace tailWord_2781638 prefixEnd_2781638 435396220335708904811 := by
  unfold tailWord_2781638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170458521769002087299299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67636448464405377862385045 3170458521769002087299299)
  ·
    refine ⟨4755687782653503130948949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3170458521769002087299299 4755687782653503130948949)
    ·
      refine ⟨435396220335708904811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 4755687782653503130948949 435396220335708904811)
      ·
        rfl

theorem cell22_2781638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 15].length) (baseStart_2781638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781638 prefixEnd_2781638 := by exact prefixLift 2781638
  have htrace : WordTrace (prefixWord ++ tailWord_2781638) baseStart_2781638 baseEnd_2781638 := by
    simpa [prefixWord, tailWord_2781638, baseEnd_2781638] using wordTrace_append hprefix tailTrace_2781638
  have hstable : (prefixWord ++ tailWord_2781638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781638).length < 2 ^ (prefixWord ++ tailWord_2781638).sum := by decide
  have hdescent : baseEnd_2781638 < baseStart_2781638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781644 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 4]
def baseStart_2781644 : Nat := 118140960795 + 2781644 * 2 ^ 59
def prefixEnd_2781644 : Nat := 4983230072969 + 3 ^ 40 * 2781644 * 2
def baseEnd_2781644 : Nat := 317404529265604453057213

theorem tailTrace_2781644 : CollatzResearch.WordTrace tailWord_2781644 prefixEnd_2781644 317404529265604453057213 := by
  unfold tailWord_2781644
  simp only [CollatzResearch.WordTrace]
  refine ⟨50727445767293164909147993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67636594356390886545530657 50727445767293164909147993)
  ·
    refine ⟨38045584325469873681860995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50727445767293164909147993 38045584325469873681860995)
    ·
      refine ⟨57068376488204810522791493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38045584325469873681860995 57068376488204810522791493)
      ·
        refine ⟨10700320591538401973023405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57068376488204810522791493 10700320591538401973023405)
        ·
          refine ⟨4012620221826900739883777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10700320591538401973023405 4012620221826900739883777)
          ·
            refine ⟨3009465166370175554912833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012620221826900739883777 3009465166370175554912833)
            ·
              refine ⟨2257098874777631666184625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009465166370175554912833 2257098874777631666184625)
              ·
                refine ⟨1692824156083223749638469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257098874777631666184625 1692824156083223749638469)
                ·
                  refine ⟨317404529265604453057213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692824156083223749638469 317404529265604453057213)
                  ·
                    rfl

theorem cell22_2781644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_2781644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781644 prefixEnd_2781644 := by exact prefixLift 2781644
  have htrace : WordTrace (prefixWord ++ tailWord_2781644) baseStart_2781644 baseEnd_2781644 := by
    simpa [prefixWord, tailWord_2781644, baseEnd_2781644] using wordTrace_append hprefix tailTrace_2781644
  have hstable : (prefixWord ++ tailWord_2781644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781644).length < 2 ^ (prefixWord ++ tailWord_2781644).sum := by decide
  have hdescent : baseEnd_2781644 < baseStart_2781644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781700 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_2781700 : Nat := 118140960795 + 2781700 * 2 ^ 59
def prefixEnd_2781700 : Nat := 4983230072969 + 3 ^ 40 * 2781700 * 2
def baseEnd_2781700 : Nat := 317410919247082626590489

theorem tailTrace_2781700 : CollatzResearch.WordTrace tailWord_2781700 prefixEnd_2781700 317410919247082626590489 := by
  unfold tailWord_2781700
  simp only [CollatzResearch.WordTrace]
  refine ⟨50728467011191725691167277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67637956014922300921556369 50728467011191725691167277)
  ·
    refine ⟨19023175129196897134187729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50728467011191725691167277 19023175129196897134187729)
    ·
      refine ⟨14267381346897672850640797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19023175129196897134187729 14267381346897672850640797)
      ·
        refine ⟨5350268005086627318990299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14267381346897672850640797 5350268005086627318990299)
        ·
          refine ⟨8025402007629940978485449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350268005086627318990299 8025402007629940978485449)
          ·
            refine ⟨6019051505722455733864087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8025402007629940978485449 6019051505722455733864087)
            ·
              refine ⟨9028577258583683600796131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019051505722455733864087 9028577258583683600796131)
              ·
                refine ⟨13542865887875525401194197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028577258583683600796131 13542865887875525401194197)
                ·
                  refine ⟨317410919247082626590489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13542865887875525401194197 317410919247082626590489)
                  ·
                    rfl

theorem cell22_2781700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_2781700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781700 prefixEnd_2781700 := by exact prefixLift 2781700
  have htrace : WordTrace (prefixWord ++ tailWord_2781700) baseStart_2781700 baseEnd_2781700 := by
    simpa [prefixWord, tailWord_2781700, baseEnd_2781700] using wordTrace_append hprefix tailTrace_2781700
  have hstable : (prefixWord ++ tailWord_2781700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781700).length < 2 ^ (prefixWord ++ tailWord_2781700).sum := by decide
  have hdescent : baseEnd_2781700 < baseStart_2781700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781713 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_2781713 : Nat := 118140960795 + 2781713 * 2 ^ 59
def prefixEnd_2781713 : Nat := 4983230072969 + 3 ^ 40 * 2781713 * 2
def baseEnd_2781713 : Nat := 952237207906920179196427

theorem tailTrace_2781713 : CollatzResearch.WordTrace tailWord_2781713 prefixEnd_2781713 952237207906920179196427 := by
  unfold tailWord_2781713
  simp only [CollatzResearch.WordTrace]
  refine ⟨101457408171336354602557793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67638272114224236401705195 101457408171336354602557793)
  ·
    refine ⟨76093056128502265951918345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101457408171336354602557793 76093056128502265951918345)
    ·
      refine ⟨57069792096376699463938759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76093056128502265951918345 57069792096376699463938759)
      ·
        refine ⟨85604688144565049195908139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57069792096376699463938759 85604688144565049195908139)
        ·
          refine ⟨128407032216847573793862209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85604688144565049195908139 128407032216847573793862209)
          ·
            refine ⟨96305274162635680345396657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128407032216847573793862209 96305274162635680345396657)
            ·
              refine ⟨72228955621976760259047493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96305274162635680345396657 72228955621976760259047493)
              ·
                refine ⟨13542929179120642548571405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72228955621976760259047493 13542929179120642548571405)
                ·
                  refine ⟨5078598442170240955714277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13542929179120642548571405 5078598442170240955714277)
                  ·
                    refine ⟨952237207906920179196427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078598442170240955714277 952237207906920179196427)
                    ·
                      rfl

theorem cell22_2781713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_2781713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781713 prefixEnd_2781713 := by exact prefixLift 2781713
  have htrace : WordTrace (prefixWord ++ tailWord_2781713) baseStart_2781713 baseEnd_2781713 := by
    simpa [prefixWord, tailWord_2781713, baseEnd_2781713] using wordTrace_append hprefix tailTrace_2781713
  have hstable : (prefixWord ++ tailWord_2781713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781713).length < 2 ^ (prefixWord ++ tailWord_2781713).sum := by decide
  have hdescent : baseEnd_2781713 < baseStart_2781713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781760 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_2781760 : Nat := 118140960795 + 2781760 * 2 ^ 59
def prefixEnd_2781760 : Nat := 4983230072969 + 3 ^ 40 * 2781760 * 2
def baseEnd_2781760 : Nat := 952253296967427723271283

theorem tailTrace_2781760 : CollatzResearch.WordTrace tailWord_2781760 prefixEnd_2781760 952253296967427723271283 := by
  unfold tailWord_2781760
  simp only [CollatzResearch.WordTrace]
  refine ⟨50729561201083040814759367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67639414934777387753012489 50729561201083040814759367)
  ·
    refine ⟨76094341801624561222139051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50729561201083040814759367 76094341801624561222139051)
    ·
      refine ⟨114141512702436841833208577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76094341801624561222139051 114141512702436841833208577)
      ·
        refine ⟨85606134526827631374906433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114141512702436841833208577 85606134526827631374906433)
        ·
          refine ⟨64204600895120723531179825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85606134526827631374906433 64204600895120723531179825)
          ·
            refine ⟨48153450671340542648384869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64204600895120723531179825 48153450671340542648384869)
            ·
              refine ⟨9028772000876351746572163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48153450671340542648384869 9028772000876351746572163)
              ·
                refine ⟨13543158001314527619858245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028772000876351746572163 13543158001314527619858245)
                ·
                  refine ⟨2539342125246473928723421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13543158001314527619858245 2539342125246473928723421)
                  ·
                    refine ⟨952253296967427723271283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539342125246473928723421 952253296967427723271283)
                    ·
                      rfl

theorem cell22_2781760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_2781760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781760 prefixEnd_2781760 := by exact prefixLift 2781760
  have htrace : WordTrace (prefixWord ++ tailWord_2781760) baseStart_2781760 baseEnd_2781760 := by
    simpa [prefixWord, tailWord_2781760, baseEnd_2781760] using wordTrace_append hprefix tailTrace_2781760
  have hstable : (prefixWord ++ tailWord_2781760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781760).length < 2 ^ (prefixWord ++ tailWord_2781760).sum := by decide
  have hdescent : baseEnd_2781760 < baseStart_2781760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781777 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 2, 3]
def baseStart_2781777 : Nat := 118140960795 + 2781777 * 2 ^ 59
def prefixEnd_2781777 : Nat := 4983230072969 + 3 ^ 40 * 2781777 * 2
def baseEnd_2781777 : Nat := 952259116414845345596231

theorem tailTrace_2781777 : CollatzResearch.WordTrace tailWord_2781777 prefixEnd_2781777 952259116414845345596231 := by
  unfold tailWord_2781777
  simp only [CollatzResearch.WordTrace]
  refine ⟨101459742443104493532887585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67639828295402995688591723 101459742443104493532887585)
  ·
    refine ⟨76094806832328370149665689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101459742443104493532887585 76094806832328370149665689)
    ·
      refine ⟨57071105124246277612249267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76094806832328370149665689 57071105124246277612249267)
      ·
        refine ⟨85606657686369416418373901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57071105124246277612249267 85606657686369416418373901)
        ·
          refine ⟨32102496632388531156890213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85606657686369416418373901 32102496632388531156890213)
          ·
            refine ⟨6019218118572849591916915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32102496632388531156890213 6019218118572849591916915)
            ·
              refine ⟨9028827177859274387875373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019218118572849591916915 9028827177859274387875373)
              ·
                refine ⟨3385810191697227895453265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9028827177859274387875373 3385810191697227895453265)
                ·
                  refine ⟨2539357643772920921589949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385810191697227895453265 2539357643772920921589949)
                  ·
                    refine ⟨952259116414845345596231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539357643772920921589949 952259116414845345596231)
                    ·
                      rfl

theorem cell22_2781777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_2781777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781777 prefixEnd_2781777 := by exact prefixLift 2781777
  have htrace : WordTrace (prefixWord ++ tailWord_2781777) baseStart_2781777 baseEnd_2781777 := by
    simpa [prefixWord, tailWord_2781777, baseEnd_2781777] using wordTrace_append hprefix tailTrace_2781777
  have hstable : (prefixWord ++ tailWord_2781777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781777).length < 2 ^ (prefixWord ++ tailWord_2781777).sum := by decide
  have hdescent : baseEnd_2781777 < baseStart_2781777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781794 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2781794 : Nat := 118140960795 + 2781794 * 2 ^ 59
def prefixEnd_2781794 : Nat := 4983230072969 + 3 ^ 40 * 2781794 * 2
def baseEnd_2781794 : Nat := 952264935862262967921179

theorem tailTrace_2781794 : CollatzResearch.WordTrace tailWord_2781794 prefixEnd_2781794 952264935862262967921179 := by
  unfold tailWord_2781794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25365090621010726359064109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67640241656028603624170957 25365090621010726359064109)
  ·
    refine ⟨9511908982879022384649041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25365090621010726359064109 9511908982879022384649041)
    ·
      refine ⟨7133931737159266788486781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9511908982879022384649041 7133931737159266788486781)
      ·
        refine ⟨2675224401434725045682543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7133931737159266788486781 2675224401434725045682543)
        ·
          refine ⟨4012836602152087568523815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675224401434725045682543 4012836602152087568523815)
          ·
            refine ⟨6019254903228131352785723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012836602152087568523815 6019254903228131352785723)
            ·
              refine ⟨9028882354842197029178585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019254903228131352785723 9028882354842197029178585)
              ·
                refine ⟨6771661766131647771883939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9028882354842197029178585 6771661766131647771883939)
                ·
                  refine ⟨10157492649197471657825909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771661766131647771883939 10157492649197471657825909)
                  ·
                    refine ⟨952264935862262967921179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10157492649197471657825909 952264935862262967921179)
                    ·
                      rfl

theorem cell22_2781794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2781794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781794 prefixEnd_2781794 := by exact prefixLift 2781794
  have htrace : WordTrace (prefixWord ++ tailWord_2781794) baseStart_2781794 baseEnd_2781794 := by
    simpa [prefixWord, tailWord_2781794, baseEnd_2781794] using wordTrace_append hprefix tailTrace_2781794
  have hstable : (prefixWord ++ tailWord_2781794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781794).length < 2 ^ (prefixWord ++ tailWord_2781794).sum := by decide
  have hdescent : baseEnd_2781794 < baseStart_2781794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781813 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 4]
def baseStart_2781813 : Nat := 118140960795 + 2781813 * 2 ^ 59
def prefixEnd_2781813 : Nat := 4983230072969 + 3 ^ 40 * 2781813 * 2
def baseEnd_2781813 : Nat := 317423813316851083898707

theorem tailTrace_2781813 : CollatzResearch.WordTrace tailWord_2781813 prefixEnd_2781813 317423813316851083898707 := by
  unfold tailWord_2781813
  simp only [CollatzResearch.WordTrace]
  refine ⟨101461055470974071681198093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67640703647316047787465395 101461055470974071681198093)
  ·
    refine ⟨38047895801615276880449285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101461055470974071681198093 38047895801615276880449285)
    ·
      refine ⟨7133980462802864415084241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38047895801615276880449285 7133980462802864415084241)
      ·
        refine ⟨5350485347102148311313181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7133980462802864415084241 5350485347102148311313181)
        ·
          refine ⟨2006432005163305616742443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5350485347102148311313181 2006432005163305616742443)
          ·
            refine ⟨3009648007744958425113665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006432005163305616742443 3009648007744958425113665)
            ·
              refine ⟨2257236005808718818835249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009648007744958425113665 2257236005808718818835249)
              ·
                refine ⟨1692927004356539114126437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257236005808718818835249 1692927004356539114126437)
                ·
                  refine ⟨317423813316851083898707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692927004356539114126437 317423813316851083898707)
                  ·
                    rfl

theorem cell22_2781813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_2781813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781813 prefixEnd_2781813 := by exact prefixLift 2781813
  have htrace : WordTrace (prefixWord ++ tailWord_2781813) baseStart_2781813 baseEnd_2781813 := by
    simpa [prefixWord, tailWord_2781813, baseEnd_2781813] using wordTrace_append hprefix tailTrace_2781813
  have hstable : (prefixWord ++ tailWord_2781813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781813).length < 2 ^ (prefixWord ++ tailWord_2781813).sum := by decide
  have hdescent : baseEnd_2781813 < baseStart_2781813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781818 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_2781818 : Nat := 118140960795 + 2781818 * 2 ^ 59
def prefixEnd_2781818 : Nat := 4983230072969 + 3 ^ 40 * 2781818 * 2
def baseEnd_2781818 : Nat := 317424383850911635107035

theorem tailTrace_2781818 : CollatzResearch.WordTrace tailWord_2781818 prefixEnd_2781818 317424383850911635107035 := by
  unfold tailWord_2781818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25365309458988989383782527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67640825223970638356753405 25365309458988989383782527)
  ·
    refine ⟨38047964188483484075673791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25365309458988989383782527 38047964188483484075673791)
    ·
      refine ⟨57071946282725226113510687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38047964188483484075673791 57071946282725226113510687)
      ·
        refine ⟨85607919424087839170266031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57071946282725226113510687 85607919424087839170266031)
        ·
          refine ⟨128411879136131758755399047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85607919424087839170266031 128411879136131758755399047)
          ·
            refine ⟨192617818704197638133098571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128411879136131758755399047 192617818704197638133098571)
            ·
              refine ⟨288926728056296457199647857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192617818704197638133098571 288926728056296457199647857)
              ·
                refine ⟨216695046042222342899735893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288926728056296457199647857 216695046042222342899735893)
                ·
                  refine ⟨317424383850911635107035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 216695046042222342899735893 317424383850911635107035)
                  ·
                    rfl

theorem cell22_2781818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_2781818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781818 prefixEnd_2781818 := by exact prefixLift 2781818
  have htrace : WordTrace (prefixWord ++ tailWord_2781818) baseStart_2781818 baseEnd_2781818 := by
    simpa [prefixWord, tailWord_2781818, baseEnd_2781818] using wordTrace_append hprefix tailTrace_2781818
  have hstable : (prefixWord ++ tailWord_2781818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781818).length < 2 ^ (prefixWord ++ tailWord_2781818).sum := by decide
  have hdescent : baseEnd_2781818 < baseStart_2781818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781856 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 1, 3]
def baseStart_2781856 : Nat := 118140960795 + 2781856 * 2 ^ 59
def prefixEnd_2781856 : Nat := 4983230072969 + 3 ^ 40 * 2781856 * 2
def baseEnd_2781856 : Nat := 952286159729315472870989

theorem tailTrace_2781856 : CollatzResearch.WordTrace tailWord_2781856 prefixEnd_2781856 952286159729315472870989 := by
  unfold tailWord_2781856
  simp only [CollatzResearch.WordTrace]
  refine ⟨50731311904909145012506711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67641749206545526683342281 50731311904909145012506711)
  ·
    refine ⟨76096967857363717518760067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50731311904909145012506711 76096967857363717518760067)
    ·
      refine ⟨114145451786045576278140101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76096967857363717518760067 114145451786045576278140101)
      ·
        refine ⟨21402272209883545552151269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114145451786045576278140101 21402272209883545552151269)
        ·
          refine ⟨4012926039353164791028363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21402272209883545552151269 4012926039353164791028363)
          ·
            refine ⟨6019389059029747186542545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012926039353164791028363 6019389059029747186542545)
            ·
              refine ⟨4514541794272310389906909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6019389059029747186542545 4514541794272310389906909)
              ·
                refine ⟨1692953172852116396215091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4514541794272310389906909 1692953172852116396215091)
                ·
                  refine ⟨2539429759278174594322637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692953172852116396215091 2539429759278174594322637)
                  ·
                    refine ⟨952286159729315472870989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539429759278174594322637 952286159729315472870989)
                    ·
                      rfl

theorem cell22_2781856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_2781856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781856 prefixEnd_2781856 := by exact prefixLift 2781856
  have htrace : WordTrace (prefixWord ++ tailWord_2781856) baseStart_2781856 baseEnd_2781856 := by
    simpa [prefixWord, tailWord_2781856, baseEnd_2781856] using wordTrace_append hprefix tailTrace_2781856
  have hstable : (prefixWord ++ tailWord_2781856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781856).length < 2 ^ (prefixWord ++ tailWord_2781856).sum := by decide
  have hdescent : baseEnd_2781856 < baseStart_2781856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781869 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 5]
def baseStart_2781869 : Nat := 118140960795 + 2781869 * 2 ^ 59
def prefixEnd_2781869 : Nat := 4983230072969 + 3 ^ 40 * 2781869 * 2
def baseEnd_2781869 : Nat := 317430203298329257431983

theorem tailTrace_2781869 : CollatzResearch.WordTrace tailWord_2781869 prefixEnd_2781869 317430203298329257431983 := by
  unfold tailWord_2781869
  simp only [CollatzResearch.WordTrace]
  refine ⟨101463097958771193245236661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67642065305847462163491107 101463097958771193245236661)
  ·
    refine ⟨9512165433634799366740937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101463097958771193245236661 9512165433634799366740937)
    ·
      refine ⟨7134124075226099525055703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9512165433634799366740937 7134124075226099525055703)
      ·
        refine ⟨10701186112839149287583555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7134124075226099525055703 10701186112839149287583555)
        ·
          refine ⟨16051779169258723931375333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10701186112839149287583555 16051779169258723931375333)
          ·
            refine ⟨3009708594236010737132875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16051779169258723931375333 3009708594236010737132875)
            ·
              refine ⟨4514562891354016105699313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009708594236010737132875 4514562891354016105699313)
              ·
                refine ⟨3385922168515512079274485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4514562891354016105699313 3385922168515512079274485)
                ·
                  refine ⟨317430203298329257431983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3385922168515512079274485 317430203298329257431983)
                  ·
                    rfl

theorem cell22_2781869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_2781869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781869 prefixEnd_2781869 := by exact prefixLift 2781869
  have htrace : WordTrace (prefixWord ++ tailWord_2781869) baseStart_2781869 baseEnd_2781869 := by
    simpa [prefixWord, tailWord_2781869, baseEnd_2781869] using wordTrace_append hprefix tailTrace_2781869
  have hstable : (prefixWord ++ tailWord_2781869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781869).length < 2 ^ (prefixWord ++ tailWord_2781869).sum := by decide
  have hdescent : baseEnd_2781869 < baseStart_2781869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781895 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2781895 : Nat := 118140960795 + 2781895 * 2 ^ 59
def prefixEnd_2781895 : Nat := 4983230072969 + 3 ^ 40 * 2781895 * 2
def baseEnd_2781895 : Nat := 952299510226332371145869

theorem tailTrace_2781895 : CollatzResearch.WordTrace tailWord_2781895 prefixEnd_2781895 952299510226332371145869 := by
  unfold tailWord_2781895
  simp only [CollatzResearch.WordTrace]
  refine ⟨101464046256676999685683139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67642697504451333123788759 101464046256676999685683139)
  ·
    refine ⟨152196069385015499528524709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101464046256676999685683139 152196069385015499528524709)
    ·
      refine ⟨28536763009690406161598383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152196069385015499528524709 28536763009690406161598383)
      ·
        refine ⟨42805144514535609242397575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28536763009690406161598383 42805144514535609242397575)
        ·
          refine ⟨64207716771803413863596363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42805144514535609242397575 64207716771803413863596363)
          ·
            refine ⟨96311575157705120795394545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64207716771803413863596363 96311575157705120795394545)
            ·
              refine ⟨72233681368278840596545909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96311575157705120795394545 72233681368278840596545909)
              ·
                refine ⟨6771907628276141305926179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72233681368278840596545909 6771907628276141305926179)
                ·
                  refine ⟨10157861442414211958889269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6771907628276141305926179 10157861442414211958889269)
                  ·
                    refine ⟨952299510226332371145869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10157861442414211958889269 952299510226332371145869)
                    ·
                      rfl

theorem cell22_2781895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2781895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781895 prefixEnd_2781895 := by exact prefixLift 2781895
  have htrace : WordTrace (prefixWord ++ tailWord_2781895) baseStart_2781895 baseEnd_2781895 := by
    simpa [prefixWord, tailWord_2781895, baseEnd_2781895] using wordTrace_append hprefix tailTrace_2781895
  have hstable : (prefixWord ++ tailWord_2781895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781895).length < 2 ^ (prefixWord ++ tailWord_2781895).sum := by decide
  have hdescent : baseEnd_2781895 < baseStart_2781895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781912 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 4, 3]
def baseStart_2781912 : Nat := 118140960795 + 2781912 * 2 ^ 59
def prefixEnd_2781912 : Nat := 4983230072969 + 3 ^ 40 * 2781912 * 2
def baseEnd_2781912 : Nat := 952305329673749993470817

theorem tailTrace_2781912 : CollatzResearch.WordTrace tailWord_2781912 prefixEnd_2781912 952305329673749993470817 := by
  unfold tailWord_2781912
  simp only [CollatzResearch.WordTrace]
  refine ⟨50732333148807705794525995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67643110865076941059367993 50732333148807705794525995)
  ·
    refine ⟨76098499723211558691788993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50732333148807705794525995 76098499723211558691788993)
    ·
      refine ⟨57073874792408669018841745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76098499723211558691788993 57073874792408669018841745)
      ·
        refine ⟨42805406094306501764131309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57073874792408669018841745 42805406094306501764131309)
        ·
          refine ⟨16052027285364938161549241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42805406094306501764131309 16052027285364938161549241)
          ·
            refine ⟨12039020464023703621161931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16052027285364938161549241 12039020464023703621161931)
            ·
              refine ⟨18058530696035555431742897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12039020464023703621161931 18058530696035555431742897)
              ·
                refine ⟨13543898022026666573807173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18058530696035555431742897 13543898022026666573807173)
                ·
                  refine ⟨2539480879129999982588845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13543898022026666573807173 2539480879129999982588845)
                  ·
                    refine ⟨952305329673749993470817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539480879129999982588845 952305329673749993470817)
                    ·
                      rfl

theorem cell22_2781912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_2781912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781912 prefixEnd_2781912 := by exact prefixLift 2781912
  have htrace : WordTrace (prefixWord ++ tailWord_2781912) baseStart_2781912 baseEnd_2781912 := by
    simpa [prefixWord, tailWord_2781912, baseEnd_2781912] using wordTrace_append hprefix tailTrace_2781912
  have hstable : (prefixWord ++ tailWord_2781912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781912).length < 2 ^ (prefixWord ++ tailWord_2781912).sum := by decide
  have hdescent : baseEnd_2781912 < baseStart_2781912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781925 : List Nat := [1, 3, 1, 4, 1, 2, 10]
def baseStart_2781925 : Nat := 118140960795 + 2781925 * 2 ^ 59
def prefixEnd_2781925 : Nat := 4983230072969 + 3 ^ 40 * 2781925 * 2
def baseEnd_2781925 : Nat := 35270732586645270107251

theorem tailTrace_2781925 : CollatzResearch.WordTrace tailWord_2781925 prefixEnd_2781925 35270732586645270107251 := by
  unfold tailWord_2781925
  simp only [CollatzResearch.WordTrace]
  refine ⟨101465140446568314809275229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67643426964378876539516819 101465140446568314809275229)
  ·
    refine ⟨38049427667463118053478211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101465140446568314809275229 38049427667463118053478211)
    ·
      refine ⟨57074141501194677080217317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38049427667463118053478211 57074141501194677080217317)
      ·
        refine ⟨10701401531474001952540747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57074141501194677080217317 10701401531474001952540747)
        ·
          refine ⟨16052102297211002928811121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10701401531474001952540747 16052102297211002928811121)
          ·
            refine ⟨12039076722908252196608341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16052102297211002928811121 12039076722908252196608341)
            ·
              refine ⟨35270732586645270107251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12039076722908252196608341 35270732586645270107251)
              ·
                rfl

theorem cell22_2781925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 10].length) (baseStart_2781925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781925 prefixEnd_2781925 := by exact prefixLift 2781925
  have htrace : WordTrace (prefixWord ++ tailWord_2781925) baseStart_2781925 baseEnd_2781925 := by
    simpa [prefixWord, tailWord_2781925, baseEnd_2781925] using wordTrace_append hprefix tailTrace_2781925
  have hstable : (prefixWord ++ tailWord_2781925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781925).length < 2 ^ (prefixWord ++ tailWord_2781925).sum := by decide
  have hdescent : baseEnd_2781925 < baseStart_2781925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781942 : List Nat := [5, 1, 1, 1, 1, 2, 4, 7]
def baseStart_2781942 : Nat := 118140960795 + 2781942 * 2 ^ 59
def prefixEnd_2781942 : Nat := 4983230072969 + 3 ^ 40 * 2781942 * 2
def baseEnd_2781942 : Nat := 105812844365204435024525

theorem tailTrace_2781942 : CollatzResearch.WordTrace tailWord_2781942 prefixEnd_2781942 105812844365204435024525 := by
  unfold tailWord_2781942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341610030469170419540255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67643840325004484475096053 6341610030469170419540255)
  ·
    refine ⟨9512415045703755629310383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341610030469170419540255 9512415045703755629310383)
    ·
      refine ⟨14268622568555633443965575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9512415045703755629310383 14268622568555633443965575)
      ·
        refine ⟨21402933852833450165948363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14268622568555633443965575 21402933852833450165948363)
        ·
          refine ⟨32104400779250175248922545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21402933852833450165948363 32104400779250175248922545)
          ·
            refine ⟨24078300584437631436691909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32104400779250175248922545 24078300584437631436691909)
            ·
              refine ⟨4514681359582055894379733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24078300584437631436691909 4514681359582055894379733)
              ·
                refine ⟨105812844365204435024525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4514681359582055894379733 105812844365204435024525)
                ·
                  rfl

theorem cell22_2781942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_2781942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781942 prefixEnd_2781942 := by exact prefixLift 2781942
  have htrace : WordTrace (prefixWord ++ tailWord_2781942) baseStart_2781942 baseEnd_2781942 := by
    simpa [prefixWord, tailWord_2781942, baseEnd_2781942] using wordTrace_append hprefix tailTrace_2781942
  have hstable : (prefixWord ++ tailWord_2781942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781942).length < 2 ^ (prefixWord ++ tailWord_2781942).sum := by decide
  have hdescent : baseEnd_2781942 < baseStart_2781942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2781957 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_2781957 : Nat := 118140960795 + 2781957 * 2 ^ 59
def prefixEnd_2781957 : Nat := 4983230072969 + 3 ^ 40 * 2781957 * 2
def baseEnd_2781957 : Nat := 952320734093384876095679

theorem tailTrace_2781957 : CollatzResearch.WordTrace tailWord_2781957 prefixEnd_2781957 952320734093384876095679 := by
  unfold tailWord_2781957
  simp only [CollatzResearch.WordTrace]
  refine ⟨101466307582452384274440125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67644205054968256182960083 101466307582452384274440125)
  ·
    refine ⟨38049865343419644102915047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101466307582452384274440125 38049865343419644102915047)
    ·
      refine ⟨57074798015129466154372571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38049865343419644102915047 57074798015129466154372571)
      ·
        refine ⟨85612197022694199231558857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57074798015129466154372571 85612197022694199231558857)
        ·
          refine ⟨64209147767020649423669143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85612197022694199231558857 64209147767020649423669143)
          ·
            refine ⟨96313721650530974135503715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64209147767020649423669143 96313721650530974135503715)
            ·
              refine ⟨144470582475796461203255573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96313721650530974135503715 144470582475796461203255573)
              ·
                refine ⟨6772058553552959118902605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144470582475796461203255573 6772058553552959118902605)
                ·
                  refine ⟨2539521957582359669588477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6772058553552959118902605 2539521957582359669588477)
                  ·
                    refine ⟨952320734093384876095679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539521957582359669588477 952320734093384876095679)
                    ·
                      rfl

theorem cell22_2781957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_2781957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2781957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2781957 prefixEnd_2781957 := by exact prefixLift 2781957
  have htrace : WordTrace (prefixWord ++ tailWord_2781957) baseStart_2781957 baseEnd_2781957 := by
    simpa [prefixWord, tailWord_2781957, baseEnd_2781957] using wordTrace_append hprefix tailTrace_2781957
  have hstable : (prefixWord ++ tailWord_2781957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2781957).length < 2 ^ (prefixWord ++ tailWord_2781957).sum := by decide
  have hdescent : baseEnd_2781957 < baseStart_2781957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2781957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782002 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2782002 : Nat := 118140960795 + 2782002 * 2 ^ 59
def prefixEnd_2782002 : Nat := 4983230072969 + 3 ^ 40 * 2782002 * 2
def baseEnd_2782002 : Nat := 952336138513019758720541

theorem tailTrace_2782002 : CollatzResearch.WordTrace tailWord_2782002 prefixEnd_2782002 952336138513019758720541 := by
  unfold tailWord_2782002
  simp only [CollatzResearch.WordTrace]
  refine ⟨25366987216822339239957065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67645299244859571306552173 25366987216822339239957065)
  ·
    refine ⟨19025240412616754429967799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25366987216822339239957065 19025240412616754429967799)
    ·
      refine ⟨28537860618925131644951699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19025240412616754429967799 28537860618925131644951699)
      ·
        refine ⟨42806790928387697467427549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28537860618925131644951699 42806790928387697467427549)
        ·
          refine ⟨16052546598145386550285331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42806790928387697467427549 16052546598145386550285331)
          ·
            refine ⟨24078819897218079825427997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16052546598145386550285331 24078819897218079825427997)
            ·
              refine ⟨9029557461456779934535499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24078819897218079825427997 9029557461456779934535499)
              ·
                refine ⟨13544336192185169901803249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9029557461456779934535499 13544336192185169901803249)
                ·
                  refine ⟨10158252144138877426352437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13544336192185169901803249 10158252144138877426352437)
                  ·
                    refine ⟨952336138513019758720541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10158252144138877426352437 952336138513019758720541)
                    ·
                      rfl

theorem cell22_2782002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2782002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782002 prefixEnd_2782002 := by exact prefixLift 2782002
  have htrace : WordTrace (prefixWord ++ tailWord_2782002) baseStart_2782002 baseEnd_2782002 := by
    simpa [prefixWord, tailWord_2782002, baseEnd_2782002] using wordTrace_append hprefix tailTrace_2782002
  have hstable : (prefixWord ++ tailWord_2782002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782002).length < 2 ^ (prefixWord ++ tailWord_2782002).sum := by decide
  have hdescent : baseEnd_2782002 < baseStart_2782002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782034 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2782034 : Nat := 118140960795 + 2782034 * 2 ^ 59
def prefixEnd_2782034 : Nat := 4983230072969 + 3 ^ 40 * 2782034 * 2
def baseEnd_2782034 : Nat := 952347092766982341920443

theorem tailTrace_2782034 : CollatzResearch.WordTrace tailWord_2782034 prefixEnd_2782034 952347092766982341920443 := by
  unfold tailWord_2782034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25367279000793356606248289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67646077335448950949995437 25367279000793356606248289)
  ·
    refine ⟨19025459250595017454686217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25367279000793356606248289 19025459250595017454686217)
    ·
      refine ⟨14269094437946263091014663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19025459250595017454686217 14269094437946263091014663)
      ·
        refine ⟨21403641656919394636521995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14269094437946263091014663 21403641656919394636521995)
        ·
          refine ⟨32105462485379091954782993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21403641656919394636521995 32105462485379091954782993)
          ·
            refine ⟨24079096864034318966087245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32105462485379091954782993 24079096864034318966087245)
            ·
              refine ⟨9029661324012869612282717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24079096864034318966087245 9029661324012869612282717)
              ·
                refine ⟨3386122996504826104606019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9029661324012869612282717 3386122996504826104606019)
                ·
                  refine ⟨5079184494757239156909029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386122996504826104606019 5079184494757239156909029)
                  ·
                    refine ⟨952347092766982341920443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5079184494757239156909029 952347092766982341920443)
                    ·
                      rfl

theorem cell22_2782034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2782034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782034 prefixEnd_2782034 := by exact prefixLift 2782034
  have htrace : WordTrace (prefixWord ++ tailWord_2782034) baseStart_2782034 baseEnd_2782034 := by
    simpa [prefixWord, tailWord_2782034, baseEnd_2782034] using wordTrace_append hprefix tailTrace_2782034
  have hstable : (prefixWord ++ tailWord_2782034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782034).length < 2 ^ (prefixWord ++ tailWord_2782034).sum := by decide
  have hdescent : baseEnd_2782034 < baseStart_2782034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782064 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 2, 3]
def baseStart_2782064 : Nat := 118140960795 + 2782064 * 2 ^ 59
def prefixEnd_2782064 : Nat := 4983230072969 + 3 ^ 40 * 2782064 * 2
def baseEnd_2782064 : Nat := 952357362380072263670351

theorem tailTrace_2782064 : CollatzResearch.WordTrace tailWord_2782064 prefixEnd_2782064 952357362380072263670351 := by
  unfold tailWord_2782064
  simp only [CollatzResearch.WordTrace]
  refine ⟨50735105096532370774292623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67646806795376494365723497 50735105096532370774292623)
  ·
    refine ⟨76102657644798556161438935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50735105096532370774292623 76102657644798556161438935)
    ·
      refine ⟨114153986467197834242158403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76102657644798556161438935 114153986467197834242158403)
      ·
        refine ⟨171230979700796751363237605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114153986467197834242158403 171230979700796751363237605)
        ·
          refine ⟨32105808693899390880607051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171230979700796751363237605 32105808693899390880607051)
          ·
            refine ⟨48158713040849086320910577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32105808693899390880607051 48158713040849086320910577)
            ·
              refine ⟨36119034780636814740682933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48158713040849086320910577 36119034780636814740682933)
              ·
                refine ⟨3386159510684701381939025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36119034780636814740682933 3386159510684701381939025)
                ·
                  refine ⟨2539619633013526036454269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3386159510684701381939025 2539619633013526036454269)
                  ·
                    refine ⟨952357362380072263670351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539619633013526036454269 952357362380072263670351)
                    ·
                      rfl

theorem cell22_2782064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_2782064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782064 prefixEnd_2782064 := by exact prefixLift 2782064
  have htrace : WordTrace (prefixWord ++ tailWord_2782064) baseStart_2782064 baseEnd_2782064 := by
    simpa [prefixWord, tailWord_2782064, baseEnd_2782064] using wordTrace_append hprefix tailTrace_2782064
  have hstable : (prefixWord ++ tailWord_2782064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782064).length < 2 ^ (prefixWord ++ tailWord_2782064).sum := by decide
  have hdescent : baseEnd_2782064 < baseStart_2782064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782169 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_2782169 : Nat := 118140960795 + 2782169 * 2 ^ 59
def prefixEnd_2782169 : Nat := 4983230072969 + 3 ^ 40 * 2782169 * 2
def baseEnd_2782169 : Nat := 952393306025886989795029

theorem tailTrace_2782169 : CollatzResearch.WordTrace tailWord_2782169 prefixEnd_2782169 952393306025886989795029 := by
  unfold tailWord_2782169
  simp only [CollatzResearch.WordTrace]
  refine ⟨101474039857684344481157561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67649359905122896320771707 101474039857684344481157561)
  ·
    refine ⟨76105529893263258360868171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101474039857684344481157561 76105529893263258360868171)
    ·
      refine ⟨114158294839894887541302257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76105529893263258360868171 114158294839894887541302257)
      ·
        refine ⟨85618721129921165655976693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114158294839894887541302257 85618721129921165655976693)
        ·
          refine ⟨8026755105930109280247815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85618721129921165655976693 8026755105930109280247815)
          ·
            refine ⟨12040132658895163920371723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8026755105930109280247815 12040132658895163920371723)
            ·
              refine ⟨18060198988342745880557585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12040132658895163920371723 18060198988342745880557585)
              ·
                refine ⟨13545149241257059410418189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18060198988342745880557585 13545149241257059410418189)
                ·
                  refine ⟨5079430965471397278906821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13545149241257059410418189 5079430965471397278906821)
                  ·
                    refine ⟨952393306025886989795029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5079430965471397278906821 952393306025886989795029)
                    ·
                      rfl

theorem cell22_2782169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_2782169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782169 prefixEnd_2782169 := by exact prefixLift 2782169
  have htrace : WordTrace (prefixWord ++ tailWord_2782169) baseStart_2782169 baseEnd_2782169 := by
    simpa [prefixWord, tailWord_2782169, baseEnd_2782169] using wordTrace_append hprefix tailTrace_2782169
  have hstable : (prefixWord ++ tailWord_2782169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782169).length < 2 ^ (prefixWord ++ tailWord_2782169).sum := by decide
  have hdescent : baseEnd_2782169 < baseStart_2782169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782201 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 4]
def baseStart_2782201 : Nat := 118140960795 + 2782201 * 2 ^ 59
def prefixEnd_2782201 : Nat := 4983230072969 + 3 ^ 40 * 2782201 * 2
def baseEnd_2782201 : Nat := 317468086759949857664977

theorem tailTrace_2782201 : CollatzResearch.WordTrace tailWord_2782201 prefixEnd_2782201 317468086759949857664977 := by
  unfold tailWord_2782201
  simp only [CollatzResearch.WordTrace]
  refine ⟨101475206993568413946322457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67650137995712275964214971 101475206993568413946322457)
  ·
    refine ⟨76106405245176310459741843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101475206993568413946322457 76106405245176310459741843)
    ·
      refine ⟨114159607867764465689612765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76106405245176310459741843 114159607867764465689612765)
      ·
        refine ⟨42809852950411674633604787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114159607867764465689612765 42809852950411674633604787)
        ·
          refine ⟨64214779425617511950407181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42809852950411674633604787 64214779425617511950407181)
          ·
            refine ⟨24080542284606566981402693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64214779425617511950407181 24080542284606566981402693)
            ·
              refine ⟨4515101678363731309013005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24080542284606566981402693 4515101678363731309013005)
              ·
                refine ⟨1693163129386399240879877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4515101678363731309013005 1693163129386399240879877)
                ·
                  refine ⟨317468086759949857664977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693163129386399240879877 317468086759949857664977)
                  ·
                    rfl

theorem cell22_2782201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_2782201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782201 prefixEnd_2782201 := by exact prefixLift 2782201
  have htrace : WordTrace (prefixWord ++ tailWord_2782201) baseStart_2782201 baseEnd_2782201 := by
    simpa [prefixWord, tailWord_2782201, baseEnd_2782201] using wordTrace_append hprefix tailTrace_2782201
  have hstable : (prefixWord ++ tailWord_2782201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782201).length < 2 ^ (prefixWord ++ tailWord_2782201).sum := by decide
  have hdescent : baseEnd_2782201 < baseStart_2782201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782216 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_2782216 : Nat := 118140960795 + 2782216 * 2 ^ 59
def prefixEnd_2782216 : Nat := 4983230072969 + 3 ^ 40 * 2782216 * 2
def baseEnd_2782216 : Nat := 952409395086394533869885

theorem tailTrace_2782216 : CollatzResearch.WordTrace tailWord_2782216 prefixEnd_2782216 952409395086394533869885 := by
  unfold tailWord_2782216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50737877044257035754059251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67650502725676047672079001 50737877044257035754059251)
  ·
    refine ⟨76106815566385553631088877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50737877044257035754059251 76106815566385553631088877)
    ·
      refine ⟨28540055837394582611658329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76106815566385553631088877 28540055837394582611658329)
      ·
        refine ⟨21405041878045936958743747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28540055837394582611658329 21405041878045936958743747)
        ·
          refine ⟨32107562817068905438115621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21405041878045936958743747 32107562817068905438115621)
          ·
            refine ⟨6020168028200419769646679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32107562817068905438115621 6020168028200419769646679)
            ·
              refine ⟨9030252042300629654470019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6020168028200419769646679 9030252042300629654470019)
              ·
                refine ⟨13545378063450944481705029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030252042300629654470019 13545378063450944481705029)
                ·
                  refine ⟨2539758386897052090319693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13545378063450944481705029 2539758386897052090319693)
                  ·
                    refine ⟨952409395086394533869885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539758386897052090319693 952409395086394533869885)
                    ·
                      rfl

theorem cell22_2782216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_2782216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782216 prefixEnd_2782216 := by exact prefixLift 2782216
  have htrace : WordTrace (prefixWord ++ tailWord_2782216) baseStart_2782216 baseEnd_2782216 := by
    simpa [prefixWord, tailWord_2782216, baseEnd_2782216] using wordTrace_append hprefix tailTrace_2782216
  have hstable : (prefixWord ++ tailWord_2782216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782216).length < 2 ^ (prefixWord ++ tailWord_2782216).sum := by decide
  have hdescent : baseEnd_2782216 < baseStart_2782216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782289 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2782289 : Nat := 118140960795 + 2782289 * 2 ^ 59
def prefixEnd_2782289 : Nat := 4983230072969 + 3 ^ 40 * 2782289 * 2
def baseEnd_2782289 : Nat := 952434384478246676794661

theorem tailTrace_2782289 : CollatzResearch.WordTrace tailWord_2782289 prefixEnd_2782289 952434384478246676794661 := by
  unfold tailWord_2782289
  simp only [CollatzResearch.WordTrace]
  refine ⟨101478416617249604975525921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67652277744833069983683947 101478416617249604975525921)
  ·
    refine ⟨76108812462937203731644441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101478416617249604975525921 76108812462937203731644441)
    ·
      refine ⟨57081609347202902798733331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76108812462937203731644441 57081609347202902798733331)
      ·
        refine ⟨85622414020804354198099997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57081609347202902798733331 85622414020804354198099997)
        ·
          refine ⟨32108405257801632824287499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85622414020804354198099997 32108405257801632824287499)
          ·
            refine ⟨48162607886702449236431249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32108405257801632824287499 48162607886702449236431249)
            ·
              refine ⟨36121955915026836927323437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48162607886702449236431249 36121955915026836927323437)
              ·
                refine ⟨13545733468135063847746289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36121955915026836927323437 13545733468135063847746289)
                ·
                  refine ⟨10159300101101297885809717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13545733468135063847746289 10159300101101297885809717)
                  ·
                    refine ⟨952434384478246676794661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10159300101101297885809717 952434384478246676794661)
                    ·
                      rfl

theorem cell22_2782289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2782289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782289 prefixEnd_2782289 := by exact prefixLift 2782289
  have htrace : WordTrace (prefixWord ++ tailWord_2782289) baseStart_2782289 baseEnd_2782289 := by
    simpa [prefixWord, tailWord_2782289, baseEnd_2782289] using wordTrace_append hprefix tailTrace_2782289
  have hstable : (prefixWord ++ tailWord_2782289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782289).length < 2 ^ (prefixWord ++ tailWord_2782289).sum := by decide
  have hdescent : baseEnd_2782289 < baseStart_2782289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782325 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 5]
def baseStart_2782325 : Nat := 118140960795 + 2782325 * 2 ^ 59
def prefixEnd_2782325 : Nat := 4983230072969 + 3 ^ 40 * 2782325 * 2
def baseEnd_2782325 : Nat := 317482236004651527631517

theorem tailTrace_2782325 : CollatzResearch.WordTrace tailWord_2782325 prefixEnd_2782325 317482236004651527631517 := by
  unfold tailWord_2782325
  simp only [CollatzResearch.WordTrace]
  refine ⟨101479729645119183123836429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67653153096746122082557619 101479729645119183123836429)
  ·
    refine ⟨38054898616919693671438661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101479729645119183123836429 38054898616919693671438661)
    ·
      refine ⟨7135293490672442563394749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38054898616919693671438661 7135293490672442563394749)
      ·
        refine ⟨2675735059002165961273031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7135293490672442563394749 2675735059002165961273031)
        ·
          refine ⟨4013602588503248941909547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675735059002165961273031 4013602588503248941909547)
          ·
            refine ⟨6020403882754873412864321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013602588503248941909547 6020403882754873412864321)
            ·
              refine ⟨4515302912066155059648241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6020403882754873412864321 4515302912066155059648241)
              ·
                refine ⟨3386477184049616294736181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4515302912066155059648241 3386477184049616294736181)
                ·
                  refine ⟨317482236004651527631517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3386477184049616294736181 317482236004651527631517)
                  ·
                    rfl

theorem cell22_2782325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_2782325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782325 prefixEnd_2782325 := by exact prefixLift 2782325
  have htrace : WordTrace (prefixWord ++ tailWord_2782325) baseStart_2782325 baseEnd_2782325 := by
    simpa [prefixWord, tailWord_2782325, baseEnd_2782325] using wordTrace_append hprefix tailTrace_2782325
  have hstable : (prefixWord ++ tailWord_2782325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782325).length < 2 ^ (prefixWord ++ tailWord_2782325).sum := by decide
  have hdescent : baseEnd_2782325 < baseStart_2782325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782329 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 1, 3]
def baseStart_2782329 : Nat := 118140960795 + 2782329 * 2 ^ 59
def prefixEnd_2782329 : Nat := 4983230072969 + 3 ^ 40 * 2782329 * 2
def baseEnd_2782329 : Nat := 952448077295699905794539

theorem tailTrace_2782329 : CollatzResearch.WordTrace tailWord_2782329 prefixEnd_2782329 952448077295699905794539 := by
  unfold tailWord_2782329
  simp only [CollatzResearch.WordTrace]
  refine ⟨101479875537104691806982041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67653250358069794537988027 101479875537104691806982041)
  ·
    refine ⟨76109906652828518855236531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101479875537104691806982041 76109906652828518855236531)
    ·
      refine ⟨114164859979242778282854797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76109906652828518855236531 114164859979242778282854797)
      ·
        refine ⟨42811822492216041856070549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114164859979242778282854797 42811822492216041856070549)
        ·
          refine ⟨2006804179322626962003307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42811822492216041856070549 2006804179322626962003307)
          ·
            refine ⟨3010206268983940443004961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006804179322626962003307 3010206268983940443004961)
            ·
              refine ⟨2257654701737955332253721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010206268983940443004961 2257654701737955332253721)
              ·
                refine ⟨1693241026303466499190291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257654701737955332253721 1693241026303466499190291)
                ·
                  refine ⟨2539861539455199748785437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693241026303466499190291 2539861539455199748785437)
                  ·
                    refine ⟨952448077295699905794539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539861539455199748785437 952448077295699905794539)
                    ·
                      rfl

theorem cell22_2782329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_2782329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782329 prefixEnd_2782329 := by exact prefixLift 2782329
  have htrace : WordTrace (prefixWord ++ tailWord_2782329) baseStart_2782329 baseEnd_2782329 := by
    simpa [prefixWord, tailWord_2782329, baseEnd_2782329] using wordTrace_append hprefix tailTrace_2782329
  have hstable : (prefixWord ++ tailWord_2782329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782329).length < 2 ^ (prefixWord ++ tailWord_2782329).sum := by decide
  have hdescent : baseEnd_2782329 < baseStart_2782329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782385 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_2782385 : Nat := 118140960795 + 2782385 * 2 ^ 59
def prefixEnd_2782385 : Nat := 4983230072969 + 3 ^ 40 * 2782385 * 2
def baseEnd_2782385 : Nat := 952467247240134426394367

theorem tailTrace_2782385 : CollatzResearch.WordTrace tailWord_2782385 prefixEnd_2782385 952467247240134426394367 := by
  unfold tailWord_2782385
  simp only [CollatzResearch.WordTrace]
  refine ⟨101481918024901813371020609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67654612016601208914013739 101481918024901813371020609)
  ·
    refine ⟨76111438518676360028265457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101481918024901813371020609 76111438518676360028265457)
    ·
      refine ⟨57083578889007270021199093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76111438518676360028265457 57083578889007270021199093)
      ·
        refine ⟨5351585520844431564487415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57083578889007270021199093 5351585520844431564487415)
        ·
          refine ⟨8027378281266647346731123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351585520844431564487415 8027378281266647346731123)
          ·
            refine ⟨12041067421899971020096685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027378281266647346731123 12041067421899971020096685)
            ·
              refine ⟨4515400283212489132536257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12041067421899971020096685 4515400283212489132536257)
              ·
                refine ⟨3386550212409366849402193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4515400283212489132536257 3386550212409366849402193)
                ·
                  refine ⟨2539912659307025137051645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3386550212409366849402193 2539912659307025137051645)
                  ·
                    refine ⟨952467247240134426394367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539912659307025137051645 952467247240134426394367)
                    ·
                      rfl

theorem cell22_2782385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_2782385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782385 prefixEnd_2782385 := by exact prefixLift 2782385
  have htrace : WordTrace (prefixWord ++ tailWord_2782385) baseStart_2782385 baseEnd_2782385 := by
    simpa [prefixWord, tailWord_2782385, baseEnd_2782385] using wordTrace_append hprefix tailTrace_2782385
  have hstable : (prefixWord ++ tailWord_2782385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782385).length < 2 ^ (prefixWord ++ tailWord_2782385).sum := by decide
  have hdescent : baseEnd_2782385 < baseStart_2782385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782447 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 3, 3]
def baseStart_2782447 : Nat := 118140960795 + 2782447 * 2 ^ 59
def prefixEnd_2782447 : Nat := 4983230072969 + 3 ^ 40 * 2782447 * 2
def baseEnd_2782447 : Nat := 952488471107186931344177

theorem tailTrace_2782447 : CollatzResearch.WordTrace tailWord_2782447 prefixEnd_2782447 952488471107186931344177 := by
  unfold tailWord_2782447
  simp only [CollatzResearch.WordTrace]
  refine ⟨101484179350677197959777595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67656119567118131973185063 101484179350677197959777595)
  ·
    refine ⟨152226269026015796939666393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101484179350677197959777595 152226269026015796939666393)
    ·
      refine ⟨114169701769511847704749795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152226269026015796939666393 114169701769511847704749795)
      ·
        refine ⟨171254552654267771557124693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114169701769511847704749795 171254552654267771557124693)
        ·
          refine ⟨2006889288917200447935055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 171254552654267771557124693 2006889288917200447935055)
          ·
            refine ⟨3010333933375800671902583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006889288917200447935055 3010333933375800671902583)
            ·
              refine ⟨4515500900063701007853875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010333933375800671902583 4515500900063701007853875)
              ·
                refine ⟨6773251350095551511780813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515500900063701007853875 6773251350095551511780813)
                ·
                  refine ⟨2539969256285831816917805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6773251350095551511780813 2539969256285831816917805)
                  ·
                    refine ⟨952488471107186931344177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2539969256285831816917805 952488471107186931344177)
                    ·
                      rfl

theorem cell22_2782447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_2782447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782447 prefixEnd_2782447 := by exact prefixLift 2782447
  have htrace : WordTrace (prefixWord ++ tailWord_2782447) baseStart_2782447 baseEnd_2782447 := by
    simpa [prefixWord, tailWord_2782447, baseEnd_2782447] using wordTrace_append hprefix tailTrace_2782447
  have hstable : (prefixWord ++ tailWord_2782447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782447).length < 2 ^ (prefixWord ++ tailWord_2782447).sum := by decide
  have hdescent : baseEnd_2782447 < baseStart_2782447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782535 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 2, 4]
def baseStart_2782535 : Nat := 118140960795 + 2782535 * 2 ^ 59
def prefixEnd_2782535 : Nat := 4983230072969 + 3 ^ 40 * 2782535 * 2
def baseEnd_2782535 : Nat := 952518595305584035143907

theorem tailTrace_2782535 : CollatzResearch.WordTrace tailWord_2782535 prefixEnd_2782535 952518595305584035143907 := by
  unfold tailWord_2782535
  simp only [CollatzResearch.WordTrace]
  refine ⟨101487388974358388988981059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67658259316238925992654039 101487388974358388988981059)
  ·
    refine ⟨152231083461537583483471589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101487388974358388988981059 152231083461537583483471589)
    ·
      refine ⟨28543328149038296903150923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152231083461537583483471589 28543328149038296903150923)
      ·
        refine ⟨42814992223557445354726385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28543328149038296903150923 42814992223557445354726385)
        ·
          refine ⟨32111244167668084016044789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42814992223557445354726385 32111244167668084016044789)
          ·
            refine ⟨3010429140718882876504199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32111244167668084016044789 3010429140718882876504199)
            ·
              refine ⟨4515643711078324314756299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010429140718882876504199 4515643711078324314756299)
              ·
                refine ⟨6773465566617486472134449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515643711078324314756299 6773465566617486472134449)
                ·
                  refine ⟨5080099174963114854100837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773465566617486472134449 5080099174963114854100837)
                  ·
                    refine ⟨952518595305584035143907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080099174963114854100837 952518595305584035143907)
                    ·
                      rfl

theorem cell22_2782535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_2782535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782535 prefixEnd_2782535 := by exact prefixLift 2782535
  have htrace : WordTrace (prefixWord ++ tailWord_2782535) baseStart_2782535 baseEnd_2782535 := by
    simpa [prefixWord, tailWord_2782535, baseEnd_2782535] using wordTrace_append hprefix tailTrace_2782535
  have hstable : (prefixWord ++ tailWord_2782535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782535).length < 2 ^ (prefixWord ++ tailWord_2782535).sum := by decide
  have hdescent : baseEnd_2782535 < baseStart_2782535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782541 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2782541 : Nat := 118140960795 + 2782541 * 2 ^ 59
def prefixEnd_2782541 : Nat := 4983230072969 + 3 ^ 40 * 2782541 * 2
def baseEnd_2782541 : Nat := 952520649228202019493889

theorem tailTrace_2782541 : CollatzResearch.WordTrace tailWord_2782541 prefixEnd_2782541 952520649228202019493889 := by
  unfold tailWord_2782541
  simp only [CollatzResearch.WordTrace]
  refine ⟨101487607812336652013699477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67658405208224434675799651 101487607812336652013699477)
  ·
    refine ⟨4757231616203280563142163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101487607812336652013699477 4757231616203280563142163)
    ·
      refine ⟨7135847424304920844713245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757231616203280563142163 7135847424304920844713245)
      ·
        refine ⟨2675942784114345316767467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7135847424304920844713245 2675942784114345316767467)
        ·
          refine ⟨4013914176171517975151201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675942784114345316767467 4013914176171517975151201)
          ·
            refine ⟨3010435632128638481363401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4013914176171517975151201 3010435632128638481363401)
            ·
              refine ⟨2257826724096478861022551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010435632128638481363401 2257826724096478861022551)
              ·
                refine ⟨3386740086144718291533827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257826724096478861022551 3386740086144718291533827)
                ·
                  refine ⟨5080110129217077437300741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3386740086144718291533827 5080110129217077437300741)
                  ·
                    refine ⟨952520649228202019493889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080110129217077437300741 952520649228202019493889)
                    ·
                      rfl

theorem cell22_2782541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2782541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782541 prefixEnd_2782541 := by exact prefixLift 2782541
  have htrace : WordTrace (prefixWord ++ tailWord_2782541) baseStart_2782541 baseEnd_2782541 := by
    simpa [prefixWord, tailWord_2782541, baseEnd_2782541] using wordTrace_append hprefix tailTrace_2782541
  have hstable : (prefixWord ++ tailWord_2782541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782541).length < 2 ^ (prefixWord ++ tailWord_2782541).sum := by decide
  have hdescent : baseEnd_2782541 < baseStart_2782541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782565 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_2782565 : Nat := 118140960795 + 2782565 * 2 ^ 59
def prefixEnd_2782565 : Nat := 4983230072969 + 3 ^ 40 * 2782565 * 2
def baseEnd_2782565 : Nat := 952528864918673956893815

theorem tailTrace_2782565 : CollatzResearch.WordTrace tailWord_2782565 prefixEnd_2782565 952528864918673956893815 := by
  unfold tailWord_2782565
  simp only [CollatzResearch.WordTrace]
  refine ⟨101488483164249704112573149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67658988776166469408382099 101488483164249704112573149)
  ·
    refine ⟨38058181186593639042214931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101488483164249704112573149 38058181186593639042214931)
    ·
      refine ⟨57087271779890458563322397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38058181186593639042214931 57087271779890458563322397)
      ·
        refine ⟨21407726917458921961245899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57087271779890458563322397 21407726917458921961245899)
        ·
          refine ⟨32111590376188382941868849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21407726917458921961245899 32111590376188382941868849)
          ·
            refine ⟨24083692782141287206401637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32111590376188382941868849 24083692782141287206401637)
            ·
              refine ⟨4515692396651491351200307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24083692782141287206401637 4515692396651491351200307)
              ·
                refine ⟨6773538594977237026800461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515692396651491351200307 6773538594977237026800461)
                ·
                  refine ⟨2540076973116463885050173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6773538594977237026800461 2540076973116463885050173)
                  ·
                    refine ⟨952528864918673956893815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540076973116463885050173 952528864918673956893815)
                    ·
                      rfl

theorem cell22_2782565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_2782565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782565 prefixEnd_2782565 := by exact prefixLift 2782565
  have htrace : WordTrace (prefixWord ++ tailWord_2782565) baseStart_2782565 baseEnd_2782565 := by
    simpa [prefixWord, tailWord_2782565, baseEnd_2782565] using wordTrace_append hprefix tailTrace_2782565
  have hstable : (prefixWord ++ tailWord_2782565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782565).length < 2 ^ (prefixWord ++ tailWord_2782565).sum := by decide
  have hdescent : baseEnd_2782565 < baseStart_2782565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782599 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 1, 3]
def baseStart_2782599 : Nat := 118140960795 + 2782599 * 2 ^ 59
def prefixEnd_2782599 : Nat := 4983230072969 + 3 ^ 40 * 2782599 * 2
def baseEnd_2782599 : Nat := 952540503813509201543711

theorem tailTrace_2782599 : CollatzResearch.WordTrace tailWord_2782599 prefixEnd_2782599 952540503813509201543711 := by
  unfold tailWord_2782599
  simp only [CollatzResearch.WordTrace]
  refine ⟨101489723246126527919310851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67659815497417685279540567 101489723246126527919310851)
  ·
    refine ⟨152234584869189791878966277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101489723246126527919310851 152234584869189791878966277)
    ·
      refine ⟨28543984662973085977306177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152234584869189791878966277 28543984662973085977306177)
      ·
        refine ⟨21407988497229814482979633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28543984662973085977306177 21407988497229814482979633)
        ·
          refine ⟨16055991372922360862234725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21407988497229814482979633 16055991372922360862234725)
          ·
            refine ⟨3010498382422942661669011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16055991372922360862234725 3010498382422942661669011)
            ·
              refine ⟨4515747573634413992503517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010498382422942661669011 4515747573634413992503517)
              ·
                refine ⟨1693405340112905247188819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4515747573634413992503517 1693405340112905247188819)
                ·
                  refine ⟨2540108010169357870783229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693405340112905247188819 2540108010169357870783229)
                  ·
                    refine ⟨952540503813509201543711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540108010169357870783229 952540503813509201543711)
                    ·
                      rfl

theorem cell22_2782599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_2782599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782599 prefixEnd_2782599 := by exact prefixLift 2782599
  have htrace : WordTrace (prefixWord ++ tailWord_2782599) baseStart_2782599 baseEnd_2782599 := by
    simpa [prefixWord, tailWord_2782599, baseEnd_2782599] using wordTrace_append hprefix tailTrace_2782599
  have hstable : (prefixWord ++ tailWord_2782599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782599).length < 2 ^ (prefixWord ++ tailWord_2782599).sum := by decide
  have hdescent : baseEnd_2782599 < baseStart_2782599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782616 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 1, 3]
def baseStart_2782616 : Nat := 118140960795 + 2782616 * 2 ^ 59
def prefixEnd_2782616 : Nat := 4983230072969 + 3 ^ 40 * 2782616 * 2
def baseEnd_2782616 : Nat := 952546323260926823868659

theorem tailTrace_2782616 : CollatzResearch.WordTrace tailWord_2782616 prefixEnd_2782616 952546323260926823868659 := by
  unfold tailWord_2782616
  simp only [CollatzResearch.WordTrace]
  refine ⟨50745171643532469911339851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67660228858043293215119801 50745171643532469911339851)
  ·
    refine ⟨76117757465298704867009777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50745171643532469911339851 76117757465298704867009777)
    ·
      refine ⟨57088318098974028650257333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76117757465298704867009777 57088318098974028650257333)
      ·
        refine ⟨5352029821778815185961625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57088318098974028650257333 5352029821778815185961625)
        ·
          refine ⟨4014022366334111389471219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5352029821778815185961625 4014022366334111389471219)
          ·
            refine ⟨6021033549501167084206829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014022366334111389471219 6021033549501167084206829)
            ·
              refine ⟨2257887581062937656577561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6021033549501167084206829 2257887581062937656577561)
              ·
                refine ⟨1693415685797203242433171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257887581062937656577561 1693415685797203242433171)
                ·
                  refine ⟨2540123528695804863649757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693415685797203242433171 2540123528695804863649757)
                  ·
                    refine ⟨952546323260926823868659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540123528695804863649757 952546323260926823868659)
                    ·
                      rfl

theorem cell22_2782616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_2782616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782616 prefixEnd_2782616 := by exact prefixLift 2782616
  have htrace : WordTrace (prefixWord ++ tailWord_2782616) baseStart_2782616 baseEnd_2782616 := by
    simpa [prefixWord, tailWord_2782616, baseEnd_2782616] using wordTrace_append hprefix tailTrace_2782616
  have hstable : (prefixWord ++ tailWord_2782616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782616).length < 2 ^ (prefixWord ++ tailWord_2782616).sum := by decide
  have hdescent : baseEnd_2782616 < baseStart_2782616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782668 : List Nat := [2, 2, 1, 4, 2, 11]
def baseStart_2782668 : Nat := 118140960795 + 2782668 * 2 ^ 59
def prefixEnd_2782668 : Nat := 4983230072969 + 3 ^ 40 * 2782668 * 2
def baseEnd_2782668 : Nat := 11760050912637234834179

theorem tailTrace_2782668 : CollatzResearch.WordTrace tailWord_2782668 prefixEnd_2782668 11760050912637234834179 := by
  unfold tailWord_2782668
  simp only [CollatzResearch.WordTrace]
  refine ⟨50746119941438276351786329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67661493255251035135715105 50746119941438276351786329)
  ·
    refine ⟨38059589956078707263839747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50746119941438276351786329 38059589956078707263839747)
    ·
      refine ⟨57089384934118060895759621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38059589956078707263839747 57089384934118060895759621)
      ·
        refine ⟨10704259675147136417954929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57089384934118060895759621 10704259675147136417954929)
        ·
          refine ⟨8028194756360352313466197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10704259675147136417954929 8028194756360352313466197)
          ·
            refine ⟨11760050912637234834179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8028194756360352313466197 11760050912637234834179)
            ·
              rfl

theorem cell22_2782668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 11].length) (baseStart_2782668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782668 prefixEnd_2782668 := by exact prefixLift 2782668
  have htrace : WordTrace (prefixWord ++ tailWord_2782668) baseStart_2782668 baseEnd_2782668 := by
    simpa [prefixWord, tailWord_2782668, baseEnd_2782668] using wordTrace_append hprefix tailTrace_2782668
  have hstable : (prefixWord ++ tailWord_2782668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782668).length < 2 ^ (prefixWord ++ tailWord_2782668).sum := by decide
  have hdescent : baseEnd_2782668 < baseStart_2782668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782670 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_2782670 : Nat := 118140960795 + 2782670 * 2 ^ 59
def prefixEnd_2782670 : Nat := 4983230072969 + 3 ^ 40 * 2782670 * 2
def baseEnd_2782670 : Nat := 952564808564488683018493

theorem tailTrace_2782670 : CollatzResearch.WordTrace tailWord_2782670 prefixEnd_2782670 952564808564488683018493 := by
  unfold tailWord_2782670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686539103608663380643183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67661541885912871363430309 12686539103608663380643183)
  ·
    refine ⟨19029808655412995070964775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12686539103608663380643183 19029808655412995070964775)
    ·
      refine ⟨28544712983119492606447163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19029808655412995070964775 28544712983119492606447163)
      ·
        refine ⟨42817069474679238909670745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28544712983119492606447163 42817069474679238909670745)
        ·
          refine ⟨32112802106009429182253059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42817069474679238909670745 32112802106009429182253059)
          ·
            refine ⟨48169203159014143773379589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32112802106009429182253059 48169203159014143773379589)
            ·
              refine ⟨9031725592315151957508673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48169203159014143773379589 9031725592315151957508673)
              ·
                refine ⟨6773794194236363968131505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9031725592315151957508673 6773794194236363968131505)
                ·
                  refine ⟨5080345645677272976098629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6773794194236363968131505 5080345645677272976098629)
                  ·
                    refine ⟨952564808564488683018493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080345645677272976098629 952564808564488683018493)
                    ·
                      rfl

theorem cell22_2782670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_2782670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782670 prefixEnd_2782670 := by exact prefixLift 2782670
  have htrace : WordTrace (prefixWord ++ tailWord_2782670) baseStart_2782670 baseEnd_2782670 := by
    simpa [prefixWord, tailWord_2782670, baseEnd_2782670] using wordTrace_append hprefix tailTrace_2782670
  have hstable : (prefixWord ++ tailWord_2782670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782670).length < 2 ^ (prefixWord ++ tailWord_2782670).sum := by decide
  have hdescent : baseEnd_2782670 < baseStart_2782670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782685 : List Nat := [1, 4, 3, 1, 1, 2, 3, 7]
def baseStart_2782685 : Nat := 118140960795 + 2782685 * 2 ^ 59
def prefixEnd_2782685 : Nat := 4983230072969 + 3 ^ 40 * 2782685 * 2
def baseEnd_2782685 : Nat := 105841104819003738210383

theorem tailTrace_2782685 : CollatzResearch.WordTrace tailWord_2782685 prefixEnd_2782685 105841104819003738210383 := by
  unfold tailWord_2782685
  simp only [CollatzResearch.WordTrace]
  refine ⟨101492859923814964606941509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67661906615876643071294339 101492859923814964606941509)
  ·
    refine ⟨19029911235715305863801533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101492859923814964606941509 19029911235715305863801533)
    ·
      refine ⟨7136216713393239698925575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19029911235715305863801533 7136216713393239698925575)
      ·
        refine ⟨10704325070089859548388363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136216713393239698925575 10704325070089859548388363)
        ·
          refine ⟨16056487605134789322582545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10704325070089859548388363 16056487605134789322582545)
          ·
            refine ⟨12042365703851091991936909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16056487605134789322582545 12042365703851091991936909)
            ·
              refine ⟨4515887138944159496976341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12042365703851091991936909 4515887138944159496976341)
              ·
                refine ⟨105841104819003738210383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4515887138944159496976341 105841104819003738210383)
                ·
                  rfl

theorem cell22_2782685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 7].length) (baseStart_2782685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782685 prefixEnd_2782685 := by exact prefixLift 2782685
  have htrace : WordTrace (prefixWord ++ tailWord_2782685) baseStart_2782685 baseEnd_2782685 := by
    simpa [prefixWord, tailWord_2782685, baseEnd_2782685] using wordTrace_append hprefix tailTrace_2782685
  have hstable : (prefixWord ++ tailWord_2782685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782685).length < 2 ^ (prefixWord ++ tailWord_2782685).sum := by decide
  have hdescent : baseEnd_2782685 < baseStart_2782685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782713 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 7]
def baseStart_2782713 : Nat := 118140960795 + 2782713 * 2 ^ 59
def prefixEnd_2782713 : Nat := 4983230072969 + 3 ^ 40 * 2782713 * 2
def baseEnd_2782713 : Nat := 317526509447750301397787

theorem tailTrace_2782713 : CollatzResearch.WordTrace tailWord_2782713 prefixEnd_2782713 317526509447750301397787 := by
  unfold tailWord_2782713
  simp only [CollatzResearch.WordTrace]
  refine ⟨101493881167713525388960793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67662587445142350259307195 101493881167713525388960793)
  ·
    refine ⟨76120410875785144041720595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101493881167713525388960793 76120410875785144041720595)
    ·
      refine ⟨114180616313677716062580893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76120410875785144041720595 114180616313677716062580893)
      ·
        refine ⟨42817731117629143523467835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114180616313677716062580893 42817731117629143523467835)
        ·
          refine ⟨64226596676443715285201753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42817731117629143523467835 64226596676443715285201753)
          ·
            refine ⟨48169947507332786463901315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64226596676443715285201753 48169947507332786463901315)
            ·
              refine ⟨72254921260999179695851973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48169947507332786463901315 72254921260999179695851973)
              ·
                refine ⟨13547797736437346192972245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72254921260999179695851973 13547797736437346192972245)
                ·
                  refine ⟨317526509447750301397787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13547797736437346192972245 317526509447750301397787)
                  ·
                    rfl

theorem cell22_2782713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_2782713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782713 prefixEnd_2782713 := by exact prefixLift 2782713
  have htrace : WordTrace (prefixWord ++ tailWord_2782713) baseStart_2782713 baseEnd_2782713 := by
    simpa [prefixWord, tailWord_2782713, baseEnd_2782713] using wordTrace_append hprefix tailTrace_2782713
  have hstable : (prefixWord ++ tailWord_2782713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782713).length < 2 ^ (prefixWord ++ tailWord_2782713).sum := by decide
  have hdescent : baseEnd_2782713 < baseStart_2782713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782730 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_2782730 : Nat := 118140960795 + 2782730 * 2 ^ 59
def prefixEnd_2782730 : Nat := 4983230072969 + 3 ^ 40 * 2782730 * 2
def baseEnd_2782730 : Nat := 317528449263556175506103

theorem tailTrace_2782730 : CollatzResearch.WordTrace tailWord_2782730 prefixEnd_2782730 317528449263556175506103 := by
  unfold tailWord_2782730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25373625302162984323082411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67663000805767958194886429 25373625302162984323082411)
  ·
    refine ⟨38060437953244476484623617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25373625302162984323082411 38060437953244476484623617)
    ·
      refine ⟨28545328464933357363467713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38060437953244476484623617 28545328464933357363467713)
      ·
        refine ⟨21408996348700018022600785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28545328464933357363467713 21408996348700018022600785)
        ·
          refine ⟨16056747261525013516950589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21408996348700018022600785 16056747261525013516950589)
          ·
            refine ⟨6021280223071880068856471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16056747261525013516950589 6021280223071880068856471)
            ·
              refine ⟨9031920334607820103284707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021280223071880068856471 9031920334607820103284707)
              ·
                refine ⟨13547880501911730154927061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031920334607820103284707 13547880501911730154927061)
                ·
                  refine ⟨317528449263556175506103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13547880501911730154927061 317528449263556175506103)
                  ·
                    rfl

theorem cell22_2782730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_2782730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782730 prefixEnd_2782730 := by exact prefixLift 2782730
  have htrace : WordTrace (prefixWord ++ tailWord_2782730) baseStart_2782730 baseEnd_2782730 := by
    simpa [prefixWord, tailWord_2782730, baseEnd_2782730] using wordTrace_append hprefix tailTrace_2782730
  have hstable : (prefixWord ++ tailWord_2782730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782730).length < 2 ^ (prefixWord ++ tailWord_2782730).sum := by decide
  have hdescent : baseEnd_2782730 < baseStart_2782730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782734 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_2782734 : Nat := 118140960795 + 2782734 * 2 ^ 59
def prefixEnd_2782734 : Nat := 4983230072969 + 3 ^ 40 * 2782734 * 2
def baseEnd_2782734 : Nat := 952586717072413849418297

theorem tailTrace_2782734 : CollatzResearch.WordTrace tailWord_2782734 prefixEnd_2782734 952586717072413849418297 := by
  unfold tailWord_2782734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686830887579680746934407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67663098067091630650316837 12686830887579680746934407)
  ·
    refine ⟨19030246331369521120401611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12686830887579680746934407 19030246331369521120401611)
    ·
      refine ⟨28545369497054281680602417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19030246331369521120401611 28545369497054281680602417)
      ·
        refine ⟨21409027122790711260451813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28545369497054281680602417 21409027122790711260451813)
        ·
          refine ⟨4014192585523258361334715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21409027122790711260451813 4014192585523258361334715)
          ·
            refine ⟨6021288878284887542002073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014192585523258361334715 6021288878284887542002073)
            ·
              refine ⟨4515966658713665656501555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6021288878284887542002073 4515966658713665656501555)
              ·
                refine ⟨6773949988070498484752333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515966658713665656501555 6773949988070498484752333)
                ·
                  refine ⟨2540231245526436931782125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6773949988070498484752333 2540231245526436931782125)
                  ·
                    refine ⟨952586717072413849418297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540231245526436931782125 952586717072413849418297)
                    ·
                      rfl

theorem cell22_2782734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_2782734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782734 prefixEnd_2782734 := by exact prefixLift 2782734
  have htrace : WordTrace (prefixWord ++ tailWord_2782734) baseStart_2782734 baseEnd_2782734 := by
    simpa [prefixWord, tailWord_2782734, baseEnd_2782734] using wordTrace_append hprefix tailTrace_2782734
  have hstable : (prefixWord ++ tailWord_2782734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782734).length < 2 ^ (prefixWord ++ tailWord_2782734).sum := by decide
  have hdescent : baseEnd_2782734 < baseStart_2782734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782777 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_2782777 : Nat := 118140960795 + 2782777 * 2 ^ 59
def prefixEnd_2782777 : Nat := 4983230072969 + 3 ^ 40 * 2782777 * 2
def baseEnd_2782777 : Nat := 952601436851176070593165

theorem tailTrace_2782777 : CollatzResearch.WordTrace tailWord_2782777 prefixEnd_2782777 952601436851176070593165 := by
  unfold tailWord_2782777
  simp only [CollatzResearch.WordTrace]
  refine ⟨101496215439481664319290585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67664143626321109546193723 101496215439481664319290585)
  ·
    refine ⟨76122161579611248239467939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101496215439481664319290585 76122161579611248239467939)
    ·
      refine ⟨114183242369416872359201909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76122161579611248239467939 114183242369416872359201909)
      ·
        refine ⟨10704678972132831783675179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114183242369416872359201909 10704678972132831783675179)
        ·
          refine ⟨16057018458199247675512769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10704678972132831783675179 16057018458199247675512769)
          ·
            refine ⟨12042763843649435756634577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16057018458199247675512769 12042763843649435756634577)
            ·
              refine ⟨9032072882737076817475933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12042763843649435756634577 9032072882737076817475933)
              ·
                refine ⟨3387027331026403806553475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9032072882737076817475933 3387027331026403806553475)
                ·
                  refine ⟨5080540996539605709830213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387027331026403806553475 5080540996539605709830213)
                  ·
                    refine ⟨952601436851176070593165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080540996539605709830213 952601436851176070593165)
                    ·
                      rfl

theorem cell22_2782777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_2782777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782777 prefixEnd_2782777 := by exact prefixLift 2782777
  have htrace : WordTrace (prefixWord ++ tailWord_2782777) baseStart_2782777 baseEnd_2782777 := by
    simpa [prefixWord, tailWord_2782777, baseEnd_2782777] using wordTrace_append hprefix tailTrace_2782777
  have hstable : (prefixWord ++ tailWord_2782777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782777).length < 2 ^ (prefixWord ++ tailWord_2782777).sum := by decide
  have hdescent : baseEnd_2782777 < baseStart_2782777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782805 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2782805 : Nat := 118140960795 + 2782805 * 2 ^ 59
def prefixEnd_2782805 : Nat := 4983230072969 + 3 ^ 40 * 2782805 * 2
def baseEnd_2782805 : Nat := 952611021823393330893079

theorem tailTrace_2782805 : CollatzResearch.WordTrace tailWord_2782805 prefixEnd_2782805 952611021823393330893079 := by
  unfold tailWord_2782805
  simp only [CollatzResearch.WordTrace]
  refine ⟨101497236683380225101309869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67664824455586816734206579 101497236683380225101309869)
  ·
    refine ⟨38061463756267584412991201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101497236683380225101309869 38061463756267584412991201)
    ·
      refine ⟨28546097817200688309743401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38061463756267584412991201 28546097817200688309743401)
      ·
        refine ⟨21409573362900516232307551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28546097817200688309743401 21409573362900516232307551)
        ·
          refine ⟨32114360044350774348461327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21409573362900516232307551 32114360044350774348461327)
          ·
            refine ⟨48171540066526161522691991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32114360044350774348461327 48171540066526161522691991)
            ·
              refine ⟨72257310099789242284037987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48171540066526161522691991 72257310099789242284037987)
              ·
                refine ⟨108385965149683863426056981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72257310099789242284037987 108385965149683863426056981)
                ·
                  refine ⟨5080592116391431098096421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108385965149683863426056981 5080592116391431098096421)
                  ·
                    refine ⟨952611021823393330893079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080592116391431098096421 952611021823393330893079)
                    ·
                      rfl

theorem cell22_2782805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2782805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782805 prefixEnd_2782805 := by exact prefixLift 2782805
  have htrace : WordTrace (prefixWord ++ tailWord_2782805) baseStart_2782805 baseEnd_2782805 := by
    simpa [prefixWord, tailWord_2782805, baseEnd_2782805] using wordTrace_append hprefix tailTrace_2782805
  have hstable : (prefixWord ++ tailWord_2782805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782805).length < 2 ^ (prefixWord ++ tailWord_2782805).sum := by decide
  have hdescent : baseEnd_2782805 < baseStart_2782805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782820 : List Nat := [2, 3, 1, 1, 2, 3, 2, 8]
def baseStart_2782820 : Nat := 118140960795 + 2782820 * 2 ^ 59
def prefixEnd_2782820 : Nat := 4983230072969 + 3 ^ 40 * 2782820 * 2
def baseEnd_2782820 : Nat := 105846239625548699085337

theorem tailTrace_2782820 : CollatzResearch.WordTrace tailWord_2782820 prefixEnd_2782820 105846239625548699085337 := by
  unfold tailWord_2782820
  simp only [CollatzResearch.WordTrace]
  refine ⟨50748891889162941331552957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67665189185550588442070609 50748891889162941331552957)
  ·
    refine ⟨19030834458436102999332359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50748891889162941331552957 19030834458436102999332359)
    ·
      refine ⟨28546251687654154498998539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19030834458436102999332359 28546251687654154498998539)
      ·
        refine ⟨42819377531481231748497809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28546251687654154498998539 42819377531481231748497809)
        ·
          refine ⟨32114533148610923811373357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42819377531481231748497809 32114533148610923811373357)
          ·
            refine ⟨12042949930729096429265009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32114533148610923811373357 12042949930729096429265009)
            ·
              refine ⟨9032212448046822321948757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12042949930729096429265009 9032212448046822321948757)
              ·
                refine ⟨105846239625548699085337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9032212448046822321948757 105846239625548699085337)
                ·
                  rfl

theorem cell22_2782820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_2782820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782820 prefixEnd_2782820 := by exact prefixLift 2782820
  have htrace : WordTrace (prefixWord ++ tailWord_2782820) baseStart_2782820 baseEnd_2782820 := by
    simpa [prefixWord, tailWord_2782820, baseEnd_2782820] using wordTrace_append hprefix tailTrace_2782820
  have hstable : (prefixWord ++ tailWord_2782820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782820).length < 2 ^ (prefixWord ++ tailWord_2782820).sum := by decide
  have hdescent : baseEnd_2782820 < baseStart_2782820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782929 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2782929 : Nat := 118140960795 + 2782929 * 2 ^ 59
def prefixEnd_2782929 : Nat := 4983230072969 + 3 ^ 40 * 2782929 * 2
def baseEnd_2782929 : Nat := 952653469557498340792699

theorem tailTrace_2782929 : CollatzResearch.WordTrace tailWord_2782929 prefixEnd_2782929 952653469557498340792699 := by
  unfold tailWord_2782929
  simp only [CollatzResearch.WordTrace]
  refine ⟨101501759334930994278823841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67667839556620662852549227 101501759334930994278823841)
  ·
    refine ⟨76126319501198245709117881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101501759334930994278823841 76126319501198245709117881)
    ·
      refine ⟨57094739625898684281838411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76126319501198245709117881 57094739625898684281838411)
      ·
        refine ⟨85642109438848026422757617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57094739625898684281838411 85642109438848026422757617)
        ·
          refine ⟨64231582079136019817068213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85642109438848026422757617 64231582079136019817068213)
          ·
            refine ⟨6021710819919001857850145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64231582079136019817068213 6021710819919001857850145)
            ·
              refine ⟨4516283114939251393387609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6021710819919001857850145 4516283114939251393387609)
              ·
                refine ⟨3387212336204438545040707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4516283114939251393387609 3387212336204438545040707)
                ·
                  refine ⟨5080818504306657817561061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3387212336204438545040707 5080818504306657817561061)
                  ·
                    refine ⟨952653469557498340792699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5080818504306657817561061 952653469557498340792699)
                    ·
                      rfl

theorem cell22_2782929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2782929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782929 prefixEnd_2782929 := by exact prefixLift 2782929
  have htrace : WordTrace (prefixWord ++ tailWord_2782929) baseStart_2782929 baseEnd_2782929 := by
    simpa [prefixWord, tailWord_2782929, baseEnd_2782929] using wordTrace_append hprefix tailTrace_2782929
  have hstable : (prefixWord ++ tailWord_2782929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782929).length < 2 ^ (prefixWord ++ tailWord_2782929).sum := by decide
  have hdescent : baseEnd_2782929 < baseStart_2782929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782944 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 4]
def baseStart_2782944 : Nat := 118140960795 + 2782944 * 2 ^ 59
def prefixEnd_2782944 : Nat := 4983230072969 + 3 ^ 40 * 2782944 * 2
def baseEnd_2782944 : Nat := 317552868121347767222551

theorem tailTrace_2782944 : CollatzResearch.WordTrace tailWord_2782944 prefixEnd_2782944 317552868121347767222551 := by
  unfold tailWord_2782944
  simp only [CollatzResearch.WordTrace]
  refine ⟨50751153214938325920309943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67668204286584434560413257 50751153214938325920309943)
  ·
    refine ⟨76126729822407488880464915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50751153214938325920309943 76126729822407488880464915)
    ·
      refine ⟨114190094733611233320697373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76126729822407488880464915 114190094733611233320697373)
      ·
        refine ⟨42821285525104212495261515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114190094733611233320697373 42821285525104212495261515)
        ·
          refine ⟨64231928287656318742892273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42821285525104212495261515 64231928287656318742892273)
          ·
            refine ⟨48173946215742239057169205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64231928287656318742892273 48173946215742239057169205)
            ·
              refine ⟨4516307457725834911609613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48173946215742239057169205 4516307457725834911609613)
              ·
                refine ⟨1693615296647188091853605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4516307457725834911609613 1693615296647188091853605)
                ·
                  refine ⟨317552868121347767222551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693615296647188091853605 317552868121347767222551)
                  ·
                    rfl

theorem cell22_2782944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_2782944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782944 prefixEnd_2782944 := by exact prefixLift 2782944
  have htrace : WordTrace (prefixWord ++ tailWord_2782944) baseStart_2782944 baseEnd_2782944 := by
    simpa [prefixWord, tailWord_2782944, baseEnd_2782944] using wordTrace_append hprefix tailTrace_2782944
  have hstable : (prefixWord ++ tailWord_2782944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782944).length < 2 ^ (prefixWord ++ tailWord_2782944).sum := by decide
  have hdescent : baseEnd_2782944 < baseStart_2782944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782955 : List Nat := [1, 1, 1, 1, 2, 4, 12]
def baseStart_2782955 : Nat := 118140960795 + 2782955 * 2 ^ 59
def prefixEnd_2782955 : Nat := 4983230072969 + 3 ^ 40 * 2782955 * 2
def baseEnd_2782955 : Nat := 35283791477364553320097

theorem tailTrace_2782955 : CollatzResearch.WordTrace tailWord_2782955 prefixEnd_2782955 35283791477364553320097 := by
  unfold tailWord_2782955
  simp only [CollatzResearch.WordTrace]
  refine ⟨101502707632836800719270319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67668471755224533812846879 101502707632836800719270319)
  ·
    refine ⟨152254061449255201078905479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101502707632836800719270319 152254061449255201078905479)
    ·
      refine ⟨228381092173882801618358219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152254061449255201078905479 228381092173882801618358219)
      ·
        refine ⟨342571638260824202427537329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228381092173882801618358219 342571638260824202427537329)
        ·
          refine ⟨256928728695618151820652997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342571638260824202427537329 256928728695618151820652997)
          ·
            refine ⟨48174136630428403466372437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256928728695618151820652997 48174136630428403466372437)
            ·
              refine ⟨35283791477364553320097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 48174136630428403466372437 35283791477364553320097)
              ·
                rfl

theorem cell22_2782955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 12].length) (baseStart_2782955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782955 prefixEnd_2782955 := by exact prefixLift 2782955
  have htrace : WordTrace (prefixWord ++ tailWord_2782955) baseStart_2782955 baseEnd_2782955 := by
    simpa [prefixWord, tailWord_2782955, baseEnd_2782955] using wordTrace_append hprefix tailTrace_2782955
  have hstable : (prefixWord ++ tailWord_2782955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782955).length < 2 ^ (prefixWord ++ tailWord_2782955).sum := by decide
  have hdescent : baseEnd_2782955 < baseStart_2782955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782959 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 2, 3]
def baseStart_2782959 : Nat := 118140960795 + 2782959 * 2 ^ 59
def prefixEnd_2782959 : Nat := 4983230072969 + 3 ^ 40 * 2782959 * 2
def baseEnd_2782959 : Nat := 952663739170588262542607

theorem tailTrace_2782959 : CollatzResearch.WordTrace tailWord_2782959 prefixEnd_2782959 952663739170588262542607 := by
  unfold tailWord_2782959
  simp only [CollatzResearch.WordTrace]
  refine ⟨101502853524822309402415931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67668569016548206268277287 101502853524822309402415931)
  ·
    refine ⟨152254280287233464103623897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101502853524822309402415931 152254280287233464103623897)
    ·
      refine ⟨114190710215425098077717923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152254280287233464103623897 114190710215425098077717923)
      ·
        refine ⟨171286065323137647116576885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114190710215425098077717923 171286065323137647116576885)
        ·
          refine ⟨16058068624044154417179083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171286065323137647116576885 16058068624044154417179083)
          ·
            refine ⟨24087102936066231625768625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16058068624044154417179083 24087102936066231625768625)
            ·
              refine ⟨18065327202049673719326469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24087102936066231625768625 18065327202049673719326469)
              ·
                refine ⟨3387248850384313822373713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18065327202049673719326469 3387248850384313822373713)
                ·
                  refine ⟨2540436637788235366780285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3387248850384313822373713 2540436637788235366780285)
                  ·
                    refine ⟨952663739170588262542607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540436637788235366780285 952663739170588262542607)
                    ·
                      rfl

theorem cell22_2782959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_2782959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782959 prefixEnd_2782959 := by exact prefixLift 2782959
  have htrace : WordTrace (prefixWord ++ tailWord_2782959) baseStart_2782959 baseEnd_2782959 := by
    simpa [prefixWord, tailWord_2782959, baseEnd_2782959] using wordTrace_append hprefix tailTrace_2782959
  have hstable : (prefixWord ++ tailWord_2782959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782959).length < 2 ^ (prefixWord ++ tailWord_2782959).sum := by decide
  have hdescent : baseEnd_2782959 < baseStart_2782959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782961 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 4]
def baseStart_2782961 : Nat := 118140960795 + 2782961 * 2 ^ 59
def prefixEnd_2782961 : Nat := 4983230072969 + 3 ^ 40 * 2782961 * 2
def baseEnd_2782961 : Nat := 317554807937153641330867

theorem tailTrace_2782961 : CollatzResearch.WordTrace tailWord_2782961 prefixEnd_2782961 317554807937153641330867 := by
  unfold tailWord_2782961
  simp only [CollatzResearch.WordTrace]
  refine ⟨101502926470815063743988737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67668617647210042495992491 101502926470815063743988737)
  ·
    refine ⟨76127194853111297807991553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101502926470815063743988737 76127194853111297807991553)
    ·
      refine ⟨57095396139833473355993665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76127194853111297807991553 57095396139833473355993665)
      ·
        refine ⟨42821547104875105016995249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57095396139833473355993665 42821547104875105016995249)
        ·
          refine ⟨32116160328656328762746437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42821547104875105016995249 32116160328656328762746437)
          ·
            refine ⟨6021780061623061643014957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32116160328656328762746437 6021780061623061643014957)
            ·
              refine ⟨2258167523108648116130609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6021780061623061643014957 2258167523108648116130609)
              ·
                refine ⟨1693625642331486087097957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258167523108648116130609 1693625642331486087097957)
                ·
                  refine ⟨317554807937153641330867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693625642331486087097957 317554807937153641330867)
                  ·
                    rfl

theorem cell22_2782961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_2782961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782961 prefixEnd_2782961 := by exact prefixLift 2782961
  have htrace : WordTrace (prefixWord ++ tailWord_2782961) baseStart_2782961 baseEnd_2782961 := by
    simpa [prefixWord, tailWord_2782961, baseEnd_2782961] using wordTrace_append hprefix tailTrace_2782961
  have hstable : (prefixWord ++ tailWord_2782961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782961).length < 2 ^ (prefixWord ++ tailWord_2782961).sum := by decide
  have hdescent : baseEnd_2782961 < baseStart_2782961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2782972 : List Nat := [2, 2, 2, 1, 3, 1, 4, 7]
def baseStart_2782972 : Nat := 118140960795 + 2782972 * 2 ^ 59
def prefixEnd_2782972 : Nat := 4983230072969 + 3 ^ 40 * 2782972 * 2
def baseEnd_2782972 : Nat := 105852021037362284663063

theorem tailTrace_2782972 : CollatzResearch.WordTrace tailWord_2782972 prefixEnd_2782972 105852021037362284663063 := by
  unfold tailWord_2782972
  simp only [CollatzResearch.WordTrace]
  refine ⟨50751663836887606311319585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67668885115850141748426113 50751663836887606311319585)
  ·
    refine ⟨38063747877665704733489689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50751663836887606311319585 38063747877665704733489689)
    ·
      refine ⟨28547810908249278550117267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38063747877665704733489689 28547810908249278550117267)
      ·
        refine ⟨42821716362373917825175901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28547810908249278550117267 42821716362373917825175901)
        ·
          refine ⟨16058143635890219184440963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42821716362373917825175901 16058143635890219184440963)
          ·
            refine ⟨24087215453835328776661445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16058143635890219184440963 24087215453835328776661445)
            ·
              refine ⟨4516352897594124145624021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24087215453835328776661445 4516352897594124145624021)
              ·
                refine ⟨105852021037362284663063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4516352897594124145624021 105852021037362284663063)
                ·
                  rfl

theorem cell22_2782972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_2782972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2782972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2782972 prefixEnd_2782972 := by exact prefixLift 2782972
  have htrace : WordTrace (prefixWord ++ tailWord_2782972) baseStart_2782972 baseEnd_2782972 := by
    simpa [prefixWord, tailWord_2782972, baseEnd_2782972] using wordTrace_append hprefix tailTrace_2782972
  have hstable : (prefixWord ++ tailWord_2782972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2782972).length < 2 ^ (prefixWord ++ tailWord_2782972).sum := by decide
  have hdescent : baseEnd_2782972 < baseStart_2782972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2782972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783006 : List Nat := [4, 3, 2, 2, 1, 10]
def baseStart_2783006 : Nat := 118140960795 + 2783006 * 2 ^ 59
def prefixEnd_2783006 : Nat := 4983230072969 + 3 ^ 40 * 2783006 * 2
def baseEnd_2783006 : Nat := 11761479360877726007623

theorem tailTrace_2783006 : CollatzResearch.WordTrace tailWord_2783006 prefixEnd_2783006 11761479360877726007623 := by
  unfold tailWord_2783006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12688070969456504553672109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67669711837101357619584581 12688070969456504553672109)
  ·
    refine ⟨4758026613546189207627041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12688070969456504553672109 4758026613546189207627041)
    ·
      refine ⟨3568519960159641905720281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4758026613546189207627041 3568519960159641905720281)
      ·
        refine ⟨2676389970119731429290211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3568519960159641905720281 2676389970119731429290211)
        ·
          refine ⟨4014584955179597143935317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676389970119731429290211 4014584955179597143935317)
          ·
            refine ⟨11761479360877726007623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4014584955179597143935317 11761479360877726007623)
            ·
              rfl

theorem cell22_2783006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 10].length) (baseStart_2783006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783006 prefixEnd_2783006 := by exact prefixLift 2783006
  have htrace : WordTrace (prefixWord ++ tailWord_2783006) baseStart_2783006 baseEnd_2783006 := by
    simpa [prefixWord, tailWord_2783006, baseEnd_2783006] using wordTrace_append hprefix tailTrace_2783006
  have hstable : (prefixWord ++ tailWord_2783006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783006).length < 2 ^ (prefixWord ++ tailWord_2783006).sum := by decide
  have hdescent : baseEnd_2783006 < baseStart_2783006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783032 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_2783032 : Nat := 118140960795 + 2783032 * 2 ^ 59
def prefixEnd_2783032 : Nat := 4983230072969 + 3 ^ 40 * 2783032 * 2
def baseEnd_2783032 : Nat := 952688728562440405467383

theorem tailTrace_2783032 : CollatzResearch.WordTrace tailWord_2783032 prefixEnd_2783032 952688728562440405467383 := by
  unfold tailWord_2783032
  simp only [CollatzResearch.WordTrace]
  refine ⟨50752758026778921434911675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67670344035705228579882233 50752758026778921434911675)
  ·
    refine ⟨76129137040168382152367513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50752758026778921434911675 76129137040168382152367513)
    ·
      refine ⟨57096852780126286614275635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76129137040168382152367513 57096852780126286614275635)
      ·
        refine ⟨85645279170189429921413453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57096852780126286614275635 85645279170189429921413453)
        ·
          refine ⟨32116979688821036220530045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85645279170189429921413453 32116979688821036220530045)
          ·
            refine ⟨12043867383307888582698767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32116979688821036220530045 12043867383307888582698767)
            ·
              refine ⟨18065801074961832874048151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12043867383307888582698767 18065801074961832874048151)
              ·
                refine ⟨27098701612442749311072227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18065801074961832874048151 27098701612442749311072227)
                ·
                  refine ⟨40648052418664123966608341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27098701612442749311072227 40648052418664123966608341)
                  ·
                    refine ⟨952688728562440405467383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40648052418664123966608341 952688728562440405467383)
                    ·
                      rfl

theorem cell22_2783032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_2783032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783032 prefixEnd_2783032 := by exact prefixLift 2783032
  have htrace : WordTrace (prefixWord ++ tailWord_2783032) baseStart_2783032 baseEnd_2783032 := by
    simpa [prefixWord, tailWord_2783032, baseEnd_2783032] using wordTrace_append hprefix tailTrace_2783032
  have hstable : (prefixWord ++ tailWord_2783032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783032).length < 2 ^ (prefixWord ++ tailWord_2783032).sum := by decide
  have hdescent : baseEnd_2783032 < baseStart_2783032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783034 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_2783034 : Nat := 118140960795 + 2783034 * 2 ^ 59
def prefixEnd_2783034 : Nat := 4983230072969 + 3 ^ 40 * 2783034 * 2
def baseEnd_2783034 : Nat := 317563137734437688972459

theorem tailTrace_2783034 : CollatzResearch.WordTrace tailWord_2783034 prefixEnd_2783034 317563137734437688972459 := by
  unfold tailWord_2783034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25376397249887649302849039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67670392666367064807597437 25376397249887649302849039)
  ·
    refine ⟨38064595874831473954273559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25376397249887649302849039 38064595874831473954273559)
    ·
      refine ⟨57096893812247210931410339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38064595874831473954273559 57096893812247210931410339)
      ·
        refine ⟨85645340718370816397115509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57096893812247210931410339 85645340718370816397115509)
        ·
          refine ⟨8029250692347264037229579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85645340718370816397115509 8029250692347264037229579)
          ·
            refine ⟨12043876038520896055844369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029250692347264037229579 12043876038520896055844369)
            ·
              refine ⟨9032907028890672041883277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12043876038520896055844369 9032907028890672041883277)
              ·
                refine ⟨3387340135834002015706229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9032907028890672041883277 3387340135834002015706229)
                ·
                  refine ⟨317563137734437688972459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387340135834002015706229 317563137734437688972459)
                  ·
                    rfl

theorem cell22_2783034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_2783034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783034 prefixEnd_2783034 := by exact prefixLift 2783034
  have htrace : WordTrace (prefixWord ++ tailWord_2783034) baseStart_2783034 baseEnd_2783034 := by
    simpa [prefixWord, tailWord_2783034, baseEnd_2783034] using wordTrace_append hprefix tailTrace_2783034
  have hstable : (prefixWord ++ tailWord_2783034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783034).length < 2 ^ (prefixWord ++ tailWord_2783034).sum := by decide
  have hdescent : baseEnd_2783034 < baseStart_2783034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783068 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 5]
def baseStart_2783068 : Nat := 118140960795 + 2783068 * 2 ^ 59
def prefixEnd_2783068 : Nat := 4983230072969 + 3 ^ 40 * 2783068 * 2
def baseEnd_2783068 : Nat := 317567017366049437189091

theorem tailTrace_2783068 : CollatzResearch.WordTrace tailWord_2783068 prefixEnd_2783068 317567017366049437189091 := by
  unfold tailWord_2783068
  simp only [CollatzResearch.WordTrace]
  refine ⟨50753414540713710509066929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67671219387618280678755905 50753414540713710509066929)
  ·
    refine ⟨38065060905535282881800197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50753414540713710509066929 38065060905535282881800197)
    ·
      refine ⟨7137198919787865540337537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38065060905535282881800197 7137198919787865540337537)
      ·
        refine ⟨5352899189840899155253153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7137198919787865540337537 5352899189840899155253153)
        ·
          refine ⟨4014674392380674366439865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5352899189840899155253153 4014674392380674366439865)
          ·
            refine ⟨3011005794285505774829899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4014674392380674366439865 3011005794285505774829899)
            ·
              refine ⟨4516508691428258662244849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011005794285505774829899 4516508691428258662244849)
              ·
                refine ⟨3387381518571193996683637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4516508691428258662244849 3387381518571193996683637)
                ·
                  refine ⟨317567017366049437189091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3387381518571193996683637 317567017366049437189091)
                  ·
                    rfl

theorem cell22_2783068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_2783068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783068 prefixEnd_2783068 := by exact prefixLift 2783068
  have htrace : WordTrace (prefixWord ++ tailWord_2783068) baseStart_2783068 baseEnd_2783068 := by
    simpa [prefixWord, tailWord_2783068, baseEnd_2783068] using wordTrace_append hprefix tailTrace_2783068
  have hstable : (prefixWord ++ tailWord_2783068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783068).length < 2 ^ (prefixWord ++ tailWord_2783068).sum := by decide
  have hdescent : baseEnd_2783068 < baseStart_2783068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783079 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 6]
def baseStart_2783079 : Nat := 118140960795 + 2783079 * 2 ^ 59
def prefixEnd_2783079 : Nat := 4983230072969 + 3 ^ 40 * 2783079 * 2
def baseEnd_2783079 : Nat := 317568272540982649847413

theorem tailTrace_2783079 : CollatzResearch.WordTrace tailWord_2783079 prefixEnd_2783079 317568272540982649847413 := by
  unfold tailWord_2783079
  simp only [CollatzResearch.WordTrace]
  refine ⟨101507230284387569896784291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67671486856258379931189527 101507230284387569896784291)
  ·
    refine ⟨152260845426581354845176437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101507230284387569896784291 152260845426581354845176437)
    ·
      refine ⟨14274454258742002016735291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152260845426581354845176437 14274454258742002016735291)
      ·
        refine ⟨21411681388113003025102937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14274454258742002016735291 21411681388113003025102937)
        ·
          refine ⟨16058761041084752268827203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21411681388113003025102937 16058761041084752268827203)
          ·
            refine ⟨24088141561627128403240805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16058761041084752268827203 24088141561627128403240805)
            ·
              refine ⟨4516526542805086575607651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24088141561627128403240805 4516526542805086575607651)
              ·
                refine ⟨6774789814207629863411477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4516526542805086575607651 6774789814207629863411477)
                ·
                  refine ⟨317568272540982649847413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6774789814207629863411477 317568272540982649847413)
                  ·
                    rfl

theorem cell22_2783079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 6].length) (baseStart_2783079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783079 prefixEnd_2783079 := by exact prefixLift 2783079
  have htrace : WordTrace (prefixWord ++ tailWord_2783079) baseStart_2783079 baseEnd_2783079 := by
    simpa [prefixWord, tailWord_2783079, baseEnd_2783079] using wordTrace_append hprefix tailTrace_2783079
  have hstable : (prefixWord ++ tailWord_2783079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783079).length < 2 ^ (prefixWord ++ tailWord_2783079).sum := by decide
  have hdescent : baseEnd_2783079 < baseStart_2783079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783109 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_2783109 : Nat := 118140960795 + 2783109 * 2 ^ 59
def prefixEnd_2783109 : Nat := 4983230072969 + 3 ^ 40 * 2783109 * 2
def baseEnd_2783109 : Nat := 952715087236037871292147

theorem tailTrace_2783109 : CollatzResearch.WordTrace tailWord_2783109 prefixEnd_2783109 952715087236037871292147 := by
  unfold tailWord_2783109
  simp only [CollatzResearch.WordTrace]
  refine ⟨101508324474278885020376381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67672216316185923346917587 101508324474278885020376381)
  ·
    refine ⟨38065621677854581882641143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101508324474278885020376381 38065621677854581882641143)
    ·
      refine ⟨57098432516781872823961715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38065621677854581882641143 57098432516781872823961715)
      ·
        refine ⟨85647648775172809235942573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57098432516781872823961715 85647648775172809235942573)
        ·
          refine ⟨32117868290689803463478465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85647648775172809235942573 32117868290689803463478465)
          ·
            refine ⟨24088401218017352597608849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32117868290689803463478465 24088401218017352597608849)
            ·
              refine ⟨18066300913513014448206637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24088401218017352597608849 18066300913513014448206637)
              ·
                refine ⟨6774862842567380418077489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18066300913513014448206637 6774862842567380418077489)
                ·
                  refine ⟨5081147131925535313558117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6774862842567380418077489 5081147131925535313558117)
                  ·
                    refine ⟨952715087236037871292147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081147131925535313558117 952715087236037871292147)
                    ·
                      rfl

theorem cell22_2783109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_2783109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783109 prefixEnd_2783109 := by exact prefixLift 2783109
  have htrace : WordTrace (prefixWord ++ tailWord_2783109) baseStart_2783109 baseEnd_2783109 := by
    simpa [prefixWord, tailWord_2783109, baseEnd_2783109] using wordTrace_append hprefix tailTrace_2783109
  have hstable : (prefixWord ++ tailWord_2783109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783109).length < 2 ^ (prefixWord ++ tailWord_2783109).sum := by decide
  have hdescent : baseEnd_2783109 < baseStart_2783109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2783124 : List Nat := [2, 4, 2, 1, 1, 2, 10]
def baseStart_2783124 : Nat := 118140960795 + 2783124 * 2 ^ 59
def prefixEnd_2783124 : Nat := 4983230072969 + 3 ^ 40 * 2783124 * 2
def baseEnd_2783124 : Nat := 35285934149725290080263

theorem tailTrace_2783124 : CollatzResearch.WordTrace tailWord_2783124 prefixEnd_2783124 35285934149725290080263 := by
  unfold tailWord_2783124
  simp only [CollatzResearch.WordTrace]
  refine ⟨50754435784612271291086213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67672581046149695054781617 50754435784612271291086213)
  ·
    refine ⟨9516456709614800867078665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50754435784612271291086213 9516456709614800867078665)
    ·
      refine ⟨7137342532211100650308999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9516456709614800867078665 7137342532211100650308999)
      ·
        refine ⟨10706013798316650975463499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7137342532211100650308999 10706013798316650975463499)
        ·
          refine ⟨16059020697474976463195249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10706013798316650975463499 16059020697474976463195249)
          ·
            refine ⟨12044265523106232347396437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16059020697474976463195249 12044265523106232347396437)
            ·
              refine ⟨35285934149725290080263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12044265523106232347396437 35285934149725290080263)
              ·
                rfl

theorem cell22_2783124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 10].length) (baseStart_2783124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2783124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2783124 prefixEnd_2783124 := by exact prefixLift 2783124
  have htrace : WordTrace (prefixWord ++ tailWord_2783124) baseStart_2783124 baseEnd_2783124 := by
    simpa [prefixWord, tailWord_2783124, baseEnd_2783124] using wordTrace_append hprefix tailTrace_2783124
  have hstable : (prefixWord ++ tailWord_2783124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2783124).length < 2 ^ (prefixWord ++ tailWord_2783124).sum := by decide
  have hdescent : baseEnd_2783124 < baseStart_2783124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2783124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
